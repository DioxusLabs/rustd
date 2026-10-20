//! The cargo that runs the wrapper. Cargo tells the rustc it runs nothing of its own command
//! line, and which build a unit is of is read from it: the command, its flags, the directory
//! it runs in and its environment.

use std::{ffi::OsString, path::PathBuf};

/// A cargo that is running, as the system describes it.
pub(crate) struct Cargo {
    pub(crate) executable: PathBuf,
    /// Its arguments, without its own name.
    pub(crate) args: Vec<String>,
    #[cfg_attr(not(test), expect(dead_code, reason = "only the tests read it"))]
    pub(crate) cwd: PathBuf,
    #[cfg_attr(not(test), expect(dead_code, reason = "only the tests read it"))]
    pub(crate) env: Vec<(OsString, OsString)>,
}

/// How many processes up from the wrapper cargo is looked for: there are the wrappers the
/// user chains between the two, and nothing else.
const FARTHEST: usize = 8;

impl Cargo {
    /// The nearest process above this one that is cargo. `Err` is why none is known.
    pub(crate) fn above() -> Result<Cargo, String> {
        let mut pid = std::process::id();
        for _ in 0..FARTHEST {
            pid = system::parent(pid).ok_or("the process that runs rustc is not cargo")?;
            if let Some(cargo) = system::described(pid).filter(Cargo::is_cargo) {
                return Ok(cargo);
            }
        }
        Err("the process that runs rustc is not cargo".to_owned())
    }

    fn is_cargo(&self) -> bool {
        self.executable.file_stem().is_some_and(|it| it == "cargo")
    }
}

#[cfg(target_os = "linux")]
mod system {
    use std::{
        ffi::OsString,
        os::unix::ffi::OsStringExt as _,
        path::{Path, PathBuf},
    };

    use super::Cargo;

    fn of(pid: u32, file: &str) -> PathBuf {
        Path::new("/proc").join(pid.to_string()).join(file)
    }

    /// The process that started `pid`, when `pid` runs.
    pub(super) fn parent(pid: u32) -> Option<u32> {
        let stat = std::fs::read_to_string(of(pid, "stat")).ok()?;
        // `pid (name) state ppid ...`, and the name may have spaces and brackets of its own.
        let after_name = &stat[stat.rfind(')')? + 1..];
        let mut fields = after_name.split_whitespace();
        let state = fields.next()?;
        let parent = fields.next()?.parse().ok()?;
        // A process that ended and is not reaped yet.
        (state != "Z").then_some(parent)
    }

    fn words(pid: u32, file: &str) -> Option<Vec<OsString>> {
        let bytes = std::fs::read(of(pid, file)).ok()?;
        let words = bytes.split(|it| *it == 0).filter(|it| !it.is_empty());
        Some(words.map(|it| OsString::from_vec(it.to_vec())).collect())
    }

    pub(super) fn described(pid: u32) -> Option<Cargo> {
        let args = words(pid, "cmdline")?.into_iter().skip(1);
        let env = words(pid, "environ")?.into_iter().filter_map(|it| {
            let bytes = it.into_vec();
            let at = bytes.iter().position(|it| *it == b'=')?;
            let (name, value) = (bytes[..at].to_vec(), bytes[at + 1..].to_vec());
            Some((OsString::from_vec(name), OsString::from_vec(value)))
        });
        Some(Cargo {
            executable: std::fs::read_link(of(pid, "exe")).ok()?,
            args: args.map(|it| it.into_string().ok()).collect::<Option<_>>()?,
            cwd: std::fs::read_link(of(pid, "cwd")).ok()?,
            env: env.collect(),
        })
    }
}

/// macOS has no `/proc`: the kernel is asked through `libproc` and `sysctl`.
#[cfg(target_os = "macos")]
mod system {
    use std::{
        ffi::{OsString, c_int, c_void},
        mem::{MaybeUninit, size_of},
        os::unix::ffi::OsStringExt as _,
        path::PathBuf,
    };

    use super::Cargo;

    /// What `flavor` of `proc_pidinfo` says of `pid`, when it says all of a `T`.
    fn info<T>(pid: u32, flavor: c_int) -> Option<T> {
        let mut info = MaybeUninit::<T>::zeroed();
        let size = size_of::<T>() as c_int;
        // SAFETY: the kernel writes at most `size` bytes to `info`, which has that many.
        let wrote =
            unsafe { libc::proc_pidinfo(pid as c_int, flavor, 0, info.as_mut_ptr().cast(), size) };
        // SAFETY: every field of these structures is an integer or an array of them, which
        // the zeroes and what the kernel wrote are values of.
        (wrote == size).then(|| unsafe { info.assume_init() })
    }

    fn path(bytes: &[libc::c_char]) -> PathBuf {
        let bytes = bytes.iter().take_while(|it| **it != 0).map(|it| *it as u8);
        PathBuf::from(OsString::from_vec(bytes.collect()))
    }

    /// The process that started `pid`, when `pid` runs.
    pub(super) fn parent(pid: u32) -> Option<u32> {
        let info: libc::proc_bsdinfo = info(pid, libc::PROC_PIDTBSDINFO)?;
        // A process that ended and is not reaped yet.
        (info.pbi_status != libc::SZOMB).then_some(info.pbi_ppid)
    }

    fn executable(pid: u32) -> Option<PathBuf> {
        let mut name = [0 as libc::c_char; libc::PROC_PIDPATHINFO_MAXSIZE as usize];
        // SAFETY: the kernel writes at most the length of `name` to it.
        let length = unsafe {
            libc::proc_pidpath(pid as c_int, name.as_mut_ptr().cast::<c_void>(), name.len() as u32)
        };
        (length > 0).then(|| path(&name))
    }

    /// The arguments of `pid` with its own name, and its environment: `KERN_PROCARGS2` is
    /// the count of the arguments, the path of the executable, zeroes, and then each
    /// argument and each variable with a zero after it.
    fn words(pid: u32) -> Option<(Vec<OsString>, Vec<OsString>)> {
        let mut name = [libc::CTL_KERN, libc::KERN_ARGMAX];
        let mut most: c_int = 0;
        let mut size = size_of::<c_int>();
        // SAFETY: `most` has the `size` bytes the kernel is told it may write.
        let failed = unsafe {
            let most = (&raw mut most).cast::<c_void>();
            libc::sysctl(name.as_mut_ptr(), 2, most, &mut size, std::ptr::null_mut(), 0)
        };
        if failed != 0 {
            return None;
        }
        let mut bytes = vec![0u8; usize::try_from(most).ok()?];
        let mut size = bytes.len();
        let mut name = [libc::CTL_KERN, libc::KERN_PROCARGS2, pid as c_int];
        // SAFETY: `bytes` has the `size` bytes the kernel is told it may write.
        let failed = unsafe {
            let bytes = bytes.as_mut_ptr().cast::<c_void>();
            libc::sysctl(name.as_mut_ptr(), 3, bytes, &mut size, std::ptr::null_mut(), 0)
        };
        if failed != 0 {
            return None;
        }
        let (count, rest) = bytes.get(..size)?.split_first_chunk::<4>()?;
        let count = usize::try_from(c_int::from_ne_bytes(*count)).ok()?;
        let executable = rest.iter().position(|it| *it == 0)?;
        let rest = &rest[executable..];
        let rest = &rest[rest.iter().position(|it| *it != 0)?..];
        let mut words = rest.split(|it| *it == 0).map(|it| OsString::from_vec(it.to_vec()));
        let args: Vec<OsString> = words.by_ref().take(count).collect();
        let env = words.take_while(|it| !it.is_empty()).collect();
        (args.len() == count).then_some((args, env))
    }

    pub(super) fn described(pid: u32) -> Option<Cargo> {
        let (args, env) = words(pid)?;
        let env = env.into_iter().filter_map(|it| {
            let bytes = it.into_vec();
            let at = bytes.iter().position(|it| *it == b'=')?;
            let (name, value) = (bytes[..at].to_vec(), bytes[at + 1..].to_vec());
            Some((OsString::from_vec(name), OsString::from_vec(value)))
        });
        let dirs: libc::proc_vnodepathinfo = info(pid, libc::PROC_PIDVNODEPATHINFO)?;
        Some(Cargo {
            executable: executable(pid)?,
            args: args
                .into_iter()
                .skip(1)
                .map(|it| it.into_string().ok())
                .collect::<Option<_>>()?,
            cwd: path(dirs.pvi_cdir.vip_path.as_flattened()),
            env: env.collect(),
        })
    }
}

/// Elsewhere the command line of another process is not read yet, and plain cargo fails
/// at the first crate of a workspace.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
mod system {
    use super::Cargo;

    pub(super) fn parent(_pid: u32) -> Option<u32> {
        None
    }

    pub(super) fn described(_pid: u32) -> Option<Cargo> {
        None
    }
}

#[cfg(all(test, target_os = "macos"))]
mod tests {
    use super::system;

    #[test]
    fn a_process_is_described_as_it_was_started() {
        let pid = std::process::id();
        let this = system::described(pid).unwrap();
        assert_eq!(this.args, std::env::args().skip(1).collect::<Vec<_>>());
        assert_eq!(this.cwd, std::env::current_dir().unwrap().canonicalize().unwrap());
        assert_eq!(this.executable, std::env::current_exe().unwrap().canonicalize().unwrap());
        let path = this.env.iter().find(|(name, _)| name == "PATH").map(|(_, value)| value);
        assert_eq!(path, std::env::var_os("PATH").as_ref());
        assert!(system::parent(pid).is_some_and(|it| it != pid));
    }
}
