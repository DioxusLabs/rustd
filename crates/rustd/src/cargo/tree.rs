//! A process of the daemon's with everything it started: what ends with it, what it used.

use std::{
    io,
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, ExitStatus},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering::Relaxed},
    },
    time::Duration,
};

use anyhow::Context as _;

use super::daemon::lock;
use crate::socket::private_file;

/// How much of what a process said is kept in memory.
const TAIL: usize = 1 << 16;

/// The file a process logs to. It writes to a pipe of the daemon's: a process whose log is on
/// a full disk goes on, and what it said last is known.
pub(super) struct Log {
    pub(super) path: PathBuf,
    tail: Arc<Mutex<Vec<u8>>>,
    drained: Arc<AtomicBool>,
}

impl Log {
    /// Has `command` log to the file at `path`, which starts out empty.
    pub(super) fn of(command: &mut Command, path: &Path) -> anyhow::Result<Log> {
        let mut file =
            private_file(std::fs::OpenOptions::new().write(true).create(true).truncate(true), path)
                .with_context(|| format!("opening {}", path.display()))?;
        let (mut reader, writer) = io::pipe().context("a pipe for a log")?;
        command.stdout(writer.try_clone()?).stderr(writer);
        let tail = Arc::new(Mutex::new(Vec::new()));
        let kept = tail.clone();
        let drained = Arc::new(AtomicBool::new(false));
        let done = drained.clone();
        std::thread::spawn(move || {
            use io::{Read as _, Write as _};
            let mut buffer = [0; 1 << 14];
            while let Ok(read @ 1..) = reader.read(&mut buffer) {
                let _ = file.write_all(&buffer[..read]);
                let mut tail = lock(&kept);
                tail.extend_from_slice(&buffer[..read]);
                if tail.len() > 2 * TAIL {
                    let cut = tail.len() - TAIL;
                    tail.drain(..cut);
                }
            }
            done.store(true, Relaxed);
        });
        Ok(Log { path: path.to_owned(), tail, drained })
    }

    /// The last line logged that says what went wrong.
    pub(super) fn last_words(&self) -> String {
        // What a process said as it ended may still be in the pipe.
        for _ in 0..100 {
            if self.drained.load(Relaxed) {
                break;
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        let tail = lock(&self.tail);
        let log = String::from_utf8_lossy(&tail);
        let lines: Vec<_> = log.lines().collect();
        match lines.iter().rposition(|it| it.starts_with("Error") || it.contains("panicked")) {
            Some(at) => lines[at..]
                .iter()
                .filter(|it| !it.trim().is_empty() && it.trim() != "Caused by:")
                .map(|it| it.trim())
                .collect::<Vec<_>>()
                .join(": "),
            None => lines.last().unwrap_or(&"no output").to_string(),
        }
    }
}

/// How a process ended.
#[derive(Clone)]
pub(super) struct Ended {
    /// None when the system would not say.
    pub(super) status: Option<ExitStatus>,
    /// In bytes.
    pub(super) peak_rss: Option<u64>,
}

/// A process and those it started, which end with it, also when it was killed.
pub(super) struct Tree {
    child: Child,
    ended: Option<Ended>,
    #[cfg(windows)]
    job: Option<std::os::windows::io::OwnedHandle>,
}

impl Tree {
    pub(super) fn spawn(command: &mut Command) -> io::Result<Tree> {
        #[cfg(unix)]
        std::os::unix::process::CommandExt::process_group(command, 0);
        let child = command.spawn()?;
        Ok(Tree {
            #[cfg(windows)]
            job: job::of(&child),
            child,
            ended: None,
        })
    }

    pub(super) fn id(&self) -> u32 {
        self.child.id()
    }

    pub(super) fn input(&mut self) -> Option<&mut ChildStdin> {
        self.child.stdin.as_mut()
    }

    /// How the process ended, once it has. What it left running is killed then.
    pub(super) fn ended(&mut self) -> Option<&Ended> {
        self.wait(false)
    }

    /// Kills the process and those it started, and waits for the process.
    pub(super) fn kill(&mut self) -> Ended {
        if self.ended.is_none() {
            self.kill_all();
        }
        self.wait(true).cloned().unwrap_or(Ended { status: None, peak_rss: None })
    }

    #[cfg(unix)]
    fn kill_all(&self) {
        // SAFETY: a signal to the group, which the process that leads it keeps reserved until
        // it is waited for. No memory of this process is involved.
        unsafe {
            libc::killpg(self.child.id() as libc::pid_t, libc::SIGKILL);
        }
    }

    #[cfg(windows)]
    fn kill_all(&mut self) {
        job::terminate(self.job.as_ref());
        let _ = self.child.kill();
    }

    /// The standard library's wait says nothing of what the process used, and this waits for
    /// `child` in its place: `child` is not asked or signalled after that. What the process
    /// left is killed before it is reaped: until then its id can't name someone else's group.
    #[cfg(unix)]
    fn wait(&mut self, block: bool) -> Option<&Ended> {
        use std::os::unix::process::ExitStatusExt as _;
        if self.ended.is_none() {
            let pid = self.child.id() as libc::pid_t;
            let flags = libc::WEXITED | libc::WNOWAIT | if block { 0 } else { libc::WNOHANG };
            // SAFETY: all zeros is a valid value of this structure of integers.
            let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
            let seen = retrying(|| {
                // SAFETY: the pointer is to a live value of the type asked for.
                unsafe { libc::waitid(libc::P_PID, pid as libc::id_t, &mut info, flags) }
            });
            if seen == 0 && info.si_signo == 0 {
                return None;
            }
            self.kill_all();
            let mut status = 0;
            // SAFETY: all zeros is a valid value of this structure of integers.
            let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
            let waited = retrying(|| {
                // SAFETY: both pointers are to live values of the types asked for.
                unsafe { libc::wait4(pid, &mut status, 0, &mut usage) }
            });
            // Kilobytes on Linux, bytes on macOS.
            let unit = if cfg!(target_vendor = "apple") { 1 } else { 1024 };
            self.ended = Some(if waited == pid {
                Ended {
                    status: Some(ExitStatus::from_raw(status)),
                    peak_rss: Some(usage.ru_maxrss as u64 * unit),
                }
            } else {
                Ended { status: None, peak_rss: None }
            });
        }
        self.ended.as_ref()
    }

    #[cfg(windows)]
    fn wait(&mut self, block: bool) -> Option<&Ended> {
        if self.ended.is_none() {
            let status =
                match if block { self.child.wait().map(Some) } else { self.child.try_wait() } {
                    Ok(None) => return None,
                    Ok(status) => status,
                    Err(_) => None,
                };
            self.kill_all();
            self.ended = Some(Ended { status, peak_rss: job::peak_memory(self.job.as_ref()) });
        }
        self.ended.as_ref()
    }

    #[cfg(not(any(unix, windows)))]
    fn kill_all(&mut self) {
        let _ = self.child.kill();
    }

    /// The CPU time used so far by the process and those it started, in a unit of its own:
    /// it changes when one of them runs. None where it can't be told.
    pub(super) fn cpu(&self) -> Option<u64> {
        #[cfg(windows)]
        return job::cpu(self.job.as_ref());
        #[cfg(not(windows))]
        cpu_of_group(self.child.id())
    }
}

#[cfg(unix)]
fn retrying(mut call: impl FnMut() -> libc::c_int) -> libc::c_int {
    loop {
        let result = call();
        if result != -1 || io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
            return result;
        }
    }
}

#[cfg(target_os = "linux")]
fn cpu_of_group(group: u32) -> Option<u64> {
    let mut total = None;
    for entry in std::fs::read_dir("/proc").ok()?.flatten() {
        if !entry.file_name().to_str().is_some_and(|it| it.parse::<u32>().is_ok()) {
            continue;
        }
        let Ok(stat) = std::fs::read_to_string(entry.path().join("stat")) else { continue };
        let Some((_, fields)) = stat.rsplit_once(')') else { continue };
        let fields: Vec<_> = fields.split_whitespace().collect();
        let parse = |at: usize| fields.get(at).and_then(|it| it.parse::<u64>().ok());
        if parse(2) == Some(group.into()) {
            // Its own time and that of the children it has waited for.
            let used = [11, 12, 13, 14].into_iter().filter_map(parse).sum::<u64>();
            total = Some(total.unwrap_or(0) + used);
        }
    }
    total
}

#[cfg(target_vendor = "apple")]
fn cpu_of_group(group: u32) -> Option<u64> {
    let mut pids = [0 as libc::pid_t; 1024];
    let size = std::mem::size_of_val(&pids) as libc::c_int;
    // SAFETY: the buffer has room for the size given.
    if unsafe { libc::proc_listpgrppids(group as _, pids.as_mut_ptr().cast(), size) } <= 0 {
        return None;
    }
    let mut total = None;
    // The buffer starts out zeroed, so its unused end needs no count.
    for &pid in pids.iter().filter(|it| **it != 0) {
        // SAFETY: all zeros is a valid value of this structure of integers.
        let mut info: libc::proc_taskinfo = unsafe { std::mem::zeroed() };
        let size = size_of::<libc::proc_taskinfo>() as libc::c_int;
        // SAFETY: the structure is the one the flavor fills, with the size given.
        let read = unsafe {
            libc::proc_pidinfo(pid, libc::PROC_PIDTASKINFO, 0, (&raw mut info).cast(), size)
        };
        if read == size {
            total = Some(total.unwrap_or(0) + info.pti_total_user + info.pti_total_system);
        }
    }
    total
}

#[cfg(not(any(target_os = "linux", target_vendor = "apple", windows)))]
fn cpu_of_group(_group: u32) -> Option<u64> {
    None
}

/// A Windows process has no group that outlives it: a job holds it and all it starts.
#[cfg(windows)]
mod job {
    use std::{
        ffi::c_void,
        os::windows::io::{AsRawHandle as _, FromRawHandle as _, OwnedHandle},
        process::Child,
    };

    use windows_sys::Win32::System::JobObjects::{
        AssignProcessToJobObject, CreateJobObjectW, JOBOBJECT_BASIC_ACCOUNTING_INFORMATION,
        JOBOBJECT_EXTENDED_LIMIT_INFORMATION, JobObjectBasicAccountingInformation,
        JobObjectExtendedLimitInformation, QueryInformationJobObject, TerminateJobObject,
    };

    pub(super) fn of(child: &Child) -> Option<OwnedHandle> {
        // SAFETY: no attributes and no name are valid arguments.
        let job = unsafe { CreateJobObjectW(std::ptr::null(), std::ptr::null()) };
        if job.is_null() {
            return None;
        }
        // SAFETY: the handle was just made and is owned from here on.
        let owned = unsafe { OwnedHandle::from_raw_handle(job) };
        // SAFETY: both handles are live.
        (unsafe { AssignProcessToJobObject(job, child.as_raw_handle()) } != 0).then_some(owned)
    }

    pub(super) fn terminate(job: Option<&OwnedHandle>) {
        if let Some(job) = job {
            // SAFETY: the handle is live.
            unsafe { TerminateJobObject(job.as_raw_handle(), 1) };
        }
    }

    fn query<T>(job: &OwnedHandle, class: i32) -> Option<T> {
        let mut info = std::mem::MaybeUninit::<T>::zeroed();
        // SAFETY: the structure is the one the class fills, with the size given.
        let read = unsafe {
            QueryInformationJobObject(
                job.as_raw_handle(),
                class,
                info.as_mut_ptr().cast::<c_void>(),
                size_of::<T>() as u32,
                std::ptr::null_mut(),
            )
        };
        // SAFETY: the system filled it, and all zeros is valid for these structures.
        (read != 0).then(|| unsafe { info.assume_init() })
    }

    pub(super) fn cpu(job: Option<&OwnedHandle>) -> Option<u64> {
        let info: JOBOBJECT_BASIC_ACCOUNTING_INFORMATION =
            query(job?, JobObjectBasicAccountingInformation)?;
        Some((info.TotalUserTime + info.TotalKernelTime) as u64)
    }

    pub(super) fn peak_memory(job: Option<&OwnedHandle>) -> Option<u64> {
        let info: JOBOBJECT_EXTENDED_LIMIT_INFORMATION =
            query(job?, JobObjectExtendedLimitInformation)?;
        Some(info.PeakProcessMemoryUsed as u64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shell(script: &str) -> Command {
        #[cfg(windows)]
        let mut command = {
            let mut command = Command::new("cmd");
            command.args(["/c", script]);
            command
        };
        #[cfg(not(windows))]
        let mut command = {
            let mut command = Command::new("sh");
            command.args(["-c", script]);
            command
        };
        command.stdin(std::process::Stdio::piped());
        command
    }

    #[test]
    fn says_how_it_ended_and_what_it_used() {
        let mut tree = Tree::spawn(&mut shell("exit 3")).unwrap();
        let ended = tree.kill();
        // Killed first or exited first, it has ended and is not waited for twice.
        assert!(ended.status.is_some());
        assert!(tree.ended().is_some());
        tree.kill();
        #[cfg(unix)]
        {
            let mut tree = Tree::spawn(&mut shell("exit 3")).unwrap();
            while tree.ended().is_none() {
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            let ended = tree.ended().unwrap();
            assert_eq!(ended.status.unwrap().code(), Some(3));
            assert!(ended.peak_rss.is_some_and(|it| it > 1 << 16));
        }
    }

    #[cfg(any(target_os = "linux", target_vendor = "apple", windows))]
    #[test]
    fn cpu_counts_what_it_started() {
        #[cfg(windows)]
        let script = "for /L %i in (1,1,2000000) do @rem";
        #[cfg(not(windows))]
        let script = "i=0; while [ $i -lt 3000000 ]; do i=$((i+1)); done & wait";
        let mut tree = Tree::spawn(&mut shell(script)).unwrap();
        let first = tree.cpu();
        let moved = (0..500).any(|_| {
            std::thread::sleep(std::time::Duration::from_millis(10));
            tree.cpu().is_some_and(|it| Some(it) != first)
        });
        tree.kill();
        assert!(moved);
    }

    #[cfg(unix)]
    #[test]
    fn what_it_started_ends_with_it_also_when_it_was_killed() {
        let dir = tempfile_dir();
        let pids = dir.join("pids");
        let script = format!("sleep 60 & echo $! > {}; wait", pids.display());
        let mut tree = Tree::spawn(&mut shell(&script)).unwrap();
        while !std::fs::read_to_string(&pids).is_ok_and(|it| it.ends_with('\n')) {
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        let left: i32 = std::fs::read_to_string(&pids).unwrap().trim().parse().unwrap();
        // SAFETY: a signal to a child of this test. No memory is involved.
        unsafe { libc::kill(tree.id() as i32, libc::SIGKILL) };
        while tree.ended().is_none() {
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        // SAFETY: as above, and signal 0 only asks whether it is there.
        let there = || unsafe { libc::kill(left, 0) } == 0;
        for _ in 0..200 {
            if !there() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(!there());
    }

    #[cfg(unix)]
    fn tempfile_dir() -> PathBuf {
        let dir = std::env::temp_dir().join(format!("rustd-tree-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn a_log_keeps_its_last_words_without_its_file() {
        let dir = std::env::temp_dir().join(format!("rustd-log-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut command = shell("echo one && echo Error: two");
        let log = Log::of(&mut command, &dir.join("log")).unwrap();
        let mut tree = Tree::spawn(&mut command).unwrap();
        drop(command);
        for _ in 0..500 {
            if log.last_words().contains("two") {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        tree.kill();
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(log.last_words().starts_with("Error: two"), "{}", log.last_words());
    }
}
