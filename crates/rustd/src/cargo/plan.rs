//! What the daemon is asked to build a program from: the crates of the workspace that are in
//! it, the files rustc built to read symbols from, and rustc's link line with the daemon's
//! objects ahead of rustc's.

use std::path::{Path, PathBuf};

use anyhow::Context as _;
use rustc_hash::FxHashSet;
use serde::{Deserialize, Serialize};

use super::{package, units::Record};
use crate::weaken;

/// What an ELF linker is told so that the first definition of a name is the one that stays.
const FIRST_DEFINITION_STAYS: &str = "-Wl,--allow-multiple-definition";

/// What Apple's linker is told so that a splice has room in the header for its two segments.
const ROOM_FOR_SEGMENTS: &str = "-Wl,-headerpad,0x200";

/// And for the tables of the unwinder to grow into, where the loader looks for them.
const ROOM_FOR_TABLES: &str = "-Wl,-sectcreate,__TEXT,__rustd_room,";
const ROOM_FOR_TABLES_LEN: usize = 0x10000;

/// The same for `link.exe`, which warns of every name it does so for unless told not to.
const FIRST_DEFINITION_STAYS_MSVC: [&str; 2] = ["/FORCE:MULTIPLE", "/IGNORE:4006"];

/// What a build script says to have `link.exe` fail on a warning. It warns of every image
/// it writes with `/FORCE` and can't be told not to, so the daemon's link leaves this out.
const WARNINGS_FAIL: &str = "/WX";

/// How `link.exe` is told where to write.
const OUT: &str = "/OUT:";

/// The stack of the first thread, when the line asks for none. `link.exe` gives it 1 MiB,
/// an eighth of what it has elsewhere, and a function compiled here can have a frame twice
/// that of rustc's: one of clap's that rustc gives 480 KiB overflows it at once.
const STACK: &str = "/STACK:";
const STACK_OF_MAIN: &str = "/STACK:8388608";

/// rustc has the executable name its symbols by file name alone, which finds them next
/// to it. The daemon's are not next to where the executable is installed.
const SYMBOLS_BY_NAME: &str = "/PDBALTPATH:%_PDB%";

/// The crates of the standard library whose symbols the daemon reads.
const LIBRARY: [&str; 3] = ["core", "alloc", "std"];

/// A program as the daemon builds it.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub(crate) struct Plan {
    /// The root files of the crates of the workspace that rustd compiles, the program's own
    /// first.
    pub(crate) crates: Vec<PathBuf>,
    /// The object with all of rustd's code for the program.
    pub(crate) object: PathBuf,
    /// The object with what an edit changed.
    pub(crate) patch: PathBuf,
    /// The executable the daemon links and splices.
    pub(crate) binary: PathBuf,
    /// The command that links `binary`, for a shell.
    pub(crate) link_cmd: String,
    pub(crate) symbol_files: Vec<PathBuf>,
    /// The copies of rustc's output the plan names, which have to stay.
    pub(crate) copies: Vec<PathBuf>,
    /// The package rustc wrote of what a debugger reads of the program it linked, when the
    /// profile keeps that in one (`split-debuginfo = "packed"`).
    #[serde(default)]
    pub(crate) package: Option<PathBuf>,
    /// The newest record the plan was made from.
    pub(crate) stamp: u128,
}

/// The harness of a test executable, which the daemon writes from the tests it finds and
/// rustc compiles. It is glue alone: each test it has calls the daemon's code of that test.
/// It is kept beside the object of the program, where the daemon looks for it.
#[derive(Serialize, Deserialize)]
pub(crate) struct Harness {
    rustc: PathBuf,
    cwd: PathBuf,
    args: Vec<String>,
    source: PathBuf,
    object: PathBuf,
}

/// The codegen flags of the test executable that the harness is compiled with too.
const OF_HARNESS: [&str; 8] = [
    "opt-level",
    "debuginfo",
    "panic",
    "overflow-checks",
    "debug-assertions",
    "target-cpu",
    "target-feature",
    "relocation-model",
];

impl Harness {
    fn beside(object: &Path) -> PathBuf {
        object.with_file_name("harness.json")
    }

    /// The harness of the program whose object is `object`, when it is a test executable.
    pub(crate) fn of(object: &Path) -> anyhow::Result<Option<Harness>> {
        let path = Harness::beside(object);
        if !path.exists() {
            return Ok(None);
        }
        let text = std::fs::read_to_string(&path)?;
        Ok(Some(serde_json::from_str(&text).with_context(|| format!("{}", path.display()))?))
    }

    /// Plans the harness of the test executable rustc was asked for by `unit`, with its
    /// files in `dir`: libtest's when `test`, and otherwise a program's own `main`.
    fn plan(unit: &Record, dir: &Path, test: bool) -> Harness {
        let mut args = vec!["--cap-lints=allow".to_owned()];
        if test {
            args.push("--test".to_owned());
        }
        let mut given = unit.args.iter();
        while let Some(arg) = given.next() {
            match arg.as_str() {
                "--crate-name" | "--edition" | "--target" | "--sysroot" => {
                    args.push(arg.clone());
                    args.extend(given.next().cloned());
                }
                "-C" => {
                    let Some(value) = given.next() else { break };
                    let name = value.split_once('=').map_or(&**value, |it| it.0);
                    if OF_HARNESS.contains(&name) {
                        args.extend(["-C".to_owned(), value.clone()]);
                    }
                }
                _ if arg.starts_with("--edition=") || arg.starts_with("--target=") => {
                    args.push(arg.clone())
                }
                _ => {}
            }
        }
        let (source, object) = (dir.join("harness.rs"), dir.join("harness.o"));
        args.extend(["--emit=obj", "-Ccodegen-units=1", "-o"].map(str::to_owned));
        args.push(object.display().to_string());
        let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()).into();
        Harness { rustc, cwd: unit.cwd.clone(), args, source, object }
    }

    /// Has the harness be `text`. `true` when it was another.
    pub(crate) fn write(&self, text: &str) -> anyhow::Result<bool> {
        if self.object.exists() && std::fs::read_to_string(&self.source).is_ok_and(|it| it == text)
        {
            return Ok(false);
        }
        std::fs::write(&self.source, text)?;
        let compiled = std::process::Command::new(&self.rustc)
            .current_dir(&self.cwd)
            .args(&self.args)
            .arg(&self.source)
            .stdin(std::process::Stdio::null())
            .output()
            .with_context(|| format!("running {}", self.rustc.display()))?;
        anyhow::ensure!(
            compiled.status.success(),
            "the harness of the tests does not build: {}",
            String::from_utf8_lossy(&compiled.stderr).trim_end()
        );
        Ok(true)
    }
}

/// The library of the workspace among `records` that wrote the file a link line names. The
/// file is told by what it is and not by its name: a target directory reached through a
/// link has two names for it.
fn member_that_wrote<'a>(records: &'a [Record], file: &Path) -> Option<&'a Record> {
    if file.extension().is_none_or(|it| it != "rlib") {
        return None;
    }
    let is_file = |it: &PathBuf| it == file || same_file::is_same_file(it, file).unwrap_or(false);
    records.iter().find(|it| it.is_rlib() && it.outputs().iter().any(is_file))
}

impl Plan {
    /// Plans the program `unit` built, with the daemon's files for it in `dir`. `records` are
    /// the units of the workspace. With `examples`, the root of the crate of the examples of
    /// the library `unit` tests, the program is the examples', linked as the unit tests are.
    /// `Err` is why the program is left to cargo.
    pub(crate) fn of(
        unit: &Record,
        records: &[Record],
        dir: &Path,
        examples: Option<&Path>,
    ) -> anyhow::Result<Result<Plan, String>> {
        if let Some(why) = unsupported(unit) {
            return Ok(Err(why));
        }
        let line = unit.link_line.as_ref().context("a linked unit without a link line")?;
        let line =
            std::fs::read_to_string(line).with_context(|| format!("reading {}", line.display()))?;
        let Some(mut link) = LinkLine::parse(&line) else {
            let why = "the link line is not one of a linker driven by `cc` or of `link.exe`";
            return Ok(Err(why.to_owned()));
        };
        let mut plan = Plan {
            crates: vec![unit.source.clone()],
            object: dir.join("rustd.o"),
            patch: dir.join("patch.o"),
            binary: dir.join("bin"),
            link_cmd: String::new(),
            symbol_files: Vec::new(),
            copies: Vec::new(),
            package: (unit.codegen("split-debuginfo") == Some("packed"))
                .then(|| link.output().map(|it| package::beside(Path::new(it))))
                .flatten(),
            stamp: unit.stamp,
        };
        for arg in &mut link.args {
            let path = PathBuf::from(&*arg);
            let member = member_that_wrote(records, &path);
            let Some(owner) = member.or_else(|| unit.copy_of(&path).map(|_| unit)) else {
                continue;
            };
            if let Some(why) = unsupported(owner) {
                return Ok(Err(why));
            }
            let Some(copy) = owner.copy_of(&path) else {
                return Ok(Err(format!("no copy of {} was kept", path.display())));
            };
            plan.copies.push(copy.to_owned());
            plan.stamp = plan.stamp.max(owner.stamp);
            *arg = copy.display().to_string();
            if member.is_some() {
                plan.crates.push(owner.source.clone());
            }
        }
        // The library the examples are of is linked as built, and its tests may link it too.
        if let Some(examples) = examples {
            plan.crates.insert(0, examples.to_owned());
            let mut seen = FxHashSet::default();
            plan.crates.retain(|it| seen.insert(it.clone()));
        }
        plan.symbol_files = link.rustc_files();
        std::fs::create_dir_all(dir)?;
        link.give_way(&plan.copies)?;
        let mut ahead = vec![&*plan.patch, &*plan.object];
        // The tests of an integration test are the daemon's, and so is the harness that runs
        // them: its `main` comes ahead of the one rustc wrote for none.
        let harness = unit.is_test().then(|| Harness::plan(unit, dir, examples.is_none()));
        let beside = Harness::beside(&plan.object);
        match &harness {
            Some(harness) => std::fs::write(&beside, serde_json::to_string(harness)?)?,
            None => _ = std::fs::remove_file(&beside),
        }
        ahead.extend(harness.as_ref().map(|it| &*it.object));
        plan.link_cmd = link.command(&ahead, &plan.binary, &dir.join("link.args"))?;
        Ok(Ok(plan))
    }
}

/// Why rustd has no part in a crate that was compiled with these flags, when it has none.
/// What a profile sets (the level, the checks, the panic strategy) the daemon reads from
/// cargo itself, and refuses there what it does not build.
fn unsupported(unit: &Record) -> Option<String> {
    let name = &unit.crate_name;
    let off = |value: Option<&str>| matches!(value, None | Some("off" | "no" | "n" | "false"));
    if !off(unit.codegen("lto")) || unit.codegen("linker-plugin-lto").is_some() {
        return Some(format!("`{name}` is built with LTO"));
    }
    for flag in ["instrument-coverage", "profile-generate", "profile-use"] {
        if unit.codegen(flag).is_some() {
            return Some(format!("`{name}` is built with -C {flag}"));
        }
    }
    if unit.args.iter().any(|it| it.starts_with("-Z")) {
        return Some(format!("`{name}` is built with unstable flags"));
    }
    None
}

/// The line rustc ran the linker with: the variables it set, the driver, the arguments.
pub(crate) struct LinkLine {
    /// What the line starts with to run the driver without some variables: `env -u NAME`.
    without: Vec<String>,
    env: Vec<(String, String)>,
    linker: String,
    args: Vec<String>,
    flavor: Flavor,
}

/// The kinds of linker the daemon can put its objects ahead of rustc's for.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Flavor {
    /// An ELF linker driven by `cc`.
    Cc,
    /// Apple's linker driven by `cc`, which tells it its architecture.
    Apple,
    /// `link.exe`, or one that takes its arguments.
    Msvc,
}

impl Flavor {
    fn of(args: &[String]) -> Option<Flavor> {
        if args.iter().any(|it| it == "/NOLOGO") {
            return args.iter().any(|it| it.starts_with(OUT)).then_some(Flavor::Msvc);
        }
        let of_cc = args.iter().any(|it| it == "-o") && !args.iter().any(|it| it == "-flavor");
        let flavor = match args.iter().any(|it| it == "-arch") {
            true => Flavor::Apple,
            false => Flavor::Cc,
        };
        of_cc.then_some(flavor)
    }
}

impl LinkLine {
    /// `None` for a line that is of no linker the daemon knows.
    pub(crate) fn parse(line: &str) -> Option<LinkLine> {
        let words = shlex::split(line.lines().find(|it| it.contains('"'))?)?;
        let unsets = match words.first().map(String::as_str) {
            Some("env") => words[1..].chunks(2).take_while(|it| it[0] == "-u").count(),
            _ => 0,
        };
        let (without, words) = words.split_at(if unsets == 0 { 0 } else { 1 + 2 * unsets });
        let first = words.iter().position(|it| !is_assignment(it))?;
        let env = words[..first]
            .iter()
            .filter_map(|it| it.split_once('='))
            .map(|(name, value)| (name.to_owned(), value.to_owned()))
            .collect();
        let args: Vec<String> = words[first + 1..]
            .iter()
            // The record keeps a copy of it, and the plan names that; one gone with rustc's
            // directory and not kept, as an older record has it, can't be linked.
            .filter(|it| !it.ends_with("symbols.o") || Path::new(it).exists())
            .cloned()
            .collect();
        let flavor = Flavor::of(&args)?;
        let (without, linker) = (without.to_vec(), words[first].clone());
        Some(LinkLine { without, env, linker, args, flavor })
    }

    /// Has what rustc built of the workspace give way to the daemon's by being weak, where
    /// the linker has no flag for the first definition staying: Apple's.
    fn give_way(&mut self, copies: &[PathBuf]) -> anyhow::Result<()> {
        if self.flavor != Flavor::Apple {
            return Ok(());
        }
        for arg in &mut self.args {
            if copies.iter().any(|it| it == Path::new(arg)) {
                *arg = weaken::copy_of(Path::new(arg))?.display().to_string();
            }
        }
        Ok(())
    }

    /// The executable the line links.
    fn output(&self) -> Option<&str> {
        let at = self.args.iter().position(|it| it == "-o")?;
        self.args.get(at + 1).map(|it| &**it)
    }

    /// What rustc built that is linked, and the standard library's crates next to it.
    pub(crate) fn rustc_files(&self) -> Vec<PathBuf> {
        let mut files: Vec<PathBuf> =
            self.args.iter().filter(|it| is_rustc_file(it)).map(PathBuf::from).collect();
        let library = files.iter().find_map(|it| {
            it.components().any(|it| it.as_os_str() == "rustlib").then(|| it.parent())?
        });
        let entries = library.and_then(|it| std::fs::read_dir(it).ok()).into_iter().flatten();
        for path in entries.flatten().map(|it| it.path()) {
            let name = path.file_name().and_then(|it| it.to_str()).unwrap_or_default();
            let of_library = LIBRARY.iter().any(|it| {
                name.strip_prefix("lib")
                    .and_then(|rest| rest.strip_prefix(it))
                    .is_some_and(|rest| rest.starts_with('-'))
            });
            if of_library && name.ends_with(".rlib") && !files.contains(&path) {
                files.push(path);
            }
        }
        files
    }

    /// The command that links `binary` with the objects `ahead` before everything rustc
    /// built, with its arguments in the file at `response`: a line with all of them is longer
    /// than a process may be given.
    pub(crate) fn command(
        mut self,
        ahead: &[&Path],
        binary: &Path,
        response: &Path,
    ) -> anyhow::Result<String> {
        if self.flavor == Flavor::Msvc {
            self.args.retain(|it| !it.eq_ignore_ascii_case(WARNINGS_FAIL));
        }
        let first = self
            .args
            .iter()
            .position(|it| is_rustc_file(it))
            .context("nothing of rustc's is linked")?;
        let ours = ahead.iter().map(|it| it.display().to_string()).collect();
        match self.flavor {
            Flavor::Cc | Flavor::Apple => self.command_of_cc(ours, first, binary, response),
            Flavor::Msvc => self.command_of_msvc(ours, first, binary, response),
        }
    }

    fn command_of_cc(
        mut self,
        ours: Vec<String>,
        first: usize,
        binary: &Path,
        response: &Path,
    ) -> anyhow::Result<String> {
        let flags = match self.flavor {
            Flavor::Apple => {
                let room = response.with_file_name("rustd.room");
                std::fs::write(&room, vec![0; ROOM_FOR_TABLES_LEN])?;
                vec![ROOM_FOR_SEGMENTS.to_owned(), format!("{ROOM_FOR_TABLES}{}", room.display())]
            }
            _ => vec![FIRST_DEFINITION_STAYS.to_owned()],
        };
        self.args.splice(first..first, ours.into_iter().chain(flags));
        let output =
            self.args.iter().position(|it| it == "-o").context("the link names no output")?;
        *self.args.get_mut(output + 1).context("the link names no output")? =
            linking(binary).display().to_string();
        let quoted: Vec<String> = self
            .args
            .iter()
            .map(|it| shlex::try_quote(it).map(|it| it.into_owned()))
            .collect::<Result<_, _>>()
            .context("an argument of the link can't be quoted")?;
        std::fs::write(response, quoted.join("\n"))?;
        let mut command = self.without;
        for (name, value) in &self.env {
            command.push(format!("{name}={}", shlex::try_quote(value)?));
        }
        command.push(shlex::try_quote(&self.linker)?.into_owned());
        command.push(shlex::try_quote(&format!("@{}", response.display()))?.into_owned());
        Ok(command.join(" "))
    }

    /// rustc tells `link.exe` where the libraries of the system are through `LIB`, which
    /// is not in the line; here the line says it.
    fn command_of_msvc(
        mut self,
        ours: Vec<String>,
        first: usize,
        binary: &Path,
        response: &Path,
    ) -> anyhow::Result<String> {
        let stays = FIRST_DEFINITION_STAYS_MSVC.map(str::to_owned);
        self.args.splice(first..first, ours.into_iter().chain(stays));
        let binary = binary.display();
        for arg in &mut self.args {
            if arg.starts_with(OUT) {
                *arg = format!("{OUT}{binary}");
            } else if arg == SYMBOLS_BY_NAME {
                *arg = format!("/PDBALTPATH:{binary}.pdb");
            }
        }
        if !self.args.iter().any(|it| it.starts_with(STACK)) {
            self.args.push(STACK_OF_MAIN.to_owned());
        }
        self.args.extend(system_libraries().iter().map(|it| format!("/LIBPATH:{}", it.display())));
        if self.args.iter().any(|it| it.contains('"')) {
            anyhow::bail!("an argument of the link can't be quoted");
        }
        // A backslash before the quote that closes an argument would make it part of it.
        let quoted = |arg: &String| {
            let closing = arg.len() - arg.trim_end_matches('\\').len();
            format!("\"{arg}{}\"", "\\".repeat(closing))
        };
        let quoted: Vec<String> = self.args.iter().map(quoted).collect();
        std::fs::write(response, quoted.join("\n"))?;
        Ok(format!("\"{}\" \"@{}\"", self.linker, response.display()))
    }
}

/// Where the linker writes the executable at `binary`, which takes its place once it is
/// whole: the linker writes its output in place, and a client that runs, or links to, the
/// executable while another build links it would have half a file, not yet executable.
pub(crate) fn linking(binary: &Path) -> PathBuf {
    let mut linking = binary.as_os_str().to_owned();
    linking.push(".linking");
    PathBuf::from(linking)
}

/// The directories `link.exe` finds the libraries of the compiler and of the system in.
#[cfg(windows)]
fn system_libraries() -> Vec<PathBuf> {
    let Some(linker) = find_msvc_tools::find_tool(std::env::consts::ARCH, "link.exe") else {
        return Vec::new();
    };
    let listed = linker.env().into_iter().find(|(name, _)| name == "LIB");
    let Some((_, dirs)) = listed else { return Vec::new() };
    // A list that ends in its separator has an empty last entry.
    std::env::split_paths(dirs).filter(|it| !it.as_os_str().is_empty()).collect()
}

#[cfg(not(windows))]
fn system_libraries() -> Vec<PathBuf> {
    Vec::new()
}

/// Whether a word of the link line sets a variable for the linker's driver.
fn is_assignment(word: &str) -> bool {
    word.split_once('=').is_some_and(|(name, _)| {
        !name.is_empty() && name.bytes().all(|it| it.is_ascii_alphanumeric() || it == b'_')
    })
}

fn is_rustc_file(arg: &str) -> bool {
    arg.ends_with(".rlib") || arg.ends_with(".rcgu.o")
}

#[cfg(test)]
mod tests {
    use super::*;

    const LINE: &str = r#"LC_ALL="C" PATH="/t/bin:/usr/bin" "cc" "-m64" "/t/deps/rustc1/symbols.o" "/t/deps/a.1.rcgu.o" "-Wl,-Bstatic" "/t/deps/libb-2.rlib" "-o" "/t/deps/a-1" "-pie""#;

    #[test]
    fn link_line_of_cc() {
        let link = LinkLine::parse(LINE).unwrap();
        assert_eq!(
            link.env,
            [
                ("LC_ALL".to_owned(), "C".to_owned()),
                ("PATH".to_owned(), "/t/bin:/usr/bin".to_owned())
            ]
        );
        assert_eq!(link.linker, "cc");
        assert_eq!(link.args[..2], ["-m64", "/t/deps/a.1.rcgu.o"]);
        assert_eq!(
            link.rustc_files(),
            ["/t/deps/a.1.rcgu.o", "/t/deps/libb-2.rlib"].map(PathBuf::from)
        );
    }

    fn unit(args: &[&str]) -> Record {
        Record {
            id: "a-1".to_owned(),
            crate_name: "a".to_owned(),
            cwd: PathBuf::from("/ws"),
            args: args.iter().map(|it| it.to_string()).collect(),
            source: PathBuf::from("/ws/src/lib.rs"),
            stamp: 1,
            copies: Vec::new(),
            link_line: None,
            env: Default::default(),
        }
    }

    #[test]
    fn tests_are_built_whatever_rustc_would_have_inlined() {
        assert_eq!(unsupported(&unit(&["--test"])), None);
        assert_eq!(unsupported(&unit(&["-C", "opt-level=3"])), None);
    }

    #[test]
    fn link_lines_that_are_not_cc_for_elf() {
        assert!(LinkLine::parse("").is_none());
        assert!(LinkLine::parse("no quotes here").is_none());
        assert!(LinkLine::parse(r#""link.exe" "/NOLOGO" "-o""#).is_none());
        assert!(LinkLine::parse(r#""rust-lld" "-flavor" "wasm" "-o" "a.wasm""#).is_none());
        assert!(LinkLine::parse(r#"A="1" "cc" "unterminated"#).is_none());
    }

    #[test]
    fn link_line_of_cc_for_mach_o() {
        let line = r#"env -u IPHONEOS_DEPLOYMENT_TARGET -u TVOS_DEPLOYMENT_TARGET LC_ALL="C" "cc" "/t/deps/a.1.rcgu.o" "-arch" "arm64" "-o" "/t/deps/a-1""#;
        let link = LinkLine::parse(line).unwrap();
        assert_eq!(
            link.without,
            ["env", "-u", "IPHONEOS_DEPLOYMENT_TARGET", "-u", "TVOS_DEPLOYMENT_TARGET"]
        );
        assert_eq!(link.env, [("LC_ALL".to_owned(), "C".to_owned())]);
        assert_eq!(link.linker, "cc");
        assert_eq!(link.flavor, Flavor::Apple);
        assert_eq!(LinkLine::parse(LINE).unwrap().flavor, Flavor::Cc);
    }

    #[test]
    fn rustcs_copies_give_way_for_apple() {
        let dir = std::env::temp_dir().join(format!("rustd-plan-apple-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let copy = dir.join("a.1.rcgu.o");
        std::fs::write(&copy, b"not an object").unwrap();
        let line = format!(
            r#"env -u IPHONEOS_DEPLOYMENT_TARGET LC_ALL="C" "cc" "{}" "/t/libstd-3.rlib" "-arch" "arm64" "-o" "/t/deps/a-1""#,
            copy.display()
        );
        let mut link = LinkLine::parse(&line).unwrap();
        link.give_way(std::slice::from_ref(&copy)).unwrap();
        let response = dir.join("link.args");
        let command =
            link.command(&[Path::new("/p/rustd.o")], Path::new("/p/bin"), &response).unwrap();
        assert_eq!(
            shlex::split(&command).unwrap(),
            [
                "env",
                "-u",
                "IPHONEOS_DEPLOYMENT_TARGET",
                "LC_ALL=C",
                "cc",
                &format!("@{}", response.display())
            ]
        );
        let weak = dir.join(weaken::DIR).join("a.1.rcgu.o");
        assert!(weak.exists());
        let args = std::fs::read_to_string(&response).unwrap();
        let args: Vec<String> = args.lines().flat_map(|it| shlex::split(it).unwrap()).collect();
        assert_eq!(
            args,
            [
                "/p/rustd.o",
                ROOM_FOR_SEGMENTS,
                &format!("{ROOM_FOR_TABLES}{}", dir.join("rustd.room").display()),
                &weak.display().to_string(),
                "/t/libstd-3.rlib",
                "-arch",
                "arm64",
                "-o",
                "/p/bin.linking"
            ]
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn ours_go_ahead_of_rustcs_for_link_exe() {
        const LINE: &str = r#""C:\\v c\\link.exe" "/NOLOGO" "C:\\t\\rustc1\\symbols.o" "C:\\t\\a.1.rcgu.o" "C:\\t\\libb-2.rlib" "kernel32.lib" "/WX" "/LIBPATH:C:\\l\\" "/OUT:C:\\t\\a.exe" "/DEBUG" "/PDBALTPATH:%_PDB%""#;
        let dir = std::env::temp_dir().join(format!("rustd-plan-msvc-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let plan = Plan {
            crates: Vec::new(),
            object: PathBuf::from("P:/rustd.o"),
            patch: PathBuf::from("P:/patch.o"),
            binary: PathBuf::from("P:/bin"),
            link_cmd: String::new(),
            symbol_files: Vec::new(),
            copies: Vec::new(),
            stamp: 0,
            package: None,
        };
        let response = dir.join("link.args");
        let link = LinkLine::parse(LINE).unwrap();
        assert_eq!(link.flavor, Flavor::Msvc);
        let command = link.command(&[&plan.patch, &plan.object], &plan.binary, &response).unwrap();
        assert_eq!(command, format!(r#""C:\v c\link.exe" "@{}""#, response.display()));
        let args = std::fs::read_to_string(&response).unwrap();
        let args: Vec<&str> = args
            .lines()
            .filter(|it| !it.starts_with("\"/LIBPATH:") || it.contains(r"C:\l"))
            .collect();
        assert_eq!(
            args,
            [
                r#""/NOLOGO""#,
                r#""P:/patch.o""#,
                r#""P:/rustd.o""#,
                r#""/FORCE:MULTIPLE""#,
                r#""/IGNORE:4006""#,
                r#""C:\t\a.1.rcgu.o""#,
                r#""C:\t\libb-2.rlib""#,
                r#""kernel32.lib""#,
                r#""/LIBPATH:C:\l\\""#,
                r#""/OUT:P:/bin""#,
                r#""/DEBUG""#,
                r#""/PDBALTPATH:P:/bin.pdb""#,
                r#""/STACK:8388608""#,
            ]
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn ours_go_ahead_of_rustcs() {
        let dir = std::env::temp_dir().join(format!("rustd-plan-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let plan = Plan {
            crates: Vec::new(),
            object: PathBuf::from("/p/rustd.o"),
            patch: PathBuf::from("/p/patch.o"),
            binary: PathBuf::from("/p/bin"),
            link_cmd: String::new(),
            symbol_files: Vec::new(),
            copies: Vec::new(),
            package: None,
            stamp: 0,
        };
        let response = dir.join("link.args");
        let command = LinkLine::parse(LINE)
            .unwrap()
            .command(&[&plan.patch, &plan.object], &plan.binary, &response)
            .unwrap();
        let response_arg = format!("@{}", response.display());
        assert_eq!(
            shlex::split(&command).unwrap(),
            ["LC_ALL=C", "PATH=/t/bin:/usr/bin", "cc", response_arg.as_str()]
        );
        // As the driver reads the file: quoted where a shell would need it.
        let args = shlex::split(&std::fs::read_to_string(&response).unwrap()).unwrap();
        assert_eq!(
            args,
            [
                "-m64",
                "/p/patch.o",
                "/p/rustd.o",
                FIRST_DEFINITION_STAYS,
                "/t/deps/a.1.rcgu.o",
                "-Wl,-Bstatic",
                "/t/deps/libb-2.rlib",
                "-o",
                "/p/bin.linking",
                "-pie"
            ]
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
