//! rustd as the wrapper cargo runs rustc through for the crates of a workspace, under
//! `cargo rustd` and, once `rustd enable` named it in cargo's configuration, under plain
//! cargo. What rustc built of a crate is recorded for the daemon; a crate that is linked is
//! also asked for its link line and for the objects it was linked from. Under plain cargo a
//! crate of the workspace fails the build, naming the `cargo rustd` command that builds it.

use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use anyhow::Context as _;

use super::{
    ancestor::Cargo,
    say, script,
    switch::Enabled,
    units::{Copied, Record, STANDS_IN, stamp_now},
};
use crate::stub::VALUED;

/// The variable `cargo rustd` sets for the cargo it runs: the wrapper records what rustc
/// builds and leaves the rest to the command that drives cargo.
pub(crate) const DRIVEN: &str = "RUSTD_CARGO_DRIVES";

/// The variable `cargo rustd` sets in the first build of a workspace: the roots of the
/// crates that are the daemon's to compile, as a list of paths.
pub(crate) const STAGED: &str = "RUSTD_STAGED_CRATES";

/// What the variables that name the programs of a build start with.
const PROGRAM_OF: &str = "CARGO_BIN_EXE_";
/// The variable that names the directory cargo gives the integration tests of a build.
const SCRATCH: &str = "CARGO_TARGET_TMPDIR";

/// The codegen option cargo names rustc's incremental directory with, as its own argument
/// after `-C`.
const INCREMENTAL: &str = "incremental";

/// The object of rustc's that names what a program needs of the libraries linked after it.
const SYMBOLS: &str = "symbols.o";

/// Builds what cargo asked rustc for and ends as rustc would have.
pub(crate) fn command(mut args: impl Iterator<Item = OsString>) -> anyhow::Result<()> {
    let rustc = args.next().context("cargo names rustc first")?;
    let args: Vec<OsString> = args.collect();
    // The wrapper the user had for the workspace's crates still runs rustc.
    let mut compiler = match Enabled::read().and_then(|it| it.chained) {
        Some(chained) => {
            let mut command = Command::new(chained);
            command.arg(&rustc);
            command
        }
        None => Command::new(&rustc),
    };
    compiler.args(&args);
    let Some(unit) = Unit::of(&args) else {
        std::process::exit(compiler.status()?.code().unwrap_or(1));
    };
    let dir = unit.records.join(&unit.id);
    if unit.is_staged() {
        match unit.stood_in(&rustc, &dir) {
            Ok(code) => std::process::exit(code),
            // The crate is the daemon's to compile, and rustc is not asked in its place.
            Err(why) => {
                say::error(&format!("rustd does not build `{}`: {why:#}", unit.crate_name));
                std::process::exit(1)
            }
        }
    }
    // Plain cargo with rustd enabled: the workspace is the daemon's, and only `cargo rustd`
    // asks it for a build.
    if std::env::var_os(DRIVEN).is_none() && !unit.runs_in_build() {
        say::error(&format!("rustd does not build `{}`: {}", unit.crate_name, plain_refusal()));
        std::process::exit(super::FAILED);
    }
    let stamp = stamp_now();
    let copies = dir.join(stamp.to_string());
    let line = copies.join("link.line");
    if unit.linked {
        std::fs::create_dir_all(&copies)?;
        compiler.arg(format!("--print=link-args={}", line.display())).arg("-Csave-temps");
    }
    let status =
        compiler.status().with_context(|| format!("running {}", Path::new(&rustc).display()))?;
    if status.success()
        && let Err(error) = unit.record(stamp, &copies, unit.linked.then_some(line), &unit.source)
    {
        // The build is good; the daemon has no part in this crate until it is built again.
        eprintln!("warning: rustd did not record `{}`: {error:#}", unit.id);
    }
    std::process::exit(status.code().unwrap_or(1));
}

/// Why plain cargo builds no crate of a workspace while rustd is enabled, and what does.
fn plain_refusal() -> String {
    let asked = Cargo::above().map_or_else(|_| "build".to_owned(), |it| it.args.join(" "));
    format!(
        "plain cargo does not build a workspace while rustd is enabled; `cargo rustd {asked}` \
         builds it, and `rustd disable` gives plain cargo its builds back"
    )
}

/// A run of rustc that compiles a crate, as cargo's arguments describe it.
struct Unit {
    id: String,
    crate_name: String,
    args: Vec<String>,
    source: PathBuf,
    cwd: PathBuf,
    records: PathBuf,
    /// Whether rustc links a program of the workspace from it.
    linked: bool,
    /// Whether rustc links a build script from it.
    script: bool,
}

impl Unit {
    /// `None` for a run that compiles nothing to record: a question to rustc (`--print`,
    /// `-vV`), source on standard input, or arguments that are not text.
    fn of(args: &[OsString]) -> Option<Unit> {
        let args: Vec<String> =
            args.iter().map(|it| it.to_str().map(str::to_owned)).collect::<Option<_>>()?;
        let value = |flag: &str| {
            let at = args.iter().position(|it| it == flag)?;
            args.get(at + 1).cloned()
        };
        let crate_name = value("--crate-name")?;
        let out_dir = value("--out-dir")?;
        if args.iter().any(|it| it == "-" || it.starts_with("--print")) {
            return None;
        }
        // The one argument that is a path to a Rust file and not the value of a flag.
        let source = (0..args.len()).find(|&at| {
            args[at].ends_with(".rs") && !(at > 0 && VALUED.contains(&args[at - 1].as_str()))
        })?;
        let cwd = std::env::current_dir().ok()?;
        let mut unit = Unit {
            id: String::new(),
            crate_name,
            source: cwd.join(&args[source]),
            records: Record::dir_for(&cwd.join(out_dir)),
            args,
            cwd,
            linked: false,
            script: false,
        };
        let record = unit.as_record(0, Vec::new(), None);
        let emits_link = unit.args.iter().any(|it| {
            it.strip_prefix("--emit=").is_some_and(|kinds| kinds.split(',').any(|it| it == "link"))
        });
        // A unit that is only checked leaves nothing the daemon reads.
        if !emits_link {
            return None;
        }
        unit.script = record.is_build_script();
        unit.linked = record.is_linked() && !record.runs_in_build();
        unit.id =
            format!("{}{}", unit.crate_name, record.codegen("extra-filename").unwrap_or_default());
        Some(unit)
    }

    /// Whether the crate runs during the build, as a build script or a proc macro.
    fn runs_in_build(&self) -> bool {
        self.script || self.as_record(0, Vec::new(), None).runs_in_build()
    }

    /// Whether the crate is one the first build of the workspace leaves to the daemon.
    fn is_staged(&self) -> bool {
        let Some(staged) = std::env::var_os(STAGED) else { return false };
        let lists = std::env::split_paths(&staged).any(|it| it == self.source);
        lists && !self.script
    }

    /// Has rustc do of the crate what it does in a build by the daemon: check it, and
    /// build what stands in for it, which is what cargo links and has no code. `dir` is
    /// where the unit is recorded. `Ok` is the status rustc's check ended with; `Err` is
    /// why nothing stands in for the crate.
    ///
    /// What stands in is built first and from the libraries that stand in for the crates
    /// it depends on, and the check reads the metadata of the checks of those. Cargo
    /// starts the units that depend on this one when the check has written the metadata,
    /// which is when both are there.
    fn stood_in(&self, rustc: &OsString, dir: &Path) -> anyhow::Result<i32> {
        let program = crate::stub::is_program(&self.args).context("not a library or a program")?;
        let stamp = stamp_now();
        let copies = dir.join(stamp.to_string());
        std::fs::create_dir_all(&copies)?;
        let line = copies.join("link.line");
        let extra = self.as_record(0, Vec::new(), None);
        let stem =
            format!("{}{}", self.crate_name, extra.codegen("extra-filename").unwrap_or_default());
        let source = copies.join(format!("{stem}.rustd.rs"));
        std::fs::write(&source, crate::stub::text_of(&self.args, program))?;

        let mut stand_in = Command::new(rustc);
        let mut args = self.args.iter().peekable();
        while let Some(arg) = args.next() {
            let incremental = |it: &&String| it.starts_with(&format!("{INCREMENTAL}="));
            if arg == "-C" && args.peek().is_some_and(incremental) {
                args.next();
            } else if self.cwd.join(arg) == self.source {
                stand_in.arg(&source);
            } else if let Some(kinds) = arg.strip_prefix("--emit=") {
                // The metadata is what cargo holds for the library being there.
                let kept = kinds.split(',').filter(|it| matches!(*it, "link" | "metadata"));
                stand_in.arg(format!("--emit={}", kept.collect::<Vec<_>>().join(",")));
            } else {
                stand_in.arg(self.standing_in(arg).unwrap_or_else(|| arg.clone()));
            }
        }
        if program {
            stand_in.arg(format!("--print=link-args={}", line.display())).arg("-Csave-temps");
        }
        let built = stand_in.stdin(Stdio::null()).output().context("running rustc")?;
        anyhow::ensure!(
            built.status.success(),
            "what stands in for it does not build: {}",
            String::from_utf8_lossy(&built.stderr).trim_end()
        );
        self.write_dep_info(&stem).context("writing the dep-info of what stands in")?;
        std::fs::write(dir.join(STANDS_IN), "")?;

        // The crate is not checked by rustc: the daemon's front end is what checks it, and a
        // second compile beside the daemon's would only compete with it.
        self.record(stamp, &copies, program.then_some(line), &source)?;
        Ok(0)
    }

    /// Writes the dep-info cargo reads to know what the crate is compiled from, which rustc
    /// is not asked for: nothing. What stands in is the same whatever the crate's sources,
    /// which are the daemon's, and a file written during the build, as its own source is,
    /// is newer than the build to cargo. Without the file, or with a file cargo finds
    /// newer, any cargo run later in the same environment (one a test or program runs)
    /// builds the crate again with rustc and puts its program where the daemon's is.
    fn write_dep_info(&self, stem: &str) -> std::io::Result<()> {
        let Some(out_dir) = self.args.windows(2).find(|it| it[0] == "--out-dir") else {
            return Ok(());
        };
        let to = self.cwd.join(&out_dir[1]).join(format!("{stem}.d"));
        std::fs::write(&to, format!("{}:\n", to.display().to_string().replace(' ', "\\ ")))
    }

    /// `--extern`'s value `named` with the library that stands in for the crate, when the
    /// value is the metadata of a crate that has one.
    fn standing_in(&self, named: &str) -> Option<String> {
        let (name, path) = named.split_once('=')?;
        let stem = Path::new(path).file_name()?.to_str()?.strip_suffix(".rmeta")?;
        let id = stem.strip_prefix("lib")?;
        self.records
            .join(id)
            .join(STANDS_IN)
            .exists()
            .then(|| format!("{name}={}", Path::new(path).with_extension("rlib").display()))
    }

    fn as_record(&self, stamp: u128, copies: Vec<Copied>, link_line: Option<PathBuf>) -> Record {
        Record {
            id: self.id.clone(),
            crate_name: self.crate_name.clone(),
            cwd: self.cwd.clone(),
            args: self.args.clone(),
            source: self.source.clone(),
            stamp,
            copies,
            link_line,
            env: std::env::vars()
                .filter(|(name, _)| name.starts_with(PROGRAM_OF) || name == SCRATCH)
                .collect(),
        }
    }

    /// Copies what a later build of the unit writes over and writes the record.
    /// `compiled` is the root of the source rustc was given.
    fn record(
        &self,
        stamp: u128,
        to: &Path,
        link_line: Option<PathBuf>,
        compiled: &Path,
    ) -> anyhow::Result<()> {
        let record = self.as_record(stamp, Vec::new(), link_line.clone());
        // The executable is the daemon's to link; of the outputs it reads the libraries.
        let libraries =
            record.outputs().into_iter().filter(|it| it.extension().is_some_and(|it| it == "rlib"));
        let mut originals: Vec<PathBuf> = libraries.filter(|it| it.exists()).collect();
        if let Some(line) = &link_line {
            let line = std::fs::read_to_string(line)
                .with_context(|| format!("rustc wrote no link line to {}", line.display()))?;
            let args = shlex::split(&line).context("the link line is not quoted as a shell's")?;
            // `symbols.o` asks for what the program needs of the libraries after it, as the
            // panic runtime, and is gone with rustc's directory.
            let objects = args
                .into_iter()
                .filter(|it| it.ends_with(".rcgu.o") || it.ends_with(SYMBOLS))
                .map(PathBuf::from);
            originals.extend(objects.filter(|it| it.exists()));
        }
        std::fs::create_dir_all(to)?;
        let mut copies = Vec::new();
        for original in originals {
            let name = original.file_name().context("an output without a name")?;
            let copy = to.join(name);
            std::fs::copy(&original, &copy)
                .with_context(|| format!("copying {}", original.display()))?;
            copies.push(Copied { original, copy });
        }
        // The daemon tells which crate a file of rustc's is by the dep-info next to it, of
        // which it reads the first source: the root of the crate.
        let stem =
            format!("{}{}", self.crate_name, record.codegen("extra-filename").unwrap_or_default());
        std::fs::write(to.join(format!("{stem}.d")), format!("{stem}: {}\n", compiled.display()))?;
        if self.script
            && let Some(linked) = record.outputs().first()
        {
            script::stand_in_front(linked)?;
        }
        self.as_record(stamp, copies, link_line).write(&self.records)
    }
}
