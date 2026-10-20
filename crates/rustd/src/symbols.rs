//! Maps Rust paths to the mangled names rustc gave them, read from rlibs and objects.

use std::{
    hash::{DefaultHasher, Hash, Hasher},
    path::{Path, PathBuf},
    time::SystemTime,
};

use anyhow::Context;
use object::{Object, ObjectSymbol, SymbolKind, read::archive::ArchiveFile};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Default)]
pub(crate) struct SymbolTable {
    /// The symbols any object of the link can refer to, by path.
    linkable: Paths,
    /// The writable statics only the object that defines them can refer to, by path.
    private_statics: Paths,
    /// The file and the member of it that defines each of `private_statics`, by symbol.
    held_in: FxHashMap<String, (usize, usize)>,
    /// The files read, which `held_in` indexes.
    files: Vec<PathBuf>,
    /// Every symbol an object refers to and leaves to another to define, hashed.
    referred: FxHashSet<u64>,
    /// rustc's `StableCrateId` of each crate named in a symbol. `None` when two crates share
    /// the name, two versions of one package say.
    crates: FxHashMap<String, Option<u64>>,
    /// The `StableCrateId` of the crate whose source starts at a file, for the crates that
    /// share a name. Their paths keep the `name[id]` rustc mangled into the symbol.
    by_root: FxHashMap<Build, u64>,
    /// The crates of the link, each by its name and the file it starts at.
    linked: FxHashSet<(String, PathBuf)>,
    /// Every symbol defined or referred to, hashed: two that hash alike are not expected.
    names: FxHashSet<u64>,
    /// The paths of the functions defined under a symbol private to its object, hashed.
    private: FxHashSet<u64>,
    /// The files rustc built that cargo left a dep-info file for, each with its sources.
    built_from: Vec<(PathBuf, Vec<Source>)>,
    /// When the files started to be read.
    read: Option<SystemTime>,
    /// The copies crates made of one instance, by the symbol without the crate that made it.
    copies: FxHashMap<String, Vec<String>>,
    /// The crates that made a copy of an instance of a function, by the function's name
    /// alone: what there is to go by for an instance whose types cannot be spelled.
    makers: FxHashMap<String, FxHashSet<u64>>,
}

/// Symbols by the paths they demangle to.
#[derive(Default)]
pub(crate) struct Paths {
    /// More than one symbol for the items that print as one path: of two `const _` blocks of
    /// a module, or of one name in one function. Linking one to another's symbol is a
    /// miscompile.
    by_path: FxHashMap<String, Vec<Placed>>,
    /// Symbols of items nested in closures and anonymous constants, by their path without the
    /// `{closure#0}`-like segments, with the numbers of the closures among those.
    nested: FxHashMap<String, Vec<NestedSymbol>>,
}

/// Who can refer to a symbol an object defines.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reach {
    /// Any object of the link.
    Linkable,
    /// Only its own object: a function.
    PrivateFunction,
    /// Only its own object: a writable static.
    PrivateStatic,
}

struct NestedSymbol {
    name: String,
    closures: Vec<u32>,
    place: Option<u64>,
    around: Vec<u64>,
}

struct Placed {
    name: String,
    /// The place of the item among those of its name in what it is written in, which rustc
    /// mangles into the symbol and no path says. `None` for a symbol we can't read it from.
    place: Option<u64>,
    /// The places of the items it is written in, the outermost first.
    around: Vec<u64>,
}

/// A linkable symbol: its mangled name and its path with and without crate ids.
struct Symbol {
    reach: Reach,
    name: String,
    place: Option<u64>,
    around: Vec<u64>,
    with_ids: String,
    path: String,
}

/// A file of the source of a crate rustc built.
#[derive(Debug)]
struct Source {
    path: PathBuf,
    /// What a file that a build script wrote came to when the symbols were read. cargo runs
    /// a script again without building the crate again when the script says the same, so
    /// when such a file was written says nothing.
    generated: Option<u64>,
}

impl Source {
    fn new(path: PathBuf) -> Source {
        let names: Vec<&str> = path.components().filter_map(|c| c.as_os_str().to_str()).collect();
        let of_script = names.windows(3).any(|it| it[0] == "build" && it[2] == "out");
        let generated = of_script.then(|| content(&path)).flatten();
        Source { path, generated }
    }

    /// Whether the file is another than the one rustc read when it finished at `built`.
    fn written_since(&self, built: SystemTime) -> bool {
        match self.generated {
            Some(generated) => content(&self.path) != Some(generated),
            None => written(&self.path).is_some_and(|it| it > built),
        }
    }
}

fn written(file: &Path) -> Option<SystemTime> {
    std::fs::metadata(file).and_then(|it| it.modified()).ok()
}

fn content(file: &Path) -> Option<u64> {
    let mut hasher = DefaultHasher::new();
    std::fs::read(file).ok()?.hash(&mut hasher);
    Some(hasher.finish())
}

/// A symbol of an object, and how it demangles when it is one of Rust's.
struct Named {
    name: String,
    reach: Reach,
    /// The member of the archive it is defined in, `0` in an object.
    member: usize,
    /// Whether the object refers to it and leaves it to another to define.
    undefined: bool,
    /// With the ids of the crates it names, and without them.
    demangled: Option<(String, String)>,
}

impl Named {
    fn new(name: &str, reach: Reach, member: usize) -> Named {
        // The memory a static points to is a symbol that demangles to the static's path.
        let demangled = (!name.starts_with("_RNn"))
            .then(|| rustc_demangle::try_demangle(name).ok())
            .flatten()
            // `{:#}` drops the crate disambiguator hashes.
            .map(|it| (it.to_string(), format!("{it:#}")));
        Named { name: name.to_owned(), reach, member, undefined: false, demangled }
    }
}

/// The symbols of each of `files`, which are objects or archives of them, read on every core.
fn names_of(files: &[PathBuf]) -> Vec<anyhow::Result<Vec<Named>>> {
    let next = std::sync::atomic::AtomicUsize::new(0);
    let read = || {
        let mut read = Vec::new();
        loop {
            let at = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let Some(file) = files.get(at) else { return read };
            read.push((at, names_of_file(file)));
        }
    };
    let threads = std::thread::available_parallelism().map_or(1, |it| it.get()).min(files.len());
    let mut read: Vec<_> = std::thread::scope(|scope| {
        let threads: Vec<_> = (0..threads).map(|_| scope.spawn(read)).collect();
        threads.into_iter().flat_map(|it| it.join().expect("reading symbols panicked")).collect()
    });
    read.sort_by_key(|it| it.0);
    read.into_iter().map(|it| it.1).collect()
}

fn names_of_file(file: &Path) -> anyhow::Result<Vec<Named>> {
    let data = std::fs::read(file).with_context(|| format!("reading {}", file.display()))?;
    let mut names = Vec::new();
    match ArchiveFile::parse(&*data) {
        Ok(archive) => {
            for (at, member) in archive.members().enumerate() {
                names_of_object(member?.data(&*data)?, at, &mut names);
            }
        }
        Err(_) => names_of_object(&data, 0, &mut names),
    }
    Ok(names)
}

fn names_of_object(data: &[u8], member: usize, names: &mut Vec<Named>) {
    // rlibs also hold `lib.rmeta`, which isn't an object file.
    let Ok(object) = object::File::parse(data) else { return };
    for symbol in object.symbols() {
        // A reference is as good as a definition: something in the link defines it.
        // Not `is_definition`, which leaves out thread locals.
        // A wasm object's data is in segments, which are not sections.
        let in_segment = object.format() == object::BinaryFormat::Wasm
            && symbol.section() == object::SymbolSection::Unknown;
        let defined = symbol.section_index().is_some() || symbol.is_common() || in_segment;
        let linkable = symbol.is_undefined() || (defined && symbol.is_global());
        let private = defined && symbol.is_local();
        let reach = match symbol.kind() {
            _ if linkable => Reach::Linkable,
            SymbolKind::Text if private => Reach::PrivateFunction,
            SymbolKind::Data | SymbolKind::Tls if private && is_writable(&object, &symbol) => {
                Reach::PrivateStatic
            }
            _ => continue,
        };
        let Ok(name) = symbol.name() else { continue };
        let name = unprefixed(&object, name);
        if reach == Reach::PrivateStatic && !name.starts_with("_R") {
            continue;
        }
        let mut named = Named::new(name, reach, member);
        named.undefined = symbol.is_undefined();
        names.push(named);
    }
}

/// Mach-O spells every name of C and Rust with an underscore in front, which the writer of an
/// object adds back.
fn unprefixed<'a>(object: &object::File, name: &'a str) -> &'a str {
    match object.format() {
        object::BinaryFormat::MachO => name.strip_prefix('_').unwrap_or(name),
        _ => name,
    }
}

fn is_writable<'data>(object: &object::File<'data>, symbol: &object::Symbol<'data, '_>) -> bool {
    use object::{ObjectSection, SectionKind};
    let Some(section) = symbol.section_index().and_then(|it| object.section_by_index(it).ok())
    else {
        return false;
    };
    matches!(
        section.kind(),
        SectionKind::Data
            | SectionKind::UninitializedData
            | SectionKind::Tls
            | SectionKind::UninitializedTls
    )
}

/// A crate rustc built: the file its source starts at, and whether it is the program itself,
/// linked from its objects, or a library of it. The unit tests of a library are the first
/// of its source, and link the second when what they use uses the library.
type Build = (PathBuf, bool);

impl SymbolTable {
    /// `root` is what the paths in cargo's dep-info files are relative to.
    pub(crate) fn load(files: &[PathBuf], root: &Path) -> anyhow::Result<SymbolTable> {
        let mut table = SymbolTable { read: Some(SystemTime::now()), ..SymbolTable::default() };
        let mut symbols = Vec::new();
        let mut owners = Vec::new();
        for (at, (file, names)) in files.iter().zip(names_of(files)).enumerate() {
            let first = symbols.len();
            for name in names? {
                if name.undefined {
                    table.referred.insert(Self::hashed(&name.name));
                }
                if name.reach == Reach::PrivateStatic {
                    table.held_in.insert(name.name.clone(), (at, name.member));
                }
                table.add_name(name, &mut symbols);
            }
            if let Some((name, sources)) = crate_sources(file, root) {
                let program = file.extension().is_none_or(|it| it != "rlib");
                owners.push((name, (sources[0].clone(), program), first..symbols.len()));
                let sources = sources.into_iter().map(Source::new).collect();
                table.built_from.push((file.clone(), sources));
            }
        }
        // A crate's symbols mention the crates of its name that it depends on (a binary
        // instantiates the generics of its library) besides itself, and never one that depends
        // on it: the id that is left once the others have theirs is its own. A crate may be
        // several files, when it is linked from its objects.
        let mut unplaced: FxHashMap<Build, FxHashMap<u64, usize>> = FxHashMap::default();
        for (name, source, range) in owners {
            table.linked.insert((name.clone(), source.0.clone()));
            if table.crates.get(&name) != Some(&None) {
                continue;
            }
            let mentions = unplaced.entry(source).or_default();
            for symbol in &symbols[range] {
                for (_, id) in crate_ids(&symbol.with_ids).filter(|it| it.0 == name) {
                    *mentions.entry(id).or_default() += 1;
                }
            }
        }
        table.place(unplaced);
        table.index(symbols);
        table.files = files.to_vec();
        Ok(table)
    }

    /// The table of the symbols named, for a link that is not read from files.
    #[allow(dead_code)] // `rustd-wasm` builds this file too, and has no files to read.
    pub(crate) fn of_names<'a>(names: impl IntoIterator<Item = &'a str>) -> SymbolTable {
        let mut table = SymbolTable::default();
        let mut symbols = Vec::new();
        for name in names {
            table.add_name(Named::new(name, Reach::Linkable, 0), &mut symbols);
        }
        table.index(symbols);
        table
    }

    /// Files the symbols under their paths, once every crate named in one is known.
    fn index(&mut self, symbols: Vec<Symbol>) {
        let table = self;
        for Symbol { reach, name, place, around, with_ids, path } in symbols {
            let shared = |krate: &str| table.crates.get(krate) == Some(&None);
            let path = if crate_ids(&with_ids).any(|(krate, _)| shared(krate)) {
                without_ids(&with_ids, |krate| !shared(krate))
            } else {
                path
            };
            match reach {
                Reach::Linkable => table.linkable.insert(path, name, place, around),
                Reach::PrivateFunction => _ = table.private.insert(Self::hashed(&path)),
                Reach::PrivateStatic => table.private_statics.insert(path, name, place, around),
            }
        }
    }

    fn hashed(symbol: &str) -> u64 {
        use std::hash::BuildHasher;
        rustc_hash::FxBuildHasher.hash_one(symbol)
    }

    /// Whether the function at `path` is defined under a symbol private to its object.
    pub(crate) fn private(&self, path: &str) -> bool {
        self.private.contains(&Self::hashed(path))
    }

    pub(crate) fn defines(&self, symbol: &str) -> bool {
        self.names.contains(&Self::hashed(symbol))
    }

    fn add_name(&mut self, named: Named, symbols: &mut Vec<Symbol>) {
        let Named { name, reach, demangled, .. } = named;
        let instance = without_instantiating_crate(&name);
        if reach == Reach::Linkable
            && self.names.insert(Self::hashed(&name))
            && instance.len() != name.len()
        {
            self.copies.entry(instance.to_owned()).or_default().push(name.clone());
        }
        let Some((with_ids, path)) = demangled else { return };
        for (krate, id) in crate_ids(&with_ids) {
            match self.crates.get_mut(krate) {
                Some(known) if *known != Some(id) => *known = None,
                Some(_) => {}
                None => {
                    self.crates.insert(krate.to_owned(), Some(id));
                }
            }
        }
        if instance.len() != name.len()
            && let Some(maker) = V0::instantiating_crate(&name)
            && let Some(function) = function_name(&path)
        {
            self.makers.entry(function).or_default().insert(maker);
        }
        let place = V0::place(&name);
        let around = V0::places_around(&name).unwrap_or_default();
        symbols.push(Symbol { reach, name, place, around, with_ids, path });
    }

    /// How paths spell the crate named `name` whose source starts at `root`: `name[id]` when
    /// another crate has the name too. `program` is whether it is the program's own crate.
    pub(crate) fn crate_path(&self, name: &str, root: &Path, program: bool) -> Option<String> {
        match self.crates.get(name) {
            Some(None) => Some(format!("{name}[{:x}]", self.id_by_root(root, program)?)),
            _ => Some(name.to_owned()),
        }
    }

    /// The id of the build of the source at `root` that is the program's own crate or is
    /// not, and of the only build of it when there is one.
    fn id_by_root(&self, root: &Path, program: bool) -> Option<u64> {
        let of = |program: bool| self.by_root.get(&(root.to_owned(), program)).copied();
        of(program).or_else(|| of(!program))
    }

    /// Gives each crate that shares its name the id that is its own, from how often its symbols
    /// mention each id of that name.
    fn place(&mut self, mut unplaced: FxHashMap<Build, FxHashMap<u64, usize>>) {
        loop {
            let taken: FxHashSet<u64> = self.by_root.values().copied().collect();
            let before = unplaced.len();
            unplaced.retain(|source, mentions| {
                let mut free = mentions.keys().filter(|id| !taken.contains(id));
                match (free.next(), free.next()) {
                    (Some(&id), None) => {
                        self.by_root.insert(source.clone(), id);
                        false
                    }
                    _ => true,
                }
            });
            if unplaced.len() == before {
                break;
            }
        }
        // The other crate of the name is none of these files (a test named `test`, and the
        // sysroot's): a guess, that a crate mentions itself more than it does the other.
        for (source, mentions) in unplaced {
            if let Some((&id, _)) = mentions.iter().max_by_key(|(_, count)| **count) {
                self.by_root.insert(source, id);
            }
        }
    }

    /// Whether the crate named `name` whose source starts at `root` is one of the link. A
    /// bench may be named as the library, start where a test does, and be another program.
    pub(crate) fn links(&self, name: &str, root: &Path) -> bool {
        self.linked.contains(&(name.to_owned(), root.to_owned()))
    }

    /// A source that was written after rustc built the crate it is of: what rustc built is
    /// then not what it would build now.
    pub(crate) fn written_since_built(&self) -> Option<&Path> {
        self.built_from.iter().find_map(|(built, sources)| {
            let built = written(built)?;
            sources.iter().find(|it| it.written_since(built)).map(|it| &*it.path)
        })
    }

    /// Every source that was written after rustc built the crate it is of.
    pub(crate) fn all_written_since_built(&self) -> impl Iterator<Item = &Path> {
        self.built_from.iter().flat_map(|(built, sources)| {
            let built = written(built);
            sources
                .iter()
                .filter(move |it| built.is_some_and(|built| it.written_since(built)))
                .map(|it| &*it.path)
        })
    }

    /// Whether rustc has built one of the files again since they were read.
    pub(crate) fn built_since_read(&self) -> bool {
        self.read.is_some_and(|read| {
            self.built_from.iter().any(|(built, _)| written(built).is_some_and(|it| it > read))
        })
    }

    pub(crate) fn stable_crate_id(&self, name: &str, root: &Path, program: bool) -> Option<u64> {
        match *self.crates.get(name)? {
            Some(id) => Some(id),
            None => self.id_by_root(root, program),
        }
    }

    /// The symbol of the one item at `path`, as [`Paths::get`] says, that any object can link.
    pub(crate) fn get(&self, path: &str) -> Option<&str> {
        self.linkable.get(path)
    }

    pub(crate) fn get_at(&self, path: &str, place: u64, around: &[u64]) -> Option<&str> {
        self.linkable.get_at(path, place, around)
    }

    pub(crate) fn get_nested(
        &self,
        named: &str,
        closures: &[u32],
        place: u64,
        around: &[u64],
    ) -> Option<&str> {
        self.linkable.get_nested(named, closures, place, around)
    }

    /// The symbols any object of the link can refer to.
    pub(crate) fn linkable(&self) -> &Paths {
        &self.linkable
    }

    /// The writable statics rustc keeps to the objects that define them.
    pub(crate) fn private_statics(&self) -> &Paths {
        &self.private_statics
    }

    /// The symbols rustc's copy of the private static `symbol` is reached from, in its own
    /// object, that any object can refer to: rustc's copy is only used when one of those is
    /// called. `None` when something else reaches it too: another object, or a section the
    /// linker keeps whatever refers to it.
    pub(crate) fn only_reached_from(&self, symbol: &str) -> Option<Vec<String>> {
        let &(file, member) = self.held_in.get(symbol)?;
        let data = std::fs::read(self.files.get(file)?).ok()?;
        let object = match ArchiveFile::parse(&*data) {
            Ok(archive) => archive.members().nth(member)?.ok()?.data(&*data).ok()?,
            Err(_) => &data,
        };
        let reached = reached_from(&object::File::parse(object).ok()?, symbol)?;
        let referred = |it: &String| self.referred.contains(&Self::hashed(it));
        (!reached.iter().any(referred)).then_some(reached)
    }

    /// The copies of the instance `symbol` is one of, each with rustc's `StableCrateId` of
    /// the crate that compiled it. None for a symbol that is of one crate only.
    pub(crate) fn copies(&self, symbol: &str) -> impl Iterator<Item = (&str, u64)> {
        let copies = self.copies.get(without_instantiating_crate(symbol));
        copies.into_iter().flatten().filter_map(|it| Some((&**it, V0::instantiating_crate(it)?)))
    }

    /// rustc's `StableCrateId` of each crate that made a copy of an instance of a function
    /// named `function`, in any module and of any type.
    pub(crate) fn makers(&self, function: &str) -> impl Iterator<Item = u64> {
        self.makers.get(function).into_iter().flatten().copied()
    }

    pub(crate) fn len(&self) -> usize {
        self.linkable.by_path.len()
    }
}

impl Paths {
    fn insert(&mut self, path: String, name: String, place: Option<u64>, around: Vec<u64>) {
        // A closure is not an item nested in itself.
        let unnamed = path.rsplit("::").next().is_some_and(|last| last.starts_with('{'));
        if path.contains("::{") && !unnamed {
            let named: Vec<_> = path.split("::").filter(|it| !it.starts_with('{')).collect();
            let closures = path
                .split("::")
                .filter_map(|it| it.strip_prefix("{closure#")?.strip_suffix('}')?.parse().ok())
                .collect();
            let symbols = self.nested.entry(named.join("::")).or_default();
            if symbols.iter().all(|it| it.name != name) {
                let around = around.clone();
                symbols.push(NestedSymbol { name: name.clone(), closures, place, around });
            }
        }
        let known = self.by_path.entry(path).or_default();
        let same = |it: &Placed| {
            without_instantiating_crate(&it.name) == without_instantiating_crate(&name)
        };
        if !known.iter().any(same) {
            known.push(Placed { name, place, around });
        }
    }

    /// The symbol of the one item at `path`. A symbol that is alone at its path and is not
    /// the first of its name there is of another item than the one the path was read from:
    /// rustc wrote that item itself, as it does the `main` of a test executable, and built
    /// nothing of the one in the source.
    pub(crate) fn get(&self, path: &str) -> Option<&str> {
        match &**self.by_path.get(path)? {
            [only] if only.place.is_none_or(|it| it == 0) => Some(&only.name),
            _ => None,
        }
    }

    /// The symbol of the item at `path` that is the `place`th of its name in what it is
    /// written in. `around` are the places of the innermost items it is written in, as far
    /// out as they tell it apart: a static in the value of the second static of a name.
    pub(crate) fn get_at(&self, path: &str, place: u64, around: &[u64]) -> Option<&str> {
        let mut symbols = match &**self.by_path.get(path)? {
            [only] => {
                return Some(only)
                    .filter(|it| it.place.is_none_or(|it| it == place))
                    .map(|it| &*it.name);
            }
            symbols => {
                symbols.iter().filter(|it| it.place == Some(place) && it.around.ends_with(around))
            }
        };
        let symbol = symbols.next()?;
        symbols.next().is_none().then_some(&*symbol.name)
    }

    /// The symbol of an item whose path has unnamed segments between the named ones given.
    ///
    /// `closures` are the numbers rustc gives the closures around the item, outermost first,
    /// which tell apart the items that only differ in those, and `place` and `around` are as
    /// in `get_at`. Anonymous constants are not numbered, so two items that differ in one of
    /// those have no symbol here.
    pub(crate) fn get_nested(
        &self,
        named: &str,
        closures: &[u32],
        place: u64,
        around: &[u64],
    ) -> Option<&str> {
        let here = |it: &&NestedSymbol| it.place.is_none_or(|known| known == place);
        let mut symbols = match &**self.nested.get(named)? {
            // Its closures may be numbered otherwise than here, but are as many.
            [only] => {
                return Some(only)
                    .filter(here)
                    .filter(|it| it.closures.len() == closures.len())
                    .map(|it| &*it.name);
            }
            symbols => symbols
                .iter()
                .filter(here)
                .filter(|it| it.closures == closures && it.around.ends_with(around)),
        };
        let symbol = symbols.next()?;
        symbols.next().is_none().then_some(&*symbol.name)
    }
}

/// The symbols that any object can refer to of the code and data of `object` that reach the
/// static `symbol` through what they refer to: what uses it. `None` when one of those is
/// something the linker keeps whatever refers to it.
///
/// What is told apart is what a linker can leave out apart: a section of an ELF or COFF object,
/// and in a section of a Mach-O one, the run from one symbol that is not a temporary label to
/// the next.
fn reached_from<'data>(object: &object::File<'data>, symbol: &str) -> Option<Vec<String>> {
    use object::{ObjectSection, RelocationTarget, SectionFlags, SectionKind};
    // A section and where in it the piece starts; `u64::MAX` for what refers to the section
    // and not to a piece of it.
    type Piece = (object::SectionIndex, u64);
    const WHOLE: u64 = u64::MAX;
    let macho = object.format() == object::BinaryFormat::MachO;
    let named = |it: &object::Symbol<'data, '_>| it.name().map(|name| unprefixed(object, name));
    let mut starts = FxHashMap::<object::SectionIndex, Vec<u64>>::default();
    if macho {
        for it in object.symbols() {
            let temporary = it.name().is_ok_and(|name| name.starts_with(['l', 'L']));
            if let Some(section) = it.section_index().filter(|_| !temporary) {
                starts.entry(section).or_default().push(it.address());
            }
        }
        starts.values_mut().for_each(|it| {
            it.sort_unstable();
            it.dedup();
        });
    }
    let piece = |section: object::SectionIndex, address: u64| -> Piece {
        let Some(starts) = starts.get(&section) else { return (section, 0) };
        let at = starts.partition_point(|it| *it <= address);
        (section, at.checked_sub(1).map_or(0, |at| starts[at]))
    };
    let start = object.symbols().find(|it| named(it) == Ok(symbol))?;
    let start = piece(start.section_index()?, start.address());
    let mut defined = FxHashMap::<Piece, Vec<String>>::default();
    for it in object.symbols() {
        if let (Some(section), true, Ok(name)) = (it.section_index(), it.is_global(), named(&it)) {
            defined.entry(piece(section, it.address())).or_default().push(name.to_owned());
        }
    }
    // What the unwinder and a debugger read refers to everything, and uses nothing.
    let read_aside = |name: &str| {
        [".debug", ".eh_frame", "__debug", "__eh_frame", "__compact_unwind", ".pdata", ".xdata"]
            .iter()
            .any(|it| name.starts_with(it))
    };
    let mut referrers = FxHashMap::<Piece, FxHashSet<Piece>>::default();
    for section in object.sections() {
        if read_aside(section.name().unwrap_or_default()) {
            continue;
        }
        for (offset, relocation) in section.relocations() {
            let target = match relocation.target() {
                RelocationTarget::Symbol(it) => {
                    let it = object.symbol_by_index(it).ok()?;
                    let whole = it.kind() == SymbolKind::Section;
                    it.section_index().map(|section| match whole {
                        true => (section, WHOLE),
                        false => piece(section, it.address()),
                    })
                }
                RelocationTarget::Section(it) => Some((it, WHOLE)),
                _ => None,
            };
            let by = piece(section.index(), section.address() + offset);
            if let Some(target) = target.filter(|it| *it != by && *it != (by.0, WHOLE)) {
                referrers.entry(target).or_default().insert(by);
            }
        }
    }
    // SHF_GNU_RETAIN.
    const RETAIN: u64 = 0x20_0000;
    let mut seen = FxHashSet::from_iter([start]);
    let mut todo = vec![start];
    let mut reached = Vec::new();
    while let Some(at) = todo.pop() {
        let section = object.section_by_index(at.0).ok()?;
        let kept =
            matches!(section.flags(), SectionFlags::Elf { sh_flags } if sh_flags & RETAIN != 0);
        let used = matches!(
            section.kind(),
            SectionKind::Text
                | SectionKind::Data
                | SectionKind::ReadOnlyData
                | SectionKind::ReadOnlyDataWithRel
                | SectionKind::ReadOnlyString
                | SectionKind::UninitializedData
                | SectionKind::Tls
                | SectionKind::UninitializedTls
        );
        let name = section.name().unwrap_or_default();
        // Constructors run whether or not anything calls them.
        let run = [".init_array", ".fini_array", ".ctors", ".dtors", "__mod_init_func", ".CRT$"]
            .iter()
            .any(|it| name.starts_with(it));
        if kept || run || !used {
            return None;
        }
        reached.extend(defined.get(&at).into_iter().flatten().cloned());
        let by = [at, (at.0, WHOLE)].into_iter().flat_map(|it| referrers.get(&it)).flatten();
        for &by in by {
            if seen.insert(by) {
                todo.push(by);
            }
        }
    }
    Some(reached)
}

/// The name of the function a demangled symbol is an instance of: the last of its path that
/// is not types or a closure.
fn function_name(path: &str) -> Option<String> {
    let mut depth = 0usize;
    let mut bare = String::new();
    for c in path.replace("->", "").chars() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.checked_sub(1)?,
            _ if depth == 0 => bare.push(c),
            _ => {}
        }
    }
    let name = bare.rsplit("::").find(|it| !it.is_empty() && !it.starts_with('{'))?;
    Some(name.to_owned())
}

/// The name of the crate in `libname-hash.rlib`, or in the `name-hash.<unit>.rcgu.o` of a crate
/// built as a program, and the files of its source, which the dep-info file cargo leaves
/// next to it lists, the one the crate starts at first.
fn crate_sources(rlib: &Path, root: &Path) -> Option<(String, Vec<PathBuf>)> {
    let file = rlib.file_name()?.to_str()?;
    let stem = match file.strip_suffix(".rlib") {
        Some(stem) => stem.strip_prefix("lib")?,
        None => file.strip_suffix(".rcgu.o")?.split_once('.')?.0,
    };
    // A crate's name has no `-`. cargo gives the program of an MSVC or Apple target no hash:
    // the file of its symbols is named after it.
    let name = stem.rsplit_once('-').map_or(stem, |(name, _)| name);
    let dep_info = std::fs::read_to_string(rlib.with_file_name(format!("{stem}.d"))).ok()?;
    let (_, sources) = dep_info.lines().next()?.split_once(": ")?;
    // FIXME: a path with a space in it is escaped.
    let sources: Vec<PathBuf> = sources.split(' ').map(|it| root.join(it)).collect();
    (!sources.is_empty()).then(|| (name.to_owned(), sources))
}

/// A v0 symbol without the crate that instantiated it, which ends the symbol of a generic
/// instance as `Cs<id>_<len><name>` or as a back reference `B<offset>_`. Copies of one instance
/// made by two crates differ only in that.
fn without_instantiating_crate(symbol: &str) -> &str {
    let is_base62 = |c: char| c.is_ascii_alphanumeric();
    if let Some(body) = symbol.strip_suffix('_')
        && let Some(start) = body.rfind('B')
        && body[start + 1..].chars().all(is_base62)
    {
        return &symbol[..start];
    }
    // `Cs<id>_<len><name>`: the name is the last `len` bytes.
    let Some(crate_start) = symbol.rfind("Cs") else { return symbol };
    let Some((id, ident)) = symbol[crate_start + 2..].split_once('_') else { return symbol };
    let digits = ident.chars().take_while(char::is_ascii_digit).count();
    let named = ident[..digits].parse() == Ok(ident.len() - digits);
    if id.chars().all(is_base62) && named { &symbol[..crate_start] } else { symbol }
}

/// The `name[id]` a demangled v0 symbol prints for each crate in it.
fn crate_ids(demangled: &str) -> impl Iterator<Item = (&str, u64)> {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_';
    let mut rest = demangled;
    std::iter::from_fn(move || {
        loop {
            let (before, after) = rest.split_once('[')?;
            rest = after;
            let Some((id, _)) = after.split_once(']') else { continue };
            let name_len = before.chars().rev().take_while(|&c| is_ident(c)).count();
            let name = &before[before.len() - name_len..];
            let Ok(id) = u64::from_str_radix(id, 16) else { continue };
            if !name.is_empty() {
                return Some((name, id));
            }
        }
    })
}

/// The demangled symbol without the ids of the crates `drop` picks.
fn without_ids(demangled: &str, drop: impl Fn(&str) -> bool) -> String {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_';
    let mut path = String::with_capacity(demangled.len());
    let mut rest = demangled;
    while let Some(open) = rest.find('[') {
        let (before, after) = rest.split_at(open);
        path.push_str(before);
        let name_len = before.chars().rev().take_while(|&c| is_ident(c)).count();
        let name = &before[before.len() - name_len..];
        match after.find(']') {
            Some(close)
                if !name.is_empty() && u64::from_str_radix(&after[1..close], 16).is_ok() =>
            {
                if !drop(name) {
                    path.push_str(&after[..=close]);
                }
                rest = &after[close + 1..];
            }
            _ => {
                path.push('[');
                rest = &after[1..];
            }
        }
    }
    path.push_str(rest);
    path
}

/// A reader of v0 symbols, for what `rustc_demangle` reads and does not print.
struct V0<'a> {
    rest: &'a [u8],
}

impl V0<'_> {
    /// The disambiguator of the last name in the path of a symbol: `0` for the first item of
    /// that name in what it is written in, `1` for the next.
    fn place(symbol: &str) -> Option<u64> {
        V0 { rest: symbol.strip_prefix("_R")?.as_bytes() }.path()
    }

    /// The `StableCrateId` of the crate that compiled a copy of an instance, which ends the
    /// symbol: see [`without_instantiating_crate`].
    fn instantiating_crate(symbol: &str) -> Option<u64> {
        let at = without_instantiating_crate(symbol).len();
        let mut reader = V0 { rest: symbol.as_bytes().get(at..)? };
        if reader.eat(b'B') {
            let to = usize::try_from(reader.base62()?).ok()?;
            reader = V0 { rest: symbol.strip_prefix("_R")?.as_bytes().get(to..)? };
        }
        reader.eat(b'C').then(|| reader.disambiguator())?
    }

    /// The disambiguators of the names in the path of a symbol before the last, outermost
    /// first: those of what an item is written in. A closure has no name.
    fn places_around(symbol: &str) -> Option<Vec<u64>> {
        let mut symbol = V0 { rest: symbol.strip_prefix("_R")?.as_bytes() };
        let mut namespaces = Vec::new();
        while symbol.eat(b'N') {
            namespaces.push(symbol.next()?);
        }
        symbol.path()?;
        let mut places = Vec::new();
        for namespace in namespaces.into_iter().rev() {
            let place = symbol.disambiguator()?;
            symbol.identifier()?;
            if namespace.is_ascii_lowercase() {
                places.push(place);
            }
        }
        places.pop();
        Some(places)
    }

    fn next(&mut self) -> Option<u8> {
        let (&first, rest) = self.rest.split_first()?;
        self.rest = rest;
        Some(first)
    }

    fn eat(&mut self, byte: u8) -> bool {
        let found = self.rest.first() == Some(&byte);
        if found {
            self.rest = &self.rest[1..];
        }
        found
    }

    fn base62(&mut self) -> Option<u64> {
        if self.eat(b'_') {
            return Some(0);
        }
        let mut value = 0u64;
        loop {
            let digit = match self.next()? {
                b'_' => return value.checked_add(1),
                byte @ b'0'..=b'9' => byte - b'0',
                byte @ b'a'..=b'z' => byte - b'a' + 10,
                byte @ b'A'..=b'Z' => byte - b'A' + 36,
                _ => return None,
            };
            value = value.checked_mul(62)?.checked_add(digit.into())?;
        }
    }

    fn disambiguator(&mut self) -> Option<u64> {
        if self.eat(b's') { self.base62()?.checked_add(1) } else { Some(0) }
    }

    fn identifier(&mut self) -> Option<()> {
        self.eat(b'u');
        // A length of zero is one `0`: the digits after it start the next name.
        let digits = match self.rest.first()? {
            b'0' => 1,
            _ => self.rest.iter().take_while(|it| it.is_ascii_digit()).count(),
        };
        let len: usize = str::from_utf8(&self.rest[..digits]).ok()?.parse().ok()?;
        self.rest = &self.rest[digits..];
        self.eat(b'_');
        self.rest = self.rest.get(len..)?;
        Some(())
    }

    /// Reads a path, for the disambiguator of the name it ends in.
    fn path(&mut self) -> Option<u64> {
        match self.next()? {
            b'C' => {
                self.disambiguator()?;
                self.identifier()?;
                Some(0)
            }
            b'M' => {
                self.disambiguator()?;
                self.path()?;
                self.ty()?;
                Some(0)
            }
            b'X' => {
                self.disambiguator()?;
                self.path()?;
                self.ty()?;
                self.path()?;
                Some(0)
            }
            b'Y' => {
                self.ty()?;
                self.path()?;
                Some(0)
            }
            b'N' => {
                self.next()?;
                self.path()?;
                let place = self.disambiguator()?;
                self.identifier()?;
                Some(place)
            }
            b'I' => {
                let place = self.path()?;
                while !self.eat(b'E') {
                    match self.rest.first()? {
                        b'L' => {
                            self.next();
                            self.base62()?;
                        }
                        b'K' => {
                            self.next();
                            self.constant()?;
                        }
                        _ => self.ty()?,
                    }
                }
                Some(place)
            }
            b'B' => {
                self.base62()?;
                Some(0)
            }
            _ => None,
        }
    }

    fn binder(&mut self) -> Option<()> {
        if self.eat(b'G') {
            self.base62()?;
        }
        Some(())
    }

    fn ty(&mut self) -> Option<()> {
        match *self.rest.first()? {
            b'C' | b'M' | b'X' | b'Y' | b'N' | b'I' | b'B' => return self.path().map(drop),
            _ => {}
        }
        match self.next()? {
            b'A' => {
                self.ty()?;
                self.constant()?;
            }
            b'S' | b'P' | b'O' => self.ty()?,
            b'T' => {
                while !self.eat(b'E') {
                    self.ty()?;
                }
            }
            b'R' | b'Q' => {
                if self.eat(b'L') {
                    self.base62()?;
                }
                self.ty()?;
            }
            b'F' => {
                self.binder()?;
                self.eat(b'U');
                if self.eat(b'K') && !self.eat(b'C') {
                    self.identifier()?;
                }
                while !self.eat(b'E') {
                    self.ty()?;
                }
                self.ty()?;
            }
            b'D' => {
                self.binder()?;
                while !self.eat(b'E') {
                    self.path()?;
                    while self.eat(b'p') {
                        self.identifier()?;
                        self.ty()?;
                    }
                }
                if !self.eat(b'L') {
                    return None;
                }
                self.base62()?;
            }
            // A basic type is one lowercase letter.
            byte if byte.is_ascii_lowercase() => {}
            _ => return None,
        }
        Some(())
    }

    // FIXME: the constants of `adt_const_params` are not read.
    fn constant(&mut self) -> Option<()> {
        if self.eat(b'p') {
            return Some(());
        }
        if self.eat(b'B') {
            return self.base62().map(drop);
        }
        self.ty()?;
        while self.next()? != b'_' {}
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use rustc_hash::FxHashMap;

    use super::{SymbolTable, V0, function_name};

    fn placed(crates: &[(&str, &[(u64, usize)])]) -> Vec<(String, u64)> {
        let mut table = SymbolTable::default();
        let unplaced: FxHashMap<_, _> = crates
            .iter()
            .map(|(root, mentions)| {
                ((PathBuf::from(root), false), mentions.iter().copied().collect())
            })
            .collect();
        table.place(unplaced);
        let mut placed: Vec<_> =
            table.by_root.iter().map(|(root, id)| (root.0.display().to_string(), *id)).collect();
        placed.sort();
        placed
    }

    #[test]
    fn the_crate_that_compiled_a_copy() {
        let of_lib = "_RINvCslFwujm09uXn_4kdep3sumhECsjPNOOTmEH7l_4klib";
        let of_app = "_RINvCslFwujm09uXn_4kdep3sumhECsjSK0TBt3L2V_4kapp";
        let by_reference = "_RNvXs_NtNtCsevLNFiNqfJP_4core3ops5arithhNtB4_3Add3addB8_";
        let table = SymbolTable::of_names([of_lib, of_app, by_reference]);
        let copies: Vec<_> = table.copies(of_app).map(|it| it.0).collect();
        assert_eq!(copies, [of_lib, of_app]);
        let ids: Vec<_> = table.copies(of_lib).map(|it| it.1).collect();
        assert_ne!(ids[0], ids[1]);
        assert_eq!(table.crates["core"], table.copies(by_reference).next().map(|it| it.1));
        assert_eq!(table.copies("_RNvCslFwujm09uXn_4kdep5small").count(), 0);
        assert_eq!(table.makers("sum").count(), 2);
    }

    #[test]
    fn a_binary_that_mentions_its_library_more_than_itself() {
        let placed = placed(&[("src/lib.rs", &[(1, 5)]), ("src/main.rs", &[(1, 9), (2, 3)])]);
        assert_eq!(placed, [("src/lib.rs".to_owned(), 1), ("src/main.rs".to_owned(), 2)]);
    }

    #[test]
    fn a_test_named_as_a_crate_of_the_sysroot() {
        let placed = placed(&[("tests/test.rs", &[(7, 6), (8, 300)])]);
        assert_eq!(placed, [("tests/test.rs".to_owned(), 8)]);
    }

    #[test]
    fn place_of_a_static_in_a_closure() {
        let in_function = "_RNvNvMNtCs7aCYEL8njSF_2h24sendNtB4_4Send5apply10___CALLSITE";
        let first = "_RNvNCNvMNtCs7aCYEL8njSF_2h24sendNtB6_4Send5apply010___CALLSITE";
        let second = "_RNvNCNvMNtCs7aCYEL8njSF_2h24sendNtB6_4Send5apply0s_10___CALLSITE";
        let third = "_RNvNCNvMNtCs7aCYEL8njSF_2h24sendNtB6_4Send5apply0s0_10___CALLSITE";
        assert_eq!(V0::place(in_function), Some(0));
        assert_eq!(V0::place(first), Some(0));
        assert_eq!(V0::place(second), Some(1));
        assert_eq!(V0::place(third), Some(2));
        let inner = "_RNvNvNCNCNvCs3XX9e4g8R7s_8filtereds_14trace_filtered00s_10___CALLSITE4META";
        assert_eq!(V0::place(inner), Some(0));
        assert_eq!(V0::places_around(inner), Some(vec![1, 1]));
        assert_eq!(V0::places_around(third), Some(vec![0]));
    }

    #[test]
    fn the_function_a_symbol_is_an_instance_of() {
        let name = |path| function_name(path).unwrap();
        assert_eq!(
            name("std::panic::catch_unwind::<&dyn core::ops::Fn<(), Output = u8>, u8>"),
            "catch_unwind"
        );
        assert_eq!(name("<core::fmt::Arguments>::new::<5, 2>"), "new");
        assert_eq!(name("<alloc::boxed::Box<fn(u8) -> u8> as core::ops::Drop>::drop"), "drop");
        assert_eq!(name("kdep::each::<u8, klib::run::{closure#0}>::{closure#1}"), "each");
    }
}
