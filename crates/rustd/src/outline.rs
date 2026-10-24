//! Telling an edit to the bodies of functions from one the rest of the program can see.
//!
//! Most edits change what a function does and nothing else. What was compiled from other
//! bodies is then as it was, and only what comes from the edited file needs another look. That
//! holds for a body nothing else sees into: not that of a `const fn`, which other items are
//! evaluated with, nor one whose type is part of its signature (`async fn`, `-> impl Trait`),
//! nor one a macro is handed, nor one that declares items other than statics and constants.
//! Such bodies count as part of what the rest of the program sees.

use std::{
    hash::{Hash, Hasher},
    time::Instant,
};

use hir_def::{FunctionId, Lookup, ModuleDefId, expr_store::Body};
use ide_db::{
    RootDatabase,
    base_db::{EditionedFileId, relevant_crates},
};
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};
use syntax::{
    AstNode, Edition, SyntaxKind, SyntaxNode, TextRange, WalkEvent,
    ast::{self, HasAttrs},
};
use vfs::FileId;

use crate::Listed;

/// Attributes that leave the item they are on as it is written.
const INERT: &[&str] = &[
    "allow",
    "cfg",
    "cold",
    "deny",
    "deprecated",
    "doc",
    "expect",
    "forbid",
    "inline",
    "must_use",
    "track_caller",
    "warn",
];

/// Each file as it was when last looked at.
#[derive(Default)]
pub(crate) struct Outlines {
    files: FxHashMap<FileId, Option<Outline>>,
}

#[derive(Clone)]
struct Outline {
    outside: u64,
    functions: Option<FxHashMap<FunctionId, (u64, u32, u32)>>,
}

pub(crate) struct ChangedFunctions {
    pub(crate) code: Vec<FunctionId>,
    pub(crate) locations: Vec<FunctionId>,
}

fn function_changes<K: Copy + Eq + Hash>(
    was: &FxHashMap<K, (u64, u32, u32)>,
    now: &FxHashMap<K, (u64, u32, u32)>,
) -> Option<(Vec<K>, Vec<K>)> {
    if now.len() != was.len() || now.keys().any(|id| !was.contains_key(id)) {
        return None;
    }
    let mut code = Vec::new();
    let mut locations = Vec::new();
    for (id, source) in now {
        let old = was[id];
        if old.0 != source.0 {
            code.push(*id);
        }
        if (old.1, old.2) != (source.1, source.2) {
            locations.push(*id);
        }
    }
    Some((code, locations))
}

impl Outlines {
    /// Takes note of the files that are about to change, unless they are known already.
    pub(crate) fn before_edit(&mut self, db: &RootDatabase, listed: &Listed, files: &[FileId]) {
        let new: Vec<_> = files.iter().copied().filter(|it| !self.files.contains_key(it)).collect();
        let outlines = outlines(db, listed, &new);
        self.files.extend(new.into_iter().zip(outlines));
    }

    /// For each file of the edit that was just applied, whether nothing changed in it but
    /// bodies that nothing else sees into. Asked after [`Outlines::before_edit`].
    pub(crate) fn after_edit(
        &mut self,
        db: &RootDatabase,
        listed: &Listed,
        files: Vec<FileId>,
    ) -> Vec<(FileId, bool, Option<ChangedFunctions>)> {
        let off = std::env::var_os("RUSTD_NO_BODIES").is_some();
        let outlines = outlines(db, listed, &files);
        let files: Vec<_> = files
            .into_iter()
            .zip(outlines)
            .map(|(file, now)| {
                let was = self.files.remove(&file).flatten();
                let bodies_only = !off
                    && now
                        .as_ref()
                        .zip(was.as_ref())
                        .is_some_and(|(now, was)| now.outside == was.outside);
                let functions = bodies_only
                    .then(|| {
                        let now = now.as_ref()?.functions.as_ref()?;
                        let was = was.as_ref()?.functions.as_ref()?;
                        let (code, locations) = function_changes(was, now)?;
                        Some(ChangedFunctions { code, locations })
                    })
                    .flatten();
                self.files.insert(file, now);
                (file, bodies_only, functions)
            })
            .collect();
        // An edit to more than bodies can change which functions there are, in any file, and
        // what is kept here was found by asking the ones listed before it.
        if files.iter().any(|(_, bodies_only, _)| !bodies_only) {
            self.files.clear();
        }
        files
    }
}

/// The [`outline`] of each file. A wide edit is of thousands of files: their bodies are
/// lowered together and the files are hashed on all threads.
fn outlines(db: &RootDatabase, listed: &Listed, files: &[FileId]) -> Vec<Option<Outline>> {
    let start = Instant::now();
    let stats = std::env::var_os("RUSTD_STATS").is_some();
    if files.len() > 1 {
        let mut crates: Vec<_> =
            files.iter().flat_map(|&file| relevant_crates(db, file).iter().copied()).collect();
        crates.sort_unstable();
        crates.dedup();
        crate::resolve_names(db, &crates);
    }
    let functions = listed.in_files(db, files);
    let bodies = functions.iter().flatten().flatten().map(|&it| it.into()).collect();
    let functions_time = start.elapsed();
    crate::lower(db, bodies);
    let lowered = start.elapsed();
    let threads = std::thread::available_parallelism().map_or(1, |it| it.get());
    let mut outlines = vec![None; files.len()];
    std::thread::scope(|scope| {
        let parts: Vec<_> = (0..threads.min(files.len()))
            .map(|part| {
                let (db, functions) = (db.clone(), &functions);
                scope.spawn(move || {
                    hir::attach_db(&db, || {
                        let files = files.iter().zip(functions).enumerate();
                        files
                            .skip(part)
                            .step_by(threads)
                            .map(|(at, (&file, functions))| {
                                let Some(functions) = functions else {
                                    if stats {
                                        eprintln!(
                                            "outline: {file:?} has functions that are not listed"
                                        );
                                    }
                                    return (at, None);
                                };
                                (at, outline(&db, file, functions))
                            })
                            .collect::<Vec<_>>()
                    })
                })
            })
            .collect();
        for (at, outline) in parts.into_iter().flat_map(|it| it.join().unwrap_or_default()) {
            outlines[at] = outline;
        }
    });
    if stats {
        eprintln!(
            "outlines-us: functions={} lower={} hash={}; files={}",
            functions_time.as_micros(),
            (lowered - functions_time).as_micros(),
            (start.elapsed() - lowered).as_micros(),
            files.len(),
        );
    }
    outlines
}

/// A hash of everything in the file but the bodies nothing else sees into, or `None` when
/// the file is not read as a file of its own. `functions` are those written in it.
fn outline(db: &RootDatabase, file: FileId, functions: &[FunctionId]) -> Option<Outline> {
    let Some(seen) = Written::of(db, functions) else {
        if std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!("outline: {file:?} is included in another file");
        }
        return None;
    };
    // As the crate reads it, so that the file is parsed once for both.
    let edition =
        relevant_crates(db, file).first().map_or(Edition::CURRENT, |it| it.data(db).edition);
    let tree = EditionedFileId::new(db, file, edition).parse(db).syntax_node();
    let (hash, found) = hash_outside_bodies(&tree, &seen.declaring);
    // Each of them has to be one of the bodies that were kept in.
    if found != seen.declaring.len() {
        return None;
    }
    let text = tree.text().to_string();
    let lines = ide_db::line_index(db, file);
    let functions = functions
        .iter()
        .map(|&func| {
            let at = func.lookup(db).id;
            if at.file_id.original_file(db).file_id(db) != file {
                return None;
            }
            let mut hash = FxHasher::default();
            let range = if at.file_id.is_macro() {
                at.to_node(db).syntax().text().to_string().hash(&mut hash);
                let call = at.file_id.original_call_node(db)?;
                if call.file_id.file_id(db) != file {
                    return None;
                }
                call.value
                    .ancestors()
                    .find_map(ast::Item::cast)?
                    .syntax()
                    .text()
                    .to_string()
                    .hash(&mut hash);
                call.value.text_range()
            } else {
                let range = at.to_range(db);
                text.get(std::ops::Range::<usize>::from(range))?.hash(&mut hash);
                range
            };
            let start = lines.try_line_col(range.start())?;
            Some((func, (hash.finish(), start.line, start.col)))
        })
        .collect();
    Some(Outline { outside: hash, functions })
}

/// What looking at the functions written in a file tells that how they are written does not.
struct Written {
    /// Where the functions are whose bodies declare items.
    declaring: FxHashSet<TextRange>,
}

impl Written {
    /// `None` when the functions are in a file that `include!` reads: those are written by a
    /// macro as far as we can tell.
    fn of(db: &RootDatabase, functions: &[FunctionId]) -> Option<Written> {
        let mut declaring = FxHashSet::default();
        for &func in functions {
            let at = func.lookup(db).id;
            if at.file_id.is_macro() {
                let included = at.file_id.original_file_respecting_includes(db)
                    != at.file_id.original_file(db);
                if included {
                    return None;
                }
                // What a macro wrote comes from what it was handed, which is no body that
                // is left out.
                continue;
            }
            if declares_items(db, func) {
                declaring.insert(at.to_range(db));
            }
        }
        Some(Written { declaring })
    }
}

fn declares_items(db: &RootDatabase, func: FunctionId) -> bool {
    Body::of(db, func.into()).blocks(db).any(|(_, def_map)| {
        def_map.modules(db).any(|(_, module)| {
            let scope = module.scope(db);
            // A static or constant is the body's own: only its code names it, and neither is
            // a function to list. Macros that log declare them.
            scope
                .declarations()
                .any(|it| !matches!(it, ModuleDefId::StaticId(_) | ModuleDefId::ConstId(_)))
                || scope.impls().len() != 0
                || scope.unnamed_consts().next().is_some()
        })
    })
}

/// The hash, and how many of the `declaring` functions were come by.
fn hash_outside_bodies(file: &SyntaxNode, declaring: &FxHashSet<TextRange>) -> (u64, usize) {
    let mut hasher = FxHasher::default();
    let mut found = 0;
    let mut walk = file.preorder_with_tokens();
    while let Some(event) = walk.next() {
        match event {
            WalkEvent::Enter(syntax::NodeOrToken::Node(node)) => {
                node.kind().hash(&mut hasher);
                if node.kind() == SyntaxKind::FN && declaring.contains(&node.text_range()) {
                    found += 1;
                } else if is_unseen_body(&node)
                    && node.parent().is_none_or(|it| !declaring.contains(&it.text_range()))
                {
                    walk.skip_subtree();
                }
            }
            WalkEvent::Enter(syntax::NodeOrToken::Token(token)) => {
                // Blank space and comments say nothing, except to a macro that is handed them.
                // A doc comment is a token of another kind.
                let blank = matches!(token.kind(), SyntaxKind::WHITESPACE | SyntaxKind::COMMENT)
                    && token.parent().is_none_or(|it| it.kind() != SyntaxKind::TOKEN_TREE);
                if !blank {
                    token.kind().hash(&mut hasher);
                    token.text().hash(&mut hasher);
                }
            }
            WalkEvent::Leave(_) => {}
        }
    }
    (hasher.finish(), found)
}

/// Whether the node is the body of a function that nothing else sees into, going by how the
/// function is written. What its body declares takes name resolution to tell.
fn is_unseen_body(node: &SyntaxNode) -> bool {
    if node.kind() != SyntaxKind::BLOCK_EXPR {
        return false;
    }
    let Some(func) = node.parent().and_then(ast::Fn::cast) else { return false };
    if func.const_token().is_some() || func.async_token().is_some() || func.gen_token().is_some() {
        return false;
    }
    let names_its_type = func.ret_type().is_some_and(|it| {
        it.syntax().descendants().any(|it| it.kind() == SyntaxKind::IMPL_TRAIT_TYPE)
    });
    if names_its_type || !is_inert(func.syntax()) {
        return false;
    }
    // rustc copies the body into the callers, also the ones it compiled for us.
    let always_inlined = func.attrs().any(|attr| {
        attr.simple_name().is_some_and(|name| name == "inline")
            && attr.syntax().text().to_string().contains("always")
    });
    if always_inlined {
        return false;
    }
    // An attribute written inside the body is the function's, and a macro declared in it can
    // be exported from the crate.
    let reaches_out = node.descendants().any(|it| match it.kind() {
        SyntaxKind::ATTR => it.ancestors().nth(2).is_some_and(|block| block == *node),
        SyntaxKind::MACRO_RULES | SyntaxKind::MACRO_DEF => true,
        _ => false,
    });
    if reaches_out {
        return false;
    }
    // Only items, all the way up: a function in a body is that body's, and one in a macro's
    // input is the macro's.
    func.syntax().ancestors().skip(1).all(|it| match it.kind() {
        SyntaxKind::SOURCE_FILE | SyntaxKind::ITEM_LIST | SyntaxKind::ASSOC_ITEM_LIST => true,
        SyntaxKind::MODULE | SyntaxKind::IMPL | SyntaxKind::TRAIT => is_inert(&it),
        _ => false,
    })
}

/// Whether no attribute on the item can be a macro that rewrites it.
fn is_inert(item: &SyntaxNode) -> bool {
    let Some(item) = ast::AnyHasAttrs::cast(item.clone()) else { return false };
    item.attrs().all(|attr| attr.simple_name().is_some_and(|name| INERT.contains(&name.as_str())))
}

/// The crate the file is a module of, when that is one of `used`, which the crates in `built`
/// depend on, and none of `built`: rustc compiled it, and what it compiled is all there is of
/// it.
pub(crate) fn left_to_rustc(
    db: &RootDatabase,
    built: &[ide_db::base_db::Crate],
    used: &FxHashSet<ide_db::base_db::Crate>,
    file: FileId,
) -> Option<ide_db::base_db::Crate> {
    let crates = relevant_crates(db, file);
    if crates.iter().any(|it| built.contains(it)) {
        return None;
    }
    crates.iter().copied().find(|&krate| {
        used.contains(&krate)
            && hir_def::nameres::crate_def_map(db, krate)
                .modules_for_file(db, file)
                .next()
                .is_some()
    })
}

impl Listed {
    /// Whether the file is a module of a crate that is built, or of one that such a crate uses.
    /// Any file may be one before a crate is listed.
    pub(crate) fn sees(&self, db: &RootDatabase, file: FileId) -> bool {
        // Copied out: a query that is cancelled unwinds, and would poison the lock.
        let built = crate::lock(&self.built).clone();
        // Before the first build there is no telling.
        built.is_empty()
            || relevant_crates(db, file).iter().any(|&krate| {
                let read = built.iter().any(|&built| {
                    let built = ide_db::base_db::Crate::from(built);
                    built == krate || built.transitive_deps(db).contains(&krate)
                });
                read && hir_def::nameres::crate_def_map(db, krate)
                    .modules_for_file(db, file)
                    .next()
                    .is_some()
            })
    }

    /// For each file the functions written in it that no body declares, as the file is now,
    /// or `None` when it belongs to a crate that is not listed: one that the crates being
    /// built use and that is not one of them.
    pub(crate) fn in_files(
        &self,
        db: &RootDatabase,
        files: &[FileId],
    ) -> Vec<Option<Vec<FunctionId>>> {
        type Crate = ide_db::base_db::Crate;
        let listed: Vec<Crate> =
            self.functions.lock().unwrap().keys().map(|&it| it.into()).collect();
        // The functions of a listed crate by the file they are in, and `None` for a crate
        // that the listed ones use.
        let mut crates: FxHashMap<Crate, Option<FxHashMap<FileId, Vec<FunctionId>>>> =
            FxHashMap::default();
        let mut used = None;
        files
            .iter()
            .map(|&file| {
                let mut functions = Vec::new();
                for &krate in relevant_crates(db, file).iter() {
                    let of_crate = crates.entry(krate).or_insert_with(|| {
                        if !listed.contains(&krate) {
                            return None;
                        }
                        let mut by_file: FxHashMap<_, Vec<_>> = FxHashMap::default();
                        for func in crate::functions_of_modules(db, krate.into()) {
                            let file = hir_ty::mir::codegen::body_file(db, func.into());
                            by_file.entry(file).or_default().push(func);
                        }
                        Some(by_file)
                    });
                    match of_crate {
                        Some(by_file) => {
                            functions.extend(by_file.get(&file).into_iter().flatten().copied())
                        }
                        None => {
                            let used = used.get_or_insert_with(|| {
                                let used = listed.iter().flat_map(|it| it.transitive_deps(db));
                                used.collect::<FxHashSet<Crate>>()
                            });
                            if used.contains(&krate) {
                                return None;
                            }
                        }
                    }
                }
                Some(functions)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syntax::SourceFile;

    #[test]
    fn changed_function_sources() {
        let was = FxHashMap::from_iter([(1, (10, 0, 0)), (2, (20, 1, 0))]);
        let now = FxHashMap::from_iter([(1, (11, 0, 0)), (2, (20, 2, 0))]);
        assert_eq!(function_changes(&was, &now), Some((vec![1], vec![2])));
        assert_eq!(function_changes(&was, &was), Some((vec![], vec![])));
        assert_eq!(
            function_changes::<u32>(&FxHashMap::default(), &FxHashMap::default()),
            Some((vec![], vec![]))
        );
        assert_eq!(function_changes(&was, &FxHashMap::from_iter([(1, (10, 0, 0))])), None);
        assert_eq!(
            function_changes(&was, &FxHashMap::from_iter([(1, (10, 0, 0)), (3, (20, 1, 0))])),
            None
        );
        let now = FxHashMap::from_iter([(1, (10, 0, 1)), (2, (20, 1, 0))]);
        assert_eq!(function_changes(&was, &now), Some((vec![], vec![1])));
    }

    fn hash(text: &str) -> u64 {
        let tree = SourceFile::parse(text, Edition::CURRENT).syntax_node();
        hash_outside_bodies(&tree, &FxHashSet::default()).0
    }

    #[track_caller]
    fn unseen(before: &str, after: &str) {
        assert_eq!(hash(before), hash(after), "{before:?} to {after:?} is seen");
    }

    #[track_caller]
    fn seen(before: &str, after: &str) {
        assert_ne!(hash(before), hash(after), "{before:?} to {after:?} is not seen");
    }

    #[test]
    fn bodies_are_left_out() {
        unseen("fn f() { 1; }", "fn f() { 2; }");
        unseen("impl S { fn f(&self) -> u8 { 1 } }", "impl S { fn f(&self) -> u8 { 2 } }");
        unseen("trait T { fn f(&self) -> u8 { 1 } }", "trait T { fn f(&self) -> u8 { 2 } }");
        unseen("mod m { pub fn f() { a() } }", "mod m { pub fn f() { b() } }");
        unseen("fn f() { #[allow(unused)] let a = 1; }", "fn f() { #[allow(unused)] let a = 2; }");
        unseen("/// Doc.\n#[inline]\nfn f() { 1; }", "/// Doc.\n#[inline]\nfn f() { 2; }");
    }

    #[test]
    fn blank_space_and_comments_are_left_out() {
        unseen("fn f() {}", "\n\nfn f() {}\n");
        unseen("fn f() {}", "fn f() {}\n// edit\n");
        unseen("struct S;", "/* note */ struct S;");
    }

    #[test]
    fn what_others_see_is_kept() {
        seen("fn f() {}", "fn g() {}");
        seen("fn f() {}", "fn f() {} fn g() {}");
        seen("fn f() -> u8 { 1 }", "fn f() -> u16 { 1 }");
        seen("struct S(u8);", "struct S(u16);");
        seen("/// One.\nfn f() {}", "/// Two.\nfn f() {}");
        seen("const C: u8 = 1;", "const C: u8 = 2;");
        seen("static S: u8 = { 1 };", "static S: u8 = { 2 };");
    }

    #[test]
    fn bodies_others_see_into_are_kept() {
        seen("const fn f() -> u8 { 1 }", "const fn f() -> u8 { 2 }");
        seen("async fn f() -> u8 { 1 }", "async fn f() -> u8 { 2 }");
        seen("fn f() -> impl Sized { 1u8 }", "fn f() -> impl Sized { 1u16 }");
        seen("fn f() -> Box<impl Sized> { a() }", "fn f() -> Box<impl Sized> { b() }");
        seen("#[test]\nfn f() { 1; }", "#[test]\nfn f() { 2; }");
        seen("#[inline(always)]\nfn f() { 1; }", "#[inline(always)]\nfn f() { 2; }");
        seen("#[tokio::main]\nfn f() { 1; }", "#[tokio::main]\nfn f() { 2; }");
        seen("#[imp]\nimpl S { fn f() { 1; } }", "#[imp]\nimpl S { fn f() { 2; } }");
        seen("fn f() { #![attr] 1; }", "fn f() { #![attr] 2; }");
        seen(
            "fn f() { macro_rules! m { () => { 1 } } }",
            "fn f() { macro_rules! m { () => { 2 } } }",
        );
    }

    #[test]
    fn what_a_macro_is_handed_is_kept() {
        seen("m! { fn f() { 1; } }", "m! { fn f() { 2; } }");
        seen("m! { a b }", "m! { a  b }");
        seen("m! { a }", "m! { a /* note */ }");
        seen("fn f() { fn g() { 1; } }", "fn f() { fn g() { 1; } } fn h() {}");
    }

    #[test]
    fn a_body_that_declares_items_is_kept() {
        let text = |n: u8| format!("fn f() {{ fn g() -> u8 {{ {n} }} }}");
        let hash = |text: &str| {
            let tree = SourceFile::parse(text, Edition::CURRENT).syntax_node();
            let declaring = tree.descendants().find(|it| it.kind() == SyntaxKind::FN).unwrap();
            hash_outside_bodies(&tree, &FxHashSet::from_iter([declaring.text_range()]))
        };
        let (one, found) = hash(&text(1));
        assert_eq!(found, 1);
        assert_ne!(one, hash(&text(2)).0);
    }
}
