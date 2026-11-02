//! Rustd-owned, explicitly refreshed impl indexes.

use std::{
    sync::Mutex,
    time::{Duration, Instant},
};

use base_db::{Crate, EditionedFileId, FileId};
use hir_def::{DefWithBodyId, Lookup, item_tree::file_item_tree_snapshot, src::HasSource};
use rustc_hash::{FxHashMap, FxHashSet};
use salsa::{Durability, SalsaValue, Setter};
use span::Edition;
use syntax::{AstNode, SourceFile, SyntaxKind, SyntaxNode, TextRange, TextSize, ast};
use triomphe::Arc;

use super::{InherentImpls, TraitImpls};
use crate::db::HirDatabase;

#[derive(Clone, Debug, PartialEq, SalsaValue)]
pub struct StoredTraitImpls(Arc<TraitImpls<'static>>);

impl StoredTraitImpls {
    fn new(value: Arc<TraitImpls<'_>>) -> Self {
        // SAFETY: TraitImpls contains only immortal Salsa IDs and owned arrays/maps,
        // never database references or GC-managed type-interner values.
        Self(unsafe { std::mem::transmute::<Arc<TraitImpls<'_>>, Arc<TraitImpls<'static>>>(value) })
    }

    pub(super) fn get<'db>(&self) -> &Arc<TraitImpls<'db>> {
        // SAFETY: only the phantom database lifetime is restored; see `new`.
        unsafe { std::mem::transmute(&self.0) }
    }
}

#[derive(Clone, Debug, PartialEq, SalsaValue)]
pub struct StoredInherentImpls(Arc<InherentImpls<'static>>);

impl StoredInherentImpls {
    fn new(value: Arc<InherentImpls<'_>>) -> Self {
        // SAFETY: InherentImpls contains only immortal Salsa IDs and owned maps/arrays,
        // never database references or GC-managed type-interner values.
        Self(unsafe {
            std::mem::transmute::<Arc<InherentImpls<'_>>, Arc<InherentImpls<'static>>>(value)
        })
    }

    pub(super) fn get<'db>(&self) -> &Arc<InherentImpls<'db>> {
        // SAFETY: only the phantom database lifetime is restored; see `new`.
        unsafe { std::mem::transmute(&self.0) }
    }
}

#[salsa::input]
pub struct Input {
    #[returns(ref)]
    pub value: Option<StoredTraitImpls>,
    #[returns(ref)]
    pub inherent: Option<StoredInherentImpls>,
}

#[derive(Clone)]
struct Part {
    traits: StoredTraitImpls,
    inherent: StoredInherentImpls,
}

#[derive(Clone)]
struct Entry {
    input: Input,
    parts: Vec<(Option<DefWithBodyId>, Part)>,
    owners: FxHashMap<(FileId, ItemPath), DefWithBodyId>,
}

type ItemPath = Vec<(SyntaxKind, usize)>;

struct Write {
    old: String,
    new: String,
    trees: Vec<(Crate, Option<std::sync::Arc<hir_def::item_tree::ItemTree>>)>,
}

#[derive(Default)]
struct State {
    entries: FxHashMap<Crate, Entry>,
    ready: FxHashSet<Crate>,
    inherent_ready: FxHashSet<Crate>,
    writes: FxHashMap<FileId, Write>,
    medium: Option<salsa::Revision>,
    structural: bool,
    full_refreshes: usize,
    holder_refreshes: usize,
    refresh_time: Duration,
}

#[derive(Default)]
pub struct Inputs {
    state: Mutex<State>,
}

impl Inputs {
    pub(super) fn ready(&self, krate: Crate) {
        self.state.lock().unwrap().ready.insert(krate);
    }

    pub(super) fn ready_inherent(&self, krate: Crate) {
        self.state.lock().unwrap().inherent_ready.insert(krate);
    }

    pub fn refresh_time(&self) -> Duration {
        self.state.lock().unwrap().refresh_time
    }

    pub fn refresh_counts(&self) -> (usize, usize) {
        let state = self.state.lock().unwrap();
        (state.full_refreshes, state.holder_refreshes)
    }

    pub fn get(&self, krate: Crate) -> Option<Input> {
        self.state.lock().unwrap().entries.get(&krate).map(|entry| entry.input)
    }

    pub fn invalidate_all(&self) {
        self.state.lock().unwrap().structural = true;
    }

    pub fn written(&self, db: &dyn HirDatabase, file: FileId, new: &str) {
        let crates: Vec<_> = self.state.lock().unwrap().entries.keys().copied().collect();
        if crates.is_empty() {
            return;
        }
        if !db.has_file_text(file) {
            self.invalidate_all();
            return;
        }
        let old = db.file_text(file).text(db).to_string();
        let trees = crates
            .into_iter()
            .map(|krate| {
                let hir_file = EditionedFileId::new(db, file, krate.data(db).edition).into();
                (krate, file_item_tree_snapshot(db, hir_file, krate))
            })
            .collect();
        let mut state = self.state.lock().unwrap();
        state.writes.entry(file).and_modify(|write| write.new = new.to_owned()).or_insert(Write {
            old,
            new: new.to_owned(),
            trees,
        });
    }

    pub fn refresh(&self, db: &mut dyn HirDatabase, crates: &[Crate], verify: bool) {
        let start = Instant::now();
        let medium = db.zalsa().last_changed_revision(Durability::MEDIUM);
        let (mut entries, ready, writes, mut full) = {
            let mut state = self.state.lock().unwrap();
            let full = state.structural || state.medium != Some(medium);
            state.structural = false;
            let ready: FxHashSet<_> =
                state.ready.intersection(&state.inherent_ready).copied().collect();
            (state.entries.clone(), ready, std::mem::take(&mut state.writes), full)
        };
        for (&krate, entry) in &entries {
            if !crates.contains(&krate) {
                entry.input.set_value(db).with_durability(Durability::MEDIUM).to(None);
                entry.input.set_inherent(db).with_durability(Durability::MEDIUM).to(None);
                full = true;
            }
        }
        entries.retain(|krate, _| crates.contains(krate));
        // Install membership before tracked consumers can read any of the new indexes.
        for &krate in crates {
            if !entries.contains_key(&krate) {
                let input = Input::builder(None, None).durability(Durability::MEDIUM).new(db);
                let entry = Entry { input, parts: Vec::new(), owners: FxHashMap::default() };
                entries.insert(krate, entry.clone());
                self.state.lock().unwrap().entries.insert(krate, entry);
            }
        }
        let mut gates = FxHashMap::default();
        for (&file, write) in &writes {
            for (&krate, _) in &entries {
                let edition = krate.data(db).edition;
                if gates
                    .entry((file, edition))
                    .or_insert_with(|| body_change(&write.old, &write.new, edition))
                    .is_none()
                {
                    full = true;
                    break;
                }
                let hir_file = EditionedFileId::new(db, file, krate.data(db).edition).into();
                if write
                    .trees
                    .iter()
                    .find(|(old_crate, _)| *old_crate == krate)
                    .map(|(_, tree)| tree)
                    != Some(&file_item_tree_snapshot(db, hir_file, krate))
                {
                    full = true;
                    break;
                }
            }
        }
        let mut full_refreshes = 0;
        let mut holder_refreshes = 0;
        for (&krate, entry) in &mut entries {
            // Cargo can still be writing generated files during the initial load.
            if !ready.contains(&krate) {
                continue;
            }
            if full || entry.parts.is_empty() {
                let live = TraitImpls::for_crate_tracked(db, krate).clone();
                let inherent_live = InherentImpls::for_crate_tracked(db, krate).clone();
                let mut parts = Vec::new();
                let assembled = TraitImpls::collect_def_map_parts(
                    db,
                    hir_def::nameres::crate_def_map(db, krate),
                    Some(&mut parts),
                );
                assert_eq!(&assembled, &*live);
                let mut inherent_parts = Vec::new();
                let inherent_assembled = InherentImpls::collect_def_map_parts(
                    db,
                    hir_def::nameres::crate_def_map(db, krate),
                    Some(&mut inherent_parts),
                );
                assert_eq!(&inherent_assembled, &*inherent_live);
                assert_eq!(parts.len(), inherent_parts.len());
                entry.parts = parts
                    .into_iter()
                    .zip(inherent_parts)
                    .map(|((owner, traits), (inherent_owner, inherent))| {
                        assert_eq!(owner, inherent_owner);
                        (
                            owner,
                            Part {
                                traits: StoredTraitImpls::new(traits),
                                inherent: StoredInherentImpls::new(inherent),
                            },
                        )
                    })
                    .collect();
                entry.owners.clear();
                for (owner, _) in &entry.parts {
                    let Some(owner) = *owner else { continue };
                    let (file, node) = match owner {
                        DefWithBodyId::VariantId(_) => continue,
                        DefWithBodyId::FunctionId(id) => {
                            let loc = id.lookup(db);
                            if loc.id.file_id.is_macro() {
                                continue;
                            }
                            let source = loc.source(db);
                            (source.file_id, source.value.syntax().clone())
                        }
                        DefWithBodyId::ConstId(id) => {
                            let loc = id.lookup(db);
                            if loc.id.file_id.is_macro() {
                                continue;
                            }
                            let source = loc.source(db);
                            (source.file_id, source.value.syntax().clone())
                        }
                        DefWithBodyId::StaticId(id) => {
                            let loc = id.lookup(db);
                            if loc.id.file_id.is_macro() {
                                continue;
                            }
                            let source = loc.source(db);
                            (source.file_id, source.value.syntax().clone())
                        }
                    };
                    entry
                        .owners
                        .insert((file.file_id().unwrap().file_id(db), item_path(&node)), owner);
                }
                full_refreshes += 1;
            } else if !writes.is_empty() {
                // The range gate pins everything outside an inert, non-macro holder body;
                // equal item trees additionally pin module scopes and the holder list.
                let changed: Vec<_> = writes
                    .iter()
                    .flat_map(|(&file, _)| {
                        let path = gates
                            .get(&(file, krate.data(db).edition))
                            .and_then(|gate| gate.as_ref().and_then(|path| path.as_ref()));
                        entry.owners.iter().filter_map(move |((owner_file, owner_path), &owner)| {
                            (file == *owner_file
                                && path.is_some_and(|path| path.ends_with(owner_path)))
                            .then_some(owner)
                        })
                    })
                    .collect();
                for (owner, part) in &mut entry.parts {
                    let Some(owner) = *owner else { continue };
                    if changed.contains(&owner) {
                        part.traits =
                            StoredTraitImpls::new(Arc::new(TraitImpls::collect_holder(db, owner)));
                        part.inherent = StoredInherentImpls::new(Arc::new(
                            InherentImpls::collect_holder(db, owner),
                        ));
                        holder_refreshes += 1;
                    }
                }
            }
            let mut map = FxHashMap::default();
            let mut inherent_map = FxHashMap::default();
            for (_, part) in &entry.parts {
                TraitImpls::append(&mut map, part.traits.get());
                InherentImpls::append(&mut inherent_map, part.inherent.get());
            }
            let value = StoredTraitImpls::new(Arc::new(TraitImpls::finish(map)));
            if entry.input.value(db).as_ref() != Some(&value) {
                entry.input.set_value(db).with_durability(Durability::MEDIUM).to(Some(value));
            }
            let inherent = StoredInherentImpls::new(Arc::new(InherentImpls::finish(inherent_map)));
            if entry.input.inherent(db).as_ref() != Some(&inherent) {
                entry.input.set_inherent(db).with_durability(Durability::MEDIUM).to(Some(inherent));
            }
        }
        if verify {
            for (&krate, entry) in &entries {
                let Some(value) = entry.input.value(db) else { continue };
                assert_eq!(&**value.get(), &**TraitImpls::for_crate_tracked(db, krate));
                let inherent = entry.input.inherent(db).as_ref().unwrap();
                assert_eq!(&**inherent.get(), &**InherentImpls::for_crate_tracked(db, krate));
            }
        }
        let mut state = self.state.lock().unwrap();
        state.entries = entries;
        state.medium = Some(db.zalsa().last_changed_revision(Durability::MEDIUM));
        state.full_refreshes += full_refreshes;
        state.holder_refreshes += holder_refreshes;
        let elapsed = start.elapsed();
        state.refresh_time += elapsed;
        if std::env::var_os("RUSTD_STATS").is_some() {
            eprintln!("impl-connector-us: {}", elapsed.as_micros());
        }
    }
}

fn body_change(old: &str, new: &str, edition: Edition) -> Option<Option<ItemPath>> {
    if old == new {
        return Some(None);
    }
    let mut prefix = old.bytes().zip(new.bytes()).take_while(|(a, b)| a == b).count();
    while !old.is_char_boundary(prefix) || !new.is_char_boundary(prefix) {
        prefix -= 1;
    }
    let mut suffix = old[prefix..]
        .bytes()
        .rev()
        .zip(new[prefix..].bytes().rev())
        .take_while(|(a, b)| a == b)
        .count();
    while !old.is_char_boundary(old.len() - suffix) || !new.is_char_boundary(new.len() - suffix) {
        suffix -= 1;
    }
    let old_range = TextRange::new(
        TextSize::try_from(prefix).ok()?,
        TextSize::try_from(old.len() - suffix).ok()?,
    );
    let new_range = TextRange::new(
        TextSize::try_from(prefix).ok()?,
        TextSize::try_from(new.len() - suffix).ok()?,
    );
    let old_parse = SourceFile::parse(old, edition);
    let new_parse = SourceFile::parse(new, edition);
    if !old_parse.errors().is_empty() || !new_parse.errors().is_empty() {
        return None;
    }
    let old_holder = holder(old_parse.tree().syntax(), old_range)?;
    let new_holder = holder(new_parse.tree().syntax(), new_range)?;
    (old_holder == new_holder).then_some(Some(old_holder))
}

fn holder(root: &SyntaxNode, changed: TextRange) -> Option<ItemPath> {
    for node in root.descendants() {
        let body = if let Some(function) = ast::Fn::cast(node.clone()) {
            function.body()
        } else if let Some(value) = ast::Const::cast(node.clone()) {
            value.body().and_then(|expr| ast::BlockExpr::cast(expr.syntax().clone()))
        } else if let Some(value) = ast::Static::cast(node.clone()) {
            value.body().and_then(|expr| ast::BlockExpr::cast(expr.syntax().clone()))
        } else {
            continue;
        };
        let Some(body) = body else { continue };
        let range = body.syntax().text_range();
        if !(range.start() < changed.start() && changed.end() < range.end()) {
            continue;
        }
        let text = body.syntax().text().to_string();
        let tokens: String = body
            .syntax()
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| !token.kind().is_trivia())
            .map(|token| token.text().to_owned())
            .collect();
        if text.contains("macro_export") || tokens.contains("include!") {
            return None;
        }
        if node.ancestors().any(|ancestor| {
            ast::MacroCall::can_cast(ancestor.kind())
                || ast::MacroRules::can_cast(ancestor.kind())
                || ast::MacroDef::can_cast(ancestor.kind())
        }) {
            return None;
        }
        for ancestor in node.ancestors().chain(
            body.syntax()
                .descendants()
                .filter(|node| node.text_range().intersect(changed).is_some()),
        ) {
            for attr in ancestor.children().filter_map(ast::Attr::cast) {
                if !matches!(
                    attr.simple_name().as_deref(),
                    Some(
                        "allow"
                            | "warn"
                            | "deny"
                            | "forbid"
                            | "expect"
                            | "doc"
                            | "inline"
                            | "cold"
                            | "track_caller"
                            | "must_use"
                            | "deprecated"
                            | "cfg"
                    )
                ) {
                    return None;
                }
            }
        }
        return Some(item_path(&node));
    }
    None
}

fn item_path(node: &SyntaxNode) -> ItemPath {
    node.ancestors()
        .filter_map(|node| {
            let parent = node.parent()?;
            let position = parent.children().position(|child| child == node)?;
            Some((node.kind(), position))
        })
        .collect()
}
