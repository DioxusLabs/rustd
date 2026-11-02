//! Refresh MEDIUM item-tree inputs before running semantic consumers.

use hir_def::item_tree::{file_item_tree_snapshot, inputs::ItemTreeInput};
use hir_expand::{MacroCallId, MacroDefKind};
use ide_db::base_db::salsa::{Durability, Setter, plumbing::ZalsaDatabase};
use ide_db::{RootDatabase, base_db::EditionedFileId};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::AstNode;
use vfs::FileId;

pub(crate) fn predemote(db: &mut RootDatabase, files: &[FileId]) -> usize {
    refresh(db);
    let count = db.predemote_ladder_files(files);
    if count != 0 {
        if let Some(inputs) = db.item_tree_inputs() {
            inputs.refreshed(db.zalsa().last_changed_revision(Durability::MEDIUM));
        }
        refresh(db);
    }
    count
}

pub(crate) fn refresh(db: &mut RootDatabase) {
    let start = std::time::Instant::now();
    if let Some((written, all, structural)) = refresh_item_trees(db) {
        let trees = start.elapsed();
        refresh_macro_expansions(db, &written, all, &structural);
        if std::env::var_os("RUSTD_LAUNDER_PROFILE").is_some() {
            eprintln!(
                "launder-profile: trees_us={} total_us={} written={} all={} structural={}",
                trees.as_micros(),
                start.elapsed().as_micros(),
                written.len(),
                all,
                structural.len()
            );
        }
    }
    db.refresh_impl_connector();
}

fn refresh_item_trees(
    db: &mut RootDatabase,
) -> Option<(FxHashSet<FileId>, bool, FxHashSet<FileId>)> {
    let inputs = db.item_tree_inputs()?;
    let (written, all) = inputs.take_writes(db.zalsa().last_changed_revision(Durability::MEDIUM));
    let ladder = db.macro_expansion_inputs().is_some();
    let mut structural = FxHashSet::default();
    let mut keys: rustc_hash::FxHashSet<_> = if all {
        inputs.entries().into_iter().map(|(key, _)| key).collect()
    } else {
        FxHashSet::default()
    };
    for &file in &written {
        if ladder && !db.ladder_file_is_low(file) && !db.ladder_file_is_selected(file) {
            continue;
        }
        if let Some(expansions) = db.macro_expansion_inputs() {
            expansions.select_file(file);
        }
        for &krate in ide_db::base_db::relevant_crates(db, file) {
            keys.insert((EditionedFileId::new(db, file, krate.data(db).edition).into(), krate));
        }
    }
    for (file, krate) in keys {
        let value = file_item_tree_snapshot(db, file, krate);
        match inputs.get(file, krate) {
            Some(input) if *input.value(db) != value => {
                structural.insert(file.file_id().unwrap().file_id(db));
                input.set_value(db).with_durability(Durability::MEDIUM).to(value);
            }
            Some(_) => {}
            None => {
                structural.insert(file.file_id().unwrap().file_id(db));
                let input = ItemTreeInput::builder(value).durability(Durability::MEDIUM).new(db);
                inputs.insert(file, krate, input);
            }
        }
    }
    if std::env::var_os("RUSTD_VERIFY_LAUNDER").is_some() {
        for ((file, krate), input) in inputs.entries() {
            assert_eq!(*input.value(db), file_item_tree_snapshot(db, file, krate));
        }
    }
    inputs.refreshed(db.zalsa().last_changed_revision(Durability::MEDIUM));
    Some((written, all, structural))
}

fn refresh_macro_expansions(
    db: &mut RootDatabase,
    written: &FxHashSet<FileId>,
    all: bool,
    structural: &FxHashSet<FileId>,
) {
    let Some(inputs) = db.macro_expansion_inputs() else { return };
    let start = std::time::Instant::now();
    inputs.set_collecting(true);
    let definitions_changed = refresh_declarative_macros(db, &inputs, written, structural);
    let mut crates = FxHashSet::default();
    let mut entries = if all {
        inputs.entries()
    } else {
        written.iter().flat_map(|&file| inputs.entries_for_file(file)).collect()
    };
    entries.sort_unstable_by_key(|(call, _)| call.loc(db).macro_depth);
    let scan = start.elapsed();
    let mut changed = FxHashSet::default();
    let mut reset = !structural.is_empty() || definitions_changed;
    for (call, input) in entries {
        if input.value(db).is_none() {
            continue;
        }
        let loc = call.loc(db);
        let file = loc.kind.file_id().original_file(db).file_id(db);
        if !all && !written.contains(&file) {
            continue;
        }
        if reset {
            continue;
        }
        let mut parent = loc.kind.file_id().macro_file();
        let mut ancestor_changed = false;
        while let Some(call) = parent {
            ancestor_changed |= changed.contains(&call);
            parent = call.loc(db).kind.file_id().macro_file();
        }
        if structural.contains(&file) || ancestor_changed {
            input.set_value(db).with_durability(Durability::MEDIUM).to(None);
            changed.insert(call);
        } else {
            let value = call.parse_macro_expansion(db).clone();
            if input.value(db).as_ref() != Some(&value) {
                input.set_value(db).with_durability(Durability::MEDIUM).to(Some(value));
                changed.insert(call);
            }
        }
    }
    reset |= !changed.is_empty();
    if reset {
        for (key, input) in inputs.declarative_entries() {
            if key.0.file_id.macro_file().is_some() {
                if input.value(db).is_some() {
                    input.set_value(db).with_durability(Durability::MEDIUM).to(None);
                }
                inputs.remove_declarative(db, key);
            }
        }
    }
    let refreshed = start.elapsed();
    if reset {
        for (call, input) in inputs.entries() {
            if input.value(db).is_some() {
                crates.insert(call.loc(db).krate);
                input.set_value(db).with_durability(Durability::MEDIUM).to(None);
            }
        }
    }
    let reset_done = start.elapsed();
    if all || reset {
        for &file in written {
            if db.ladder_file_is_low(file) || db.ladder_file_is_selected(file) {
                crates.extend(ide_db::base_db::relevant_crates(db, file).iter().copied());
            }
        }
        if all {
            crates.extend(inputs.entries().into_iter().map(|(call, _)| call.loc(db).krate));
        }
    }
    let mut discovery_us = 0;
    let mut populate_us = 0;
    for krate in crates {
        let step = std::time::Instant::now();
        let calls: FxHashSet<_> = {
            let map = hir_def::nameres::crate_def_map(db, krate);
            map.modules(db)
                .flat_map(|(_, module)| {
                    let scope = module.scope(db);
                    scope.all_macro_calls().chain(
                        scope
                            .derive_macro_invocs()
                            .flat_map(|(_, attrs)| attrs.map(|(_, call, _)| call)),
                    )
                })
                .collect()
        };
        discovery_us += step.elapsed().as_micros();
        let step = std::time::Instant::now();
        for call in calls {
            populate_macro(db, &inputs, call);
        }
        populate_us += step.elapsed().as_micros();
    }
    for ((id, krate), input) in inputs.declarative_entries() {
        if input.value(db).is_none() {
            let value = id.decl_macro_expander(db, krate).clone();
            input.set_value(db).with_durability(Durability::MEDIUM).to(Some(value));
        }
    }
    inputs.set_collecting(false);
    if std::env::var_os("RUSTD_VERIFY_LAUNDER").is_some() {
        for ((id, krate), input) in inputs.declarative_entries() {
            if let Some(value) = input.value(db) {
                assert_eq!(value, id.decl_macro_expander(db, krate), "declarative macro {id:?}");
            }
        }
        for (call, input) in inputs.entries() {
            if let Some(value) = input.value(db) {
                assert_eq!(value, call.parse_macro_expansion(db), "macro frontier {call:?}");
            }
        }
    }
    if std::env::var_os("RUSTD_LAUNDER_PROFILE").is_some() {
        eprintln!(
            "launder-profile: scan_us={} refresh_us={} reset_us={} discover_us={} populate_us={} macro_total_us={} entries={} reset={}",
            scan.as_micros(),
            (refreshed - scan).as_micros(),
            (reset_done - refreshed).as_micros(),
            discovery_us,
            populate_us,
            start.elapsed().as_micros(),
            inputs.entry_count(),
            reset
        );
    }
}

fn refresh_declarative_macros(
    db: &mut RootDatabase,
    inputs: &hir_expand::inputs::MacroExpansionInputs,
    written: &FxHashSet<FileId>,
    structural: &FxHashSet<FileId>,
) -> bool {
    let mut changed = false;
    let mut definitions = FxHashMap::default();
    for &file in written {
        for (key @ (id, krate), input) in inputs.declarative_entries_for_file(file) {
            let valid = !structural.contains(&file) && id.file_id.macro_file().is_none() && {
                let ids = definitions.entry(id.file_id).or_insert_with(|| {
                    let map = id.file_id.ast_id_map(db);
                    id.file_id
                        .parse_or_expand(db)
                        .descendants()
                        .filter_map(syntax::ast::Macro::cast)
                        .map(|node| map.ast_id(&node))
                        .collect::<FxHashSet<_>>()
                });
                ids.contains(&id.value)
            };
            if !valid {
                if input.value(db).is_some() {
                    input.set_value(db).with_durability(Durability::MEDIUM).to(None);
                }
                inputs.remove_declarative(db, key);
                changed = true;
                continue;
            }
            let value = id.decl_macro_expander(db, krate).clone();
            if input.value(db).as_ref() != Some(&value) {
                input.set_value(db).with_durability(Durability::MEDIUM).to(Some(value));
                changed = true;
            }
        }
    }
    changed
}

#[cfg(test)]
mod tests {
    #[test]
    fn ordinary_medium_edit_keeps_conservative_refresh() {
        use ide_db::base_db::{
            SourceDatabase, SourceRoot, SourceRootId,
            salsa::{Durability, plumbing::ZalsaDatabase},
        };
        use triomphe::Arc;
        use vfs::{FileId, VfsPath, file_set::FileSet};

        let mut db = ide_db::RootDatabase::new(None);
        assert_eq!(super::predemote(&mut db, &[]), 0);
        db.enable_ladder(vec![("/selected".into(), true)], false);
        let file = FileId::from_raw(0);
        let mut files = FileSet::default();
        files.insert(file, VfsPath::new_real_path("/selected/lib.rs".into()));
        let root = SourceRootId(0);
        db.set_source_root_with_durability(
            root,
            Arc::new(SourceRoot::new_local(files)),
            Durability::LOW,
        );
        db.set_file_source_root_with_durability(file, root, Durability::LOW);
        db.set_file_text(file, "pub fn old() {}");
        super::refresh(&mut db);
        let medium = db.zalsa().last_changed_revision(Durability::MEDIUM);
        db.set_file_text(file, "pub fn new() {}");
        let changed = db.zalsa().last_changed_revision(Durability::MEDIUM);
        assert!(changed > medium);
        let (written, all) = db.item_tree_inputs().unwrap().take_writes(changed);
        assert!(written.contains(&file));
        assert!(all);
    }

    #[test]
    fn macro_frontier_refreshes_cross_file_definitions_and_removed_calls() {
        use ide_db::base_db::salsa::plumbing::ZalsaDatabase;
        use ide_db::{
            RootDatabase,
            base_db::{
                CrateGraphBuilder, CrateOrigin, CrateWorkspaceData, SourceDatabase, SourceRoot,
                SourceRootId, all_crates, salsa::Durability,
            },
        };
        use triomphe::Arc;
        use vfs::{AbsPathBuf, FileId, VfsPath, file_set::FileSet};

        let mut db = RootDatabase::new(None);
        db.enable_ladder(vec![("/selected".into(), true)], false);
        let texts = [
            "#[macro_use] mod defs; mod calls;",
            "macro_rules! make { () => { pub struct Old; } } pub fn sibling() { let _ = 0; }",
            "make!(); pub fn edited() { let _ = 0; }",
        ];
        let mut files = FileSet::default();
        for (index, name) in ["lib", "defs", "calls"].into_iter().enumerate() {
            files.insert(
                FileId::from_raw(index as u32),
                VfsPath::new_real_path(format!("/selected/{name}.rs")),
            );
        }
        let root = SourceRootId(0);
        db.set_source_root_with_durability(
            root,
            Arc::new(SourceRoot::new_local(files)),
            Durability::LOW,
        );
        for (index, text) in texts.iter().enumerate() {
            let file = FileId::from_raw(index as u32);
            db.set_file_source_root_with_durability(file, root, Durability::LOW);
            db.set_file_text_with_durability(file, text, Durability::LOW);
        }
        let mut graph = CrateGraphBuilder::default();
        graph.add_crate_root(
            FileId::from_raw(0),
            syntax::Edition::CURRENT,
            None,
            None,
            Default::default(),
            None,
            Default::default(),
            CrateOrigin::Local { repo: None, name: None },
            Vec::new(),
            false,
            Arc::new(AbsPathBuf::assert_utf8("/selected".into())),
            Arc::new(CrateWorkspaceData { target: Err("".into()), toolchain: None }),
        );
        graph.set_in_db(&mut db);
        super::refresh(&mut db);
        let krate = all_crates(&db)[0];
        let names = |db: &RootDatabase| {
            hir_def::nameres::crate_def_map(db, krate)
                .modules(db)
                .flat_map(|(_, module)| {
                    module.scope(db).entries().map(|(name, _)| name.as_str().to_owned())
                })
                .collect::<Vec<_>>()
        };
        assert!(names(&db).contains(&"Old".to_owned()));
        let inputs = db.macro_expansion_inputs().unwrap();
        let declarative = inputs.declarative_entries_for_file(FileId::from_raw(1));
        assert!(!declarative.is_empty());
        let definitions: Vec<_> = declarative
            .iter()
            .map(|(_, input)| input.value(&db).clone().expect("populated declarative macro"))
            .collect();
        assert!(inputs.declarative_entries_for_file(FileId::from_raw(2)).is_empty());
        assert!(inputs.entries().iter().any(|(_, input)| input.value(&db).is_some()));
        let calls = inputs.entries_for_file(FileId::from_raw(2));
        assert!(!calls.is_empty());
        assert!(inputs.entries_for_file(FileId::from_raw(0)).is_empty());
        assert_eq!(inputs.entry_count(), calls.len());
        super::refresh(&mut db);
        assert_eq!(inputs.entry_count(), calls.len());
        assert!(!db.ladder_file_is_low(FileId::from_raw(2)));
        let retained = inputs.entries();
        let values: Vec<_> = retained.iter().map(|(_, input)| input.value(&db).clone()).collect();
        let medium = db.zalsa().last_changed_revision(Durability::MEDIUM);
        let files = [0, 1, 2].map(FileId::from_raw);
        assert_eq!(super::predemote(&mut db, &files), 3);
        assert!(db.zalsa().last_changed_revision(Durability::MEDIUM) > medium);
        assert_eq!(super::predemote(&mut db, &files), 0);
        for ((_, input), value) in retained.iter().zip(&values) {
            assert_eq!(input.value(&db), value);
        }
        for (&file, text) in files.iter().zip(texts) {
            assert!(db.ladder_file_is_low(file));
            assert_eq!(&**db.file_text(file).text(&db), text);
        }
        for ((_, input), value) in declarative.iter().zip(&definitions) {
            assert_eq!(input.value(&db).as_ref(), Some(value));
        }
        let medium = db.zalsa().last_changed_revision(Durability::MEDIUM);
        db.set_file_text(FileId::from_raw(1), &texts[1].replace("= 0", "= 1"));
        super::refresh(&mut db);
        assert_eq!(db.zalsa().last_changed_revision(Durability::MEDIUM), medium);
        assert!(inputs.declarative_entries_for_file(FileId::from_raw(1)) == declarative);
        for ((id, krate), input) in &declarative {
            assert_eq!(input.value(&db).as_ref(), Some(id.decl_macro_expander(&db, *krate)));
        }
        for ((_, input), value) in retained.iter().zip(&values) {
            assert_eq!(input.value(&db), value);
        }
        let medium = db.zalsa().last_changed_revision(Durability::MEDIUM);
        assert!(!db.item_tree_inputs().unwrap().take_writes(medium).1);
        db.set_file_text(FileId::from_raw(2), &texts[2].replace("= 0", "= 1"));
        super::refresh(&mut db);
        assert!(
            db.macro_expansion_inputs()
                .unwrap()
                .entries()
                .iter()
                .any(|(_, input)| input.value(&db).is_some())
        );
        for name in ["New", "Again"] {
            db.set_file_text(FileId::from_raw(1), &texts[1].replace("Old", name));
            super::refresh(&mut db);
            assert!(db.zalsa().last_changed_revision(Durability::MEDIUM) > medium);
            assert!(names(&db).contains(&name.to_owned()));
            assert!(!names(&db).contains(&"Old".to_owned()));
            for ((id, krate), input) in inputs.declarative_entries_for_file(FileId::from_raw(1)) {
                assert_eq!(input.value(&db).as_ref(), Some(id.decl_macro_expander(&db, krate)));
                assert_ne!(input.value(&db).as_ref(), definitions.first());
            }
        }
        for (file, text) in [
            (1, "macro_rules! make { () => { pub struct"),
            (2, "pub fn edited() {}"),
            (1, ""),
            (2, ""),
            (1, texts[1]),
            (2, texts[2]),
        ] {
            db.set_file_text(FileId::from_raw(file), text);
            super::refresh(&mut db);
            let _ = names(&db);
        }
        assert!(names(&db).contains(&"Old".to_owned()));
        let generated = "macro_rules! outer { () => { macro_rules! make { () => { pub struct Old; } } } } outer!();";
        db.set_file_text(FileId::from_raw(1), generated);
        super::refresh(&mut db);
        assert!(names(&db).contains(&"Old".to_owned()));
        assert!(inputs.declarative_entries_for_file(FileId::from_raw(1)).iter().any(
            |((id, _), input)| { id.file_id.macro_file().is_some() && input.value(&db).is_some() }
        ));
        db.set_file_text(FileId::from_raw(1), &generated.replace("Old", "Generated"));
        super::refresh(&mut db);
        assert!(names(&db).contains(&"Generated".to_owned()));
        assert!(!names(&db).contains(&"Old".to_owned()));
        db.set_file_text(FileId::from_raw(1), "");
        super::refresh(&mut db);
        assert!(inputs.declarative_entries_for_file(FileId::from_raw(1)).is_empty());
    }
}

fn populate_macro(
    db: &mut RootDatabase,
    inputs: &hir_expand::inputs::MacroExpansionInputs,
    call: MacroCallId,
) {
    if let Some(arg) = call.eager_argument(db) {
        populate_macro(db, inputs, arg);
    }
    let loc = call.loc(db);
    let file = loc.kind.file_id().original_file(db).file_id(db);
    if !db.ladder_file_is_low(file) && !db.ladder_file_is_selected(file) {
        return;
    }
    if matches!(loc.def.kind, MacroDefKind::BuiltInEager(..)) {
        eprintln!("ladder-leak: eager item call {call:?} in {file:?} remains tracked");
        return;
    }
    let input = inputs.input(db, call);
    let value = call.parse_macro_expansion(db).clone();
    if input.value(db).as_ref() != Some(&value) {
        input.set_value(db).with_durability(Durability::MEDIUM).to(Some(value));
    }
}
