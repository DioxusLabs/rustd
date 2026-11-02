//! Connector-owned item trees. Membership must be populated before consumers run.

use std::sync::Mutex;

use base_db::Crate;
use hir_expand::HirFileId;
use rustc_hash::{FxHashMap, FxHashSet};
use span::FileId;

use super::ItemTree;

#[salsa::input]
pub struct ItemTreeInput {
    #[returns(ref)]
    pub value: Option<std::sync::Arc<ItemTree>>,
}

#[derive(Default)]
pub struct ItemTreeInputs {
    state: Mutex<State>,
}

#[derive(Default)]
struct State {
    entries: FxHashMap<(HirFileId, Crate), ItemTreeInput>,
    written: FxHashSet<FileId>,
    all: bool,
    medium: Option<salsa::Revision>,
}

impl ItemTreeInputs {
    pub fn get(&self, file: HirFileId, krate: Crate) -> Option<ItemTreeInput> {
        self.state.lock().unwrap().entries.get(&(file, krate)).copied()
    }

    pub fn insert(&self, file: HirFileId, krate: Crate, input: ItemTreeInput) {
        assert!(!file.is_macro());
        self.state.lock().unwrap().entries.insert((file, krate), input);
    }

    pub fn entries(&self) -> Vec<((HirFileId, Crate), ItemTreeInput)> {
        self.state.lock().unwrap().entries.iter().map(|(&key, &value)| (key, value)).collect()
    }

    pub fn written(&self, file: FileId) {
        self.state.lock().unwrap().written.insert(file);
    }

    pub fn invalidate_all(&self) {
        self.state.lock().unwrap().all = true;
    }

    pub fn take_writes(&self, medium: salsa::Revision) -> (FxHashSet<FileId>, bool) {
        let mut state = self.state.lock().unwrap();
        let all = state.all || state.medium != Some(medium);
        state.all = false;
        (std::mem::take(&mut state.written), all)
    }

    pub fn refreshed(&self, medium: salsa::Revision) {
        self.state.lock().unwrap().medium = Some(medium);
    }
}
