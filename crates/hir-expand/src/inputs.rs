use std::sync::{
    Mutex,
    atomic::{AtomicBool, Ordering},
};

use base_db::{Crate, SourceDatabase};
use rustc_hash::FxHashMap;
use salsa::Durability;
use span::FileId;
use syntax::{Parse, SyntaxNode, ast};

use crate::{
    AstId, ExpandResult, ExpansionSpanMap, MacroCallId, MacroDefKind,
    declarative::DeclarativeMacroExpander,
};

pub type MacroExpansion = ExpandResult<(Parse<SyntaxNode>, ExpansionSpanMap)>;

#[salsa::input]
pub struct MacroExpansionInput {
    #[returns(ref)]
    pub value: Option<MacroExpansion>,
}

pub type DeclarativeMacroKey = (AstId<ast::Macro>, Crate);

#[salsa::input]
pub struct DeclarativeMacroInput {
    #[returns(ref)]
    pub value: Option<DeclarativeMacroExpander>,
}

#[derive(Default)]
pub struct MacroExpansionInputs {
    entries: Mutex<FxHashMap<FileId, FxHashMap<MacroCallId, MacroExpansionInput>>>,
    declarative: Mutex<FxHashMap<FileId, FxHashMap<DeclarativeMacroKey, DeclarativeMacroInput>>>,
    collecting: AtomicBool,
}

impl MacroExpansionInputs {
    pub fn set_collecting(&self, collecting: bool) {
        self.collecting.store(collecting, Ordering::Relaxed);
    }

    pub fn select_file(&self, file: FileId) {
        self.entries.lock().unwrap().entry(file).or_default();
        self.declarative.lock().unwrap().entry(file).or_default();
    }

    fn selected_declarative_input(
        &self,
        db: &dyn SourceDatabase,
        key: DeclarativeMacroKey,
    ) -> Option<DeclarativeMacroInput> {
        let file = key.0.file_id.original_file(db).file_id(db);
        let mut entries = self.declarative.lock().unwrap();
        let entries = entries.get_mut(&file)?;
        if let Some(&input) = entries.get(&key) {
            return Some(input);
        }
        if !self.collecting.load(Ordering::Relaxed) {
            return None;
        }
        Some(*entries.entry(key).or_insert_with(|| {
            DeclarativeMacroInput::builder(None).durability(Durability::MEDIUM).new(db)
        }))
    }

    pub fn declarative_entries_for_file(
        &self,
        file: FileId,
    ) -> Vec<(DeclarativeMacroKey, DeclarativeMacroInput)> {
        self.declarative.lock().unwrap().get(&file).map_or_else(Vec::new, |entries| {
            entries.iter().map(|(&key, &input)| (key, input)).collect()
        })
    }

    pub fn declarative_entries(&self) -> Vec<(DeclarativeMacroKey, DeclarativeMacroInput)> {
        self.declarative
            .lock()
            .unwrap()
            .values()
            .flat_map(|entries| entries.iter().map(|(&key, &input)| (key, input)))
            .collect()
    }

    pub fn remove_declarative(&self, db: &dyn SourceDatabase, key: DeclarativeMacroKey) {
        let file = key.0.file_id.original_file(db).file_id(db);
        if let Some(entries) = self.declarative.lock().unwrap().get_mut(&file) {
            entries.remove(&key);
        }
    }

    pub fn input(&self, db: &dyn SourceDatabase, call: MacroCallId) -> MacroExpansionInput {
        let file = call.loc(db).kind.file_id().original_file(db).file_id(db);
        *self.entries.lock().unwrap().entry(file).or_default().entry(call).or_insert_with(|| {
            MacroExpansionInput::builder(None).durability(Durability::MEDIUM).new(db)
        })
    }

    fn selected_input(
        &self,
        db: &dyn SourceDatabase,
        call: MacroCallId,
    ) -> Option<MacroExpansionInput> {
        let file = call.loc(db).kind.file_id().original_file(db).file_id(db);
        let mut entries = self.entries.lock().unwrap();
        let entries = entries.get_mut(&file)?;
        if let Some(&input) = entries.get(&call) {
            return Some(input);
        }
        if !self.collecting.load(Ordering::Relaxed) {
            return None;
        }
        Some(*entries.entry(call).or_insert_with(|| {
            MacroExpansionInput::builder(None).durability(Durability::MEDIUM).new(db)
        }))
    }

    pub fn entries_for_file(&self, file: FileId) -> Vec<(MacroCallId, MacroExpansionInput)> {
        self.entries.lock().unwrap().get(&file).map_or_else(Vec::new, |entries| {
            entries.iter().map(|(&call, &input)| (call, input)).collect()
        })
    }

    pub fn entry_count(&self) -> usize {
        self.entries.lock().unwrap().values().map(|entries| entries.len()).sum()
    }

    pub fn entries(&self) -> Vec<(MacroCallId, MacroExpansionInput)> {
        self.entries
            .lock()
            .unwrap()
            .values()
            .flat_map(|entries| entries.iter().map(|(&call, &input)| (call, input)))
            .collect()
    }
}

impl AstId<ast::Macro> {
    pub fn decl_macro_expander_laundered(
        self,
        db: &dyn SourceDatabase,
        krate: Crate,
    ) -> &DeclarativeMacroExpander {
        if let Some(inputs) =
            db.macro_expansion_data().and_then(|data| data.downcast_ref::<MacroExpansionInputs>())
            && let Some(input) = inputs.selected_declarative_input(db, (self, krate))
            && let Some(value) = input.value(db)
        {
            return value;
        }
        self.decl_macro_expander(db, krate)
    }
}

impl MacroCallId {
    pub fn eager_argument(self, db: &dyn SourceDatabase) -> Option<MacroCallId> {
        match &self.loc(db).kind {
            crate::MacroCallKind::FnLike { eager: Some(eager), .. } => Some(eager.arg_id),
            _ => None,
        }
    }

    pub fn parse_macro_expansion_laundered(self, db: &dyn SourceDatabase) -> &MacroExpansion {
        if !matches!(self.loc(db).def.kind, MacroDefKind::BuiltInEager(..))
            && let Some(inputs) = db
                .macro_expansion_data()
                .and_then(|data| data.downcast_ref::<MacroExpansionInputs>())
            && let Some(input) = inputs.selected_input(db, self)
            && let Some(value) = input.value(db)
        {
            return value;
        }
        self.parse_macro_expansion(db)
    }
}
