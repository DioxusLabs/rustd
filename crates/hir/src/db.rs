//! Re-exports various subcrates' databases and queries so that the calling code
//! can depend only on `hir`. This breaks abstraction boundary a bit, it would
//! be cool if we didn't do that.
//!
//! But we need this for at least LRU caching at the query level.
pub use hir_def::item_tree::inputs::ItemTreeInputs;
pub use hir_def::{file_item_tree, set_expand_proc_attr_macros, set_lru_capacity};
pub use hir_expand::inputs::MacroExpansionInputs;
pub use hir_ide::db::HirDatabase;
pub use hir_ide::method_resolution::connector::Inputs as TraitImplsInputs;
