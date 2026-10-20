//! Symbol paths shared by the native and WebAssembly resolvers.

use hir::{AsAssocItem, AssocItemContainer, Module, ModuleDef};
use hir_def::{FunctionId, ModuleDefId};
use ide_db::RootDatabase;

/// The function's path as `rustc-demangle` prints its v0 symbol.
///
/// Each resolver supplies the module and type paths, which depend on how it names sources.
pub(crate) fn function(
    db: &RootDatabase,
    func: FunctionId,
    item_path: impl Fn(Module, &str) -> Option<String>,
    type_path: impl Fn(&hir::Type<'_>) -> Option<String>,
) -> Option<String> {
    let ModuleDef::Function(func) = ModuleDef::from(ModuleDefId::FunctionId(func)) else {
        return None;
    };
    let name = func.name(db);
    let Some(assoc) = func.as_assoc_item(db) else {
        return item_path(func.module(db), name.as_str());
    };
    let AssocItemContainer::Impl(imp) = assoc.container(db) else { return None };
    let self_ty = type_path(&imp.self_ty(db))?;
    match imp.trait_(db) {
        Some(trait_) => {
            let mut path = item_path(trait_.module(db), trait_.name(db).as_str())?;
            // `impl PartialEq<str> for String` and `impl PartialEq<&str> for String` are
            // told apart by the trait's arguments alone.
            let trait_ref = imp.trait_ref(db)?;
            let params = hir::GenericDef::from(trait_).type_or_const_params(db);
            let mut args = Vec::new();
            for (idx, param) in params.iter().enumerate().skip(1) {
                let arg = trait_ref.get_type_argument(idx)?;
                let default = param.as_type_param(db).and_then(|it| it.default(db));
                // FIXME: a default that names a parameter is understood only as `= Self`.
                let is_default = default.as_ref().is_some_and(|default| {
                    if default.as_type_param(db).is_some() {
                        return hir::attach_db(db, || arg == trait_ref.self_ty());
                    }
                    let default = type_path(default);
                    default.is_some() && default == type_path(&arg)
                });
                if idx + 1 == params.len() && is_default {
                    break;
                }
                args.push(type_path(&arg)?);
            }
            if !args.is_empty() {
                path = format!("{path}<{}>", args.join(", "));
            }
            let trait_ = path;
            Some(format!("<{self_ty} as {trait_}>::{}", name.as_str()))
        }
        None => Some(format!("<{self_ty}>::{}", name.as_str())),
    }
}
