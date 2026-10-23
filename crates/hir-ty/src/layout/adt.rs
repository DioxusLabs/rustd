//! Compute the binary representation of structs, unions and enums

use std::cmp;

use hir_def::{
    AdtId, VariantId,
    attrs::AttrFlags,
    signatures::{StructFlags, StructSignature, VariantFields},
};
use rustc_abi::{Integer, ReprOptions, TargetDataLayout};
use rustc_index::IndexVec;
use smallvec::SmallVec;
use triomphe::Arc;

use crate::{
    db::HirDatabase,
    layout::{Layout, LayoutCx, LayoutError, field_ty},
    next_solver::{DbInterner, StoredGenericArgs, TypingMode, infer::DbInternerInferExt},
    representability::{Representability, representability},
    traits::StoredParamEnvAndCrate,
};

#[salsa::tracked(cycle_result = layout_of_adt_cycle_result, returns(clone))]
pub fn layout_of_adt_query(
    db: &dyn HirDatabase,
    def: AdtId,
    args: StoredGenericArgs,
    trait_env: StoredParamEnvAndCrate,
) -> Result<Arc<Layout>, LayoutError> {
    layout_of_adt_with(db, def, args, trait_env, &super::DbLayout(db))
}

pub(crate) fn layout_of_adt_with<'db>(
    db: &'db dyn HirDatabase,
    def: AdtId,
    args: StoredGenericArgs,
    trait_env: StoredParamEnvAndCrate,
    provider: &dyn super::LayoutProvider<'db>,
) -> Result<Arc<Layout>, LayoutError> {
    let krate = trait_env.krate;
    let Ok(target) = db.target_data_layout(krate) else {
        return Err(LayoutError::TargetLayoutNotAvailable);
    };
    if representability(db, def) == Representability::Infinite {
        return Err(LayoutError::RecursiveTypeWithoutIndirection);
    }
    let dl = target;
    let cx = LayoutCx::new(dl);
    let handle_variant = |def: VariantId, var: &VariantFields| {
        var.fields()
            .iter()
            .map(|(fd, _)| {
                provider.layout(field_ty(db, def, fd, args.as_ref()).store(), trait_env.clone())
            })
            .collect::<Result<Vec<_>, _>>()
    };
    let (variants, repr, is_special_no_niche) = match def {
        AdtId::StructId(s) => {
            let sig = StructSignature::of(db, s);
            let mut r = SmallVec::<[_; 1]>::new();
            r.push(handle_variant(s.into(), s.fields(db))?);
            (
                r,
                AttrFlags::repr(db, s.into()).unwrap_or_default(),
                sig.flags.intersects(StructFlags::IS_UNSAFE_CELL | StructFlags::IS_UNSAFE_PINNED),
            )
        }
        AdtId::UnionId(id) => {
            let repr = AttrFlags::repr(db, id.into());
            let mut r = SmallVec::new();
            r.push(handle_variant(id.into(), id.fields(db))?);
            (r, repr.unwrap_or_default(), false)
        }
        AdtId::EnumId(e) => {
            let variants = e.enum_variants(db);
            let r = variants
                .variants
                .values()
                .map(|&(v, _)| handle_variant(v.into(), v.fields(db)))
                .collect::<Result<SmallVec<_>, _>>()?;
            (r, AttrFlags::repr(db, e.into()).unwrap_or_default(), false)
        }
    };
    // A struct whose last field may be unsized for some generic arguments keeps that field last
    // for all of them, so that unsizing the struct does not move it.
    let maybe_unsized = match def {
        AdtId::StructId(s) => s.fields(db).fields().iter().last().is_some_and(|(fd, _)| {
            let interner = DbInterner::new_with(db, krate);
            let infcx = interner.infer_ctxt().build(TypingMode::PostAnalysis);
            let ty = db.field_types(s.into())[fd].ty().instantiate_identity().skip_norm_wip();
            !infcx.type_is_sized_modulo_regions(db.trait_environment(def.into()), ty)
        }),
        AdtId::UnionId(_) | AdtId::EnumId(_) => false,
    };
    let variants = variants
        .iter()
        .map(|it| it.iter().map(|it| &**it).collect::<Vec<_>>())
        .collect::<SmallVec<[_; 1]>>();
    let variants = variants.iter().map(|it| it.iter().collect()).collect::<IndexVec<_, _>>();
    let result = if matches!(def, AdtId::UnionId(..)) {
        cx.calc.layout_of_union(&repr, &variants)?
    } else {
        cx.calc.layout_of_struct_or_enum(
            &repr,
            &variants,
            matches!(def, AdtId::EnumId(..)),
            is_special_no_niche,
            |min, max| repr_discr(dl, &repr, min.start, max.last).unwrap_or((Integer::I8, false)),
            variants.iter_enumerated().filter_map(|(id, _)| {
                let AdtId::EnumId(e) = def else { return None };
                let d = db.const_eval_discriminant(e.enum_variants(db).variants[id.0].0).ok()?;
                // As rustc has a discriminant: the bits of its type, and no more.
                let size = Integer::from_attr(dl, repr.discr_type()).size();
                Some((id, size.truncate(d as u128)))
            }),
            !matches!(def, AdtId::EnumId(..)) && !maybe_unsized,
        )?
    };
    Ok(Arc::new(result))
}

fn layout_of_adt_cycle_result(
    _: &dyn HirDatabase,
    _: salsa::Id,
    _def: AdtId,
    _args: StoredGenericArgs,
    _trait_env: StoredParamEnvAndCrate,
) -> Result<Arc<Layout>, LayoutError> {
    Err(LayoutError::RecursiveTypeWithoutIndirection)
}

/// Finds the appropriate Integer type and signedness for the given
/// signed discriminant range and `#[repr]` attribute.
/// N.B.: `u128` values above `i128::MAX` will be treated as signed, but
/// that shouldn't affect anything, other than maybe debuginfo.
fn repr_discr(
    dl: &TargetDataLayout,
    repr: &ReprOptions,
    min: i128,
    max: u128,
) -> Result<(Integer, bool), LayoutError> {
    // Theoretically, negative values could be larger in unsigned representation
    // than the unsigned representation of the signed minimum. However, if there
    // are any negative values, the only valid unsigned representation is u128
    // which can fit all i128 values, so the result remains unaffected.
    let unsigned_fit = Integer::fit_unsigned(cmp::max(min as u128, max));
    let signed_fit = cmp::max(Integer::fit_signed(min), Integer::fit_signed(max as i128));

    if let Some(ity) = repr.int {
        let discr = Integer::from_attr(dl, ity);
        let fit = if ity.is_signed() { signed_fit } else { unsigned_fit };
        if discr < fit {
            return Err(LayoutError::UserReprTooSmall);
        }
        return Ok((discr, ity.is_signed()));
    }

    let at_least = if repr.c() {
        // This is usually I32, however it can be different on some platforms,
        // notably hexagon and arm-none/thumb-none
        dl.c_enum_min_size
    } else {
        // repr(Rust) enums try to be as small as possible
        Integer::I8
    };

    // `min` and `max` are the ends of a wrapping range, so their sign is not a usable test.
    Ok(if unsigned_fit <= signed_fit {
        (cmp::max(unsigned_fit, at_least), false)
    } else {
        (cmp::max(signed_fit, at_least), true)
    })
}
