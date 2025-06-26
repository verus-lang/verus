use crate::unsupported_err;
use rustc_hir::def::{CtorKind, CtorOf, DefKind, Res};
use rustc_middle::ty::{Ty, TyCtxt, TyKind, VariantDef};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use vir::ast::VirErr;

#[derive(PartialEq, Eq, Debug)]
pub(crate) enum AdtKind {
    Struct,
    Enum,
    Union,
}

#[derive(Debug)]
pub(crate) struct Ctor<'tcx> {
    pub adt_def_id: DefId,
    pub variant_def: &'tcx VariantDef,
    pub kind: AdtKind,
}

impl<'tcx> Ctor<'tcx> {
    pub(crate) fn variant_name(
        &self,
        tcx: TyCtxt<'tcx>,
        fields: &'tcx [rustc_hir::ExprField<'tcx>],
    ) -> vir::ast::Ident {
        match &self.kind {
            AdtKind::Union => {
                // For a union, rustc has one "variant" with all the fields, while our
                // VIR representation has one variant per field.
                // Use the name of the VIR variant (same as the field name).
                assert!(fields.len() == 1);
                air::ast_util::str_ident(fields[0].ident.as_str())
            }
            AdtKind::Struct | AdtKind::Enum => {
                air::ast_util::str_ident(&self.variant_def.ident(tcx).as_str())
            }
        }
    }
}

// Some notes about rustc's representation:
//
//  * Every ADT has some number of "variants". Structs and unions always 1 "variant".
//
//  * Every variant optionally has a "constructor kind". The ctor_kind() is one of:
//        None, Some(CtorKind::Fn) or Some(CtorKind::Const)
//
//  * For variants that have a CtorKind, there is a separate DefId for the constructor.
//
//  * Res object can resolve to either Constructors, Variants, or Types.
//
//  * When a constructor is used as an expression (ExprKind::Path) it will resolve to the
//    the DefId of the Constructor (the Res will be of DefKind::Ctor or Res::SelfCtor, i.e.,
//    something with Ctor in its name). This can only happen for any variant which has
//    a CtorKind and a Constructor DefId.
//
//  * However, for a *braces-style* constructor expression (ExprKind::Struct),
//    the Res resolves to a Variant (for enums) or to a Type (for structs and unions).
//    This can happen for _any_ variant, not just those that have a CtorKind.

/// Const and tuple-style (i.e., when the path appears in an expression position)
///
/// Returns struct/enum only, never union. Returns None if this is not a constructor.
///
/// Caller should check the CtorKind is correct for its context.
pub(crate) fn resolve_ctor<'tcx>(tcx: TyCtxt<'tcx>, res: Res) -> Option<(Ctor<'tcx>, CtorKind)> {
    match res {
        Res::Def(DefKind::Ctor(CtorOf::Struct, ctor_kind), ctor_did) => {
            let struct_did = tcx.parent(ctor_did);
            let adt_def = tcx.adt_def(struct_did);
            assert!(adt_def.is_struct());
            let variant_def = adt_def.non_enum_variant();
            assert!(variant_def.ctor_kind() == Some(ctor_kind));
            Some((Ctor { adt_def_id: struct_did, variant_def, kind: AdtKind::Struct }, ctor_kind))
        }
        Res::Def(DefKind::Ctor(CtorOf::Variant, ctor_kind), variant_ctor_did) => {
            let variant_did = tcx.parent(variant_ctor_did);
            let enum_did = tcx.parent(variant_did);
            let adt_def = tcx.adt_def(enum_did);
            assert!(adt_def.is_enum());
            let variant_def = adt_def.variant_with_ctor_id(variant_ctor_did);
            assert!(variant_def.ctor_kind() == Some(ctor_kind));
            Some((Ctor { adt_def_id: adt_def.did(), variant_def, kind: AdtKind::Enum }, ctor_kind))
        }
        Res::SelfCtor(impl_id) => {
            let self_ty = tcx.type_of(impl_id).skip_binder();
            let struct_did = match self_ty.kind() {
                TyKind::Adt(adt_def, _args) => adt_def.did(),
                _ => {
                    panic!("got unexpected Self type trying to resolve constructor")
                }
            };

            let adt_def = tcx.adt_def(struct_did);
            assert!(adt_def.is_struct());

            let variant_def = adt_def.non_enum_variant();

            assert!(variant_def.ctor_kind().is_some());

            Some((
                Ctor { adt_def_id: struct_did, variant_def, kind: AdtKind::Struct },
                variant_def.ctor_kind().unwrap(),
            ))
        }
        _ => None,
    }
}

/// Braces-style (i.e., when the path appears as an argument to ExprKind::Struct or PatKind::Struct)
pub(crate) fn resolve_braces_ctor<'tcx>(
    tcx: TyCtxt<'tcx>,
    res: Res,
    ty: Ty<'tcx>,
    allow_union: bool,
    span: Span,
) -> Result<Ctor<'tcx>, VirErr> {
    match ty.kind() {
        TyKind::Adt(adt_def, _args) => {
            if adt_def.is_struct() || adt_def.is_union() {
                if !allow_union && adt_def.is_union() {
                    unsupported_err!(span, "using a union here")
                }
                let kind = if adt_def.is_struct() { AdtKind::Struct } else { AdtKind::Union };
                return Ok(Ctor {
                    adt_def_id: adt_def.did(),
                    variant_def: adt_def.non_enum_variant(),
                    kind,
                });
            }
        }
        _ => {
            panic!("get_adt_res expected Adt type");
        }
    }

    // Must be an enum, so the only possibility is DefKind::Variant
    // (DefKind::Ctor only shows for resolve_ctor, don't have to handle it here)

    match res {
        Res::Def(DefKind::Variant, did) => {
            let enum_did = tcx.parent(did);
            let variant_def = tcx.adt_def(enum_did).variant_with_id(did);
            return Ok(Ctor { adt_def_id: enum_did, variant_def, kind: AdtKind::Enum });
        }
        _ => {
            crate::internal_err!(span, "unexpected Res trying to resolve struct constructor", res)
        }
    }
}
