use crate::attributes::{get_mode, get_ret_mode, get_var_mode, AttrPublish, VerifierAttrs};
use crate::automatic_derive::AutomaticDeriveAction;
use crate::context::{BodyCtxt, Context};
use crate::rust_to_vir_base::mk_visibility;
use crate::rust_to_vir_base::{
    check_generics_bounds_no_polarity, def_id_to_vir_path, mid_ty_to_vir, no_body_param_to_var,
};
use crate::rust_to_vir_expr::{expr_to_vir, pat_to_mut_var, ExprModifier};
use crate::rust_to_vir_impl::ExternalInfo;
use crate::util::{err_span, err_span_bare};
use crate::verus_items::{BuiltinTypeItem, VerusItem};
use crate::{unsupported_err, unsupported_err_unless};
use rustc_ast::Attribute;
use rustc_hir::{
    Body, BodyId, Crate, ExprKind, FnDecl, FnHeader, FnSig, Generics, HirId, MaybeOwner, Param,
    Safety,
};
use rustc_middle::ty::{
    AdtDef, BoundRegion, BoundRegionKind, BoundVar, Clause, ClauseKind, GenericArgKind,
    GenericArgsRef, Region, TraitRef, TyCtxt, TyKind,
};
use rustc_span::def_id::DefId;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use rustc_trait_selection::traits::ImplSource;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{
    BodyVisibility, Fun, FunX, FunctionAttrsX, FunctionKind, FunctionX, GenericBoundX, ItemKind,
    KrateX, Mode, Opaqueness, ParamX, SpannedTyped, Typ, TypDecoration, TypX, VarIdent, VirErr,
    Visibility,
};
use vir::ast_util::{air_unique_var, clean_ensures_for_unit_return, unit_typ};
use vir::def::{RETURN_VALUE, VERUS_SPEC};
use vir::sst_util::subst_typ;

pub(crate) fn autospec_fun(path: &vir::ast::Path, method_name: String) -> vir::ast::Path {
    // turn a::b::c into a::b::method_name
    let mut pathx = (**path).clone();
    let mut segments = (*pathx.segments).clone();
    *segments.last_mut().expect("empty path") = Arc::new(method_name);
    pathx.segments = Arc::new(segments);
    Arc::new(pathx)
}

pub(crate) fn body_id_to_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: &BodyId,
) -> &'tcx rustc_middle::ty::TypeckResults<'tcx> {
    tcx.typeck(id.hir_id.owner.def_id)
}

pub(crate) fn body_to_vir<'tcx>(
    ctxt: &Context<'tcx>,
    fun_id: DefId,
    id: &BodyId,
    body: &Body<'tcx>,
    mode: Mode,
    external_body: bool,
) -> Result<vir::ast::Expr, VirErr> {
    let types = body_id_to_types(ctxt.tcx, id);
    let bctx = BodyCtxt {
        ctxt: ctxt.clone(),
        types,
        fun_id,
        mode,
        external_body,
        in_ghost: mode != Mode::Exec,
    };
    let e = expr_to_vir(&bctx, &body.value, ExprModifier::REGULAR)?;

    if external_body {
        match &e.x {
            vir::ast::ExprX::NeverToAny(e) => Ok(e.clone()),
            _ => Ok(e),
        }
    } else {
        Ok(e)
    }
}

fn check_fn_decl<'tcx>(
    span: Span,
    ctxt: &Context<'tcx>,
    id: DefId,
    decl: &'tcx FnDecl<'tcx>,
    attrs: &[Attribute],
    mode: Mode,
    output_ty: rustc_middle::ty::Ty<'tcx>,
) -> Result<Option<(Typ, Mode)>, VirErr> {
    let FnDecl { inputs: _, output, c_variadic, implicit_self, lifetime_elision_allowed: _ } = decl;
    unsupported_err_unless!(!c_variadic, span, "c_variadic functions");
    match implicit_self {
        rustc_hir::ImplicitSelfKind::None => {}
        rustc_hir::ImplicitSelfKind::Imm => {}
        rustc_hir::ImplicitSelfKind::RefImm => {}
        rustc_hir::ImplicitSelfKind::RefMut => {}
        rustc_hir::ImplicitSelfKind::Mut => unsupported_err!(span, "mut self"),
    }
    match output {
        rustc_hir::FnRetTy::DefaultReturn(_) => Ok(None),
        // REVIEW: there's no attribute syntax on return types,
        // so we always return the default mode.
        // The current workaround is to return a struct if the default doesn't work.
        rustc_hir::FnRetTy::Return(_ty) => {
            let typ = mid_ty_to_vir(ctxt.tcx, &ctxt.verus_items, id, span, &output_ty, false)?;
            Ok(Some((typ, get_ret_mode(mode, attrs))))
        }
    }
}

pub(crate) fn find_body_krate<'tcx>(
    krate: &'tcx Crate<'tcx>,
    body_id: &BodyId,
) -> &'tcx Body<'tcx> {
    let owner = krate.owners[body_id.hir_id.owner.def_id];
    if let MaybeOwner::Owner(owner) = owner {
        if let Some(body) = owner.nodes.bodies.get(&body_id.hir_id.local_id) {
            return body;
        }
    }
    panic!("Body not found");
}

pub(crate) fn find_body<'tcx>(ctxt: &Context<'tcx>, body_id: &BodyId) -> &'tcx Body<'tcx> {
    find_body_krate(ctxt.krate, body_id)
}

// Check for any obvious type mismatches
fn compare_external_ty_or_true<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    from_path: &vir::ast::Path,
    to_path: &vir::ast::Path,
    ty1: &rustc_middle::ty::Ty<'tcx>,
    ty2: &rustc_middle::ty::Ty<'tcx>,
) -> bool {
    use rustc_middle::ty::{GenericArg, GenericArgKind, Ty};
    // TODO, but low priority, since this is just a check for trusted declarations:
    // finish more cases so as to be more precise and report more mismatches.
    // (Note: we used to try to convert to VIR types and compare,
    // but this led to rustc internal errors, since we didn't have the write param_env_src for ty2)
    let check_t = |t1: &Ty<'tcx>, t2: &Ty<'tcx>| -> bool {
        compare_external_ty_or_true(tcx, verus_items, from_path, to_path, t1, t2)
    };
    let check_ts = |ts1: &[Ty<'tcx>], ts2: &[Ty<'tcx>]| -> bool {
        ts1.len() == ts2.len() && ts1.iter().zip(ts2.iter()).all(|(t1, t2)| check_t(t1, t2))
    };
    let check_args = |args1: &[GenericArg<'tcx>], args2: &[GenericArg<'tcx>]| -> bool {
        if args1.len() != args2.len() {
            return false;
        }
        for (arg1, arg2) in args1.iter().zip(args2.iter()) {
            let ok = match (&arg1.unpack(), &arg2.unpack()) {
                (GenericArgKind::Type(t1), GenericArgKind::Type(t2)) => check_t(t1, t2),
                _ => arg1 == arg2,
            };
            if !ok {
                return false;
            }
        }
        true
    };
    match (ty1.kind(), ty2.kind()) {
        // These cases are complete:
        (TyKind::Bool, _) => ty1 == ty2,
        (TyKind::Uint(_), _) => ty1 == ty2,
        (TyKind::Int(_), _) => ty1 == ty2,
        (TyKind::Char, _) => ty1 == ty2,
        (TyKind::Closure(..), _) => ty1 == ty2,
        (TyKind::Str, _) => ty1 == ty2,
        (TyKind::Never, _) => ty1 == ty2,
        (TyKind::Float(..), _) => ty1 == ty2,
        (TyKind::Param(_), _) => ty1 == ty2,
        (TyKind::Ref(_, t1, m1), TyKind::Ref(_, t2, m2)) => m1 == m2 && check_t(t1, t2),
        (TyKind::Tuple(_), TyKind::Tuple(_)) => check_ts(ty1.tuple_fields(), ty2.tuple_fields()),
        (TyKind::Slice(t1), TyKind::Slice(t2)) => check_t(t1, t2),
        (TyKind::RawPtr(t1, m1), TyKind::RawPtr(t2, m2)) => m1 == m2 && check_t(t1, t2),
        (TyKind::Array(t1, len1), TyKind::Array(t2, len2)) => len1 == len2 && check_t(t1, t2),
        (TyKind::Adt(a1, args1), TyKind::Adt(a2, args2)) => a1 == a2 && check_args(args1, args2),
        (TyKind::Alias(k1, t1), TyKind::Alias(k2, t2)) => {
            if k1 != k2 {
                return false;
            }
            if tcx.associated_item(t1.def_id).name != tcx.associated_item(t2.def_id).name {
                return false;
            }
            if !check_args(&t1.args, &t2.args) {
                return false;
            }
            let trait_def1 = tcx.generics_of(t1.def_id).parent;
            let trait_def2 = tcx.generics_of(t2.def_id).parent;
            match (trait_def1, trait_def2) {
                (None, None) => true,
                (Some(trait_def1), Some(trait_def2)) => {
                    let mut trait_path1 = def_id_to_vir_path(tcx, verus_items, trait_def1);
                    let trait_path2 = def_id_to_vir_path(tcx, verus_items, trait_def2);
                    if trait_path1 == *from_path {
                        trait_path1 = to_path.clone();
                    }
                    trait_path1 == trait_path2
                }
                _ => false,
            }
        }

        // These cases are incomplete and always return true:
        (TyKind::FnDef(..), _) => true,
        (TyKind::Coroutine(..), _) => true,
        (TyKind::CoroutineWitness(..), _) => true,
        (TyKind::Bound(..), _) => true,
        (TyKind::Placeholder(..), _) => true,
        (TyKind::Infer(..), _) => true,
        (TyKind::Error(..), _) => true,
        (TyKind::CoroutineClosure(..), _) => true,
        (TyKind::Pat(..), _) => true,
        (TyKind::Foreign(..), _) => true,
        (TyKind::FnPtr(..), _) => true,
        (TyKind::Dynamic(..), _) => true,

        _ => false,
    }
}

fn compare_external_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    ty1: &rustc_middle::ty::Ty<'tcx>,
    ty2: &rustc_middle::ty::Ty<'tcx>,
    external_trait_from_to: &Option<(vir::ast::Path, vir::ast::Path)>,
) -> bool {
    if let Some((from_path, to_path)) = external_trait_from_to {
        compare_external_ty_or_true(tcx, verus_items, from_path, to_path, ty1, ty2)
    } else {
        ty1 == ty2
    }
}

fn compare_external_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    sig1: &rustc_middle::ty::FnSig<'tcx>,
    sig2: &rustc_middle::ty::FnSig<'tcx>,
    external_trait_from_to: &Option<(vir::ast::Path, vir::ast::Path)>,
) -> Result<bool, VirErr> {
    use rustc_middle::ty::FnSig;
    // Ignore abi and safety for the sake of comparison
    // Useful for rust-intrinsics
    let FnSig { inputs_and_output: io1, c_variadic: c1, safety: _, abi: _ } = sig1;
    let FnSig { inputs_and_output: io2, c_variadic: c2, safety: _, abi: _ } = sig2;
    if io1.len() != io2.len() {
        return Ok(false);
    }
    for (ty1, ty2) in io1.iter().zip(io2.iter()) {
        if !compare_external_ty(tcx, verus_items, &ty1, &ty2, external_trait_from_to) {
            return Ok(false);
        }
    }
    Ok(c1 == c2)
}

pub(crate) fn handle_external_fn<'tcx>(
    ctxt: &Context<'tcx>,
    id: DefId,
    kind: FunctionKind,
    visibility: vir::ast::Visibility,
    sig: &'tcx FnSig<'tcx>,
    // (impl generics, impl def_id)
    self_generics: Option<(&'tcx Generics, DefId)>,
    body_id: &CheckItemFnEither<&BodyId, &[Ident]>,
    mode: Mode,
    vattrs: &VerifierAttrs,
    external_trait_from_to: &Option<(vir::ast::Path, vir::ast::Path)>,
    external_fn_specification_via_external_trait: Option<DefId>,
    external_info: &mut ExternalInfo,
) -> Result<(vir::ast::Path, vir::ast::Visibility, FunctionKind, bool, Safety), VirErr> {
    // This function is the proxy, and we need to look up the actual path.

    let is_builtin_external = matches!(
        external_fn_specification_via_external_trait
            .and_then(|d| ctxt.verus_items.id_to_name.get(&d)),
        Some(VerusItem::External(_))
    );
    if mode != Mode::Exec && !is_builtin_external {
        return err_span(
            sig.span,
            format!("an `assume_specification` declaration cannot be marked `{mode:}`"),
        );
    }

    if vattrs.external_body {
        return err_span(
            sig.span,
            format!("an `assume_specification` declaration cannot be marked `external_body`"),
        );
    }

    if self_generics.is_some() && external_fn_specification_via_external_trait.is_none() {
        return err_span(sig.span, "`assume_specification` declaration not supported here");
    }

    let (external_id, kind) =
        if let Some(external_id) = external_fn_specification_via_external_trait {
            (external_id, kind)
        } else {
            let body_id = match body_id {
                CheckItemFnEither::BodyId(body_id) => body_id,
                _ => {
                    return err_span(
                        sig.span,
                        "assume_specification not supported for trait functions",
                    );
                }
            };
            let body = find_body(ctxt, body_id);
            get_external_def_id(ctxt.tcx, &ctxt.verus_items, id, body_id, body, sig)?
        };
    let external_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, external_id);

    if external_path.krate == Some(Arc::new("builtin".to_string()))
        && &*external_path.last_segment() != "clone"
        && !is_builtin_external
    {
        return err_span(
            sig.span,
            "cannot apply `assume_specification` to Verus builtin functions",
        );
    }

    // The comparison is a little tricky because we could have a situation like this:
    //
    // ctxt.tcx.type_of(id) = EarlyBinder {
    //   value: for<'a, 'b> fn(&'a &'b T) -> &'b T {std_specs::clone::ex_ref_clone::<T>},
    // }
    // substs1 = [
    //   T,
    // ]
    //
    // ctxt.tcx.type_of(external_id) = EarlyBinder {
    //   value: for<'a> fn(&'a &T) -> &T {std::clone::impls::<impl std::clone::Clone for &T>::clone},
    // }
    // substs2 = [
    //   ReEarlyBound(DefId(2:54293 ~ core[739c]::clone::impls::{impl#3}::'_), 0, '_),
    //   T,
    // ]
    //
    // In this case, 'b is early-bound when looking at the external_id and late-bound when
    // looking at the proxy. In order to treat these as 'identical', we have to consider
    // the early-binder and the outermost late-binder together.

    let ty1 = ctxt.tcx.type_of(id).skip_binder();
    let ty2 = ctxt.tcx.type_of(external_id).skip_binder();

    let substs1_early = get_substs_early(ctxt.tcx, ty1, ctxt.tcx.generics_of(id), sig.span)?;
    let substs2_early =
        get_substs_early(ctxt.tcx, ty2, ctxt.tcx.generics_of(external_id), sig.span)?;

    let poly_sig1 = ctxt.tcx.fn_sig(id);
    let poly_sig2 = ctxt.tcx.fn_sig(external_id);

    let Some((substs1_early, substs2_early, substs1_late, substs2_late)) = equalize_substs(
        ctxt.tcx,
        substs1_early,
        substs2_early,
        poly_sig1.skip_binder().bound_vars().len(),
        poly_sig2.skip_binder().bound_vars().len(),
    ) else {
        return err_span(
            sig.span,
            format!(
                "assume_specification requires function type signature to match exactly (got `{ty1:#?}` and `{ty2:#?}`)"
            ),
        );
    };

    let poly_sig1 = poly_sig1.instantiate(ctxt.tcx, substs1_early);
    let poly_sig1 =
        ctxt.tcx.instantiate_bound_regions(poly_sig1, |br| substs1_late[usize::from(br.var)]).0;

    let poly_sig2 = poly_sig2.instantiate(ctxt.tcx, substs2_early);
    let poly_sig2 =
        ctxt.tcx.instantiate_bound_regions(poly_sig2, |br| substs2_late[usize::from(br.var)]).0;

    let poly_sig_eq = compare_external_sig(
        ctxt.tcx,
        &ctxt.verus_items,
        &poly_sig1,
        &poly_sig2,
        &external_trait_from_to,
    )?;
    if !poly_sig_eq {
        return err_span(
            sig.span,
            format!(
                "assume_specification requires function type signature to match exactly (got `{poly_sig1:#?}` and `{poly_sig2:#?}`)"
            ),
        );
    }

    // trait bounds aren't part of the type signature - we have to check those separately
    let mut proxy_preds = all_predicates(ctxt.tcx, id, substs1_early, false);
    let mut external_preds = all_predicates(ctxt.tcx, external_id, substs2_early, true);
    let in_trait = external_fn_specification_via_external_trait.is_some();
    remove_ignored_trait_bounds_from_predicates(
        ctxt,
        in_trait,
        &[ctxt.tcx.parent(external_id), ctxt.tcx.parent(id)],
        None,
        &mut proxy_preds,
    );
    remove_ignored_trait_bounds_from_predicates(
        ctxt,
        in_trait,
        &[ctxt.tcx.parent(external_id)],
        None,
        &mut external_preds,
    );
    // TODO, but low priority, since this is just a check for trusted declarations:
    // predicates_match for external_trait case (would need to rename from_path -> to_path)
    let preds_match = external_trait_from_to.is_some()
        || predicates_match(ctxt.tcx, &proxy_preds, &external_preds);
    if !preds_match {
        let err = err_span_bare(
            sig.span,
            "assume_specification trait bound mismatch")
            .help(format!("assume_specification requires function type signatures to match exactly, ignoring any Destruct trait bounds\n\
          but the proxy function's trait bounds are:\n{}\nthe external function's trait bounds are:\n{}",
          proxy_preds.iter().map(|x| format!("  - {}", x.to_string())).collect::<Vec<_>>().join("\n"),
          external_preds.iter().map(|x| format!("  - {}", x.to_string())).collect::<Vec<_>>().join("\n")));
        return Err(err);
    }

    let external_item_visibility = mk_visibility(ctxt, external_id);
    if !vir::ast_util::is_visible_to_opt(&visibility, &external_item_visibility.restricted_to) {
        return err_span(
            sig.span,
            "an `assume_specification` declaration must be at least as visible as the function it provides a spec for (try writing `pub assume_specification ...`)",
        );
    }

    let has_self_parameter = has_self_parameter(ctxt, external_id);

    if matches!(kind, FunctionKind::ForeignTraitMethodImpl { .. }) {
        external_info.external_fn_specification_trait_method_impls.push((external_id, sig.span));
    }

    let safety = ctxt.tcx.fn_sig(external_id).skip_binder().safety();

    Ok((external_path, external_item_visibility, kind, has_self_parameter, safety))
}

fn get_substs_early<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    generics: &'tcx rustc_middle::ty::Generics,
    span: Span,
) -> Result<GenericArgsRef<'tcx>, VirErr> {
    let substs = match ty.kind() {
        rustc_middle::ty::FnDef(_, substs) => substs,
        _ => {
            crate::internal_err!(span, "expected FnDef")
        }
    };
    if let Some(host_effect_index) = generics.host_effect_index {
        let mut s: Vec<_> = substs.iter().collect();
        s.remove(host_effect_index);
        Ok(tcx.mk_args(&s))
    } else {
        Ok(substs)
    }
}

fn equalize_substs<'tcx>(
    tcx: TyCtxt<'tcx>,
    substs1_early: GenericArgsRef<'tcx>,
    substs2_early: GenericArgsRef<'tcx>,
    num_late1: usize,
    num_late2: usize,
) -> Option<(GenericArgsRef<'tcx>, GenericArgsRef<'tcx>, Vec<Region<'tcx>>, Vec<Region<'tcx>>)> {
    let mut s2 = vec![];
    let mut l1 = vec![];
    let mut l2 = vec![];

    if substs1_early.len() + num_late1 != substs2_early.len() + num_late2 {
        return None;
    }

    let mut reg =
        substs1_early.iter().filter(|g| matches!(g.unpack(), GenericArgKind::Lifetime(_)));
    let mut other =
        substs1_early.iter().filter(|g| !matches!(g.unpack(), GenericArgKind::Lifetime(_)));

    for i in 0..substs2_early.len() {
        match substs2_early[i].unpack() {
            GenericArgKind::Type(_) => {
                let Some(arg) = other.next() else {
                    return None;
                };
                if !matches!(arg.unpack(), GenericArgKind::Type(_)) {
                    return None;
                }
                s2.push(arg);
            }
            GenericArgKind::Const(_) => {
                let Some(arg) = other.next() else {
                    return None;
                };
                if !matches!(arg.unpack(), GenericArgKind::Const(_)) {
                    return None;
                }
                s2.push(arg);
            }
            GenericArgKind::Lifetime(r) => match reg.next() {
                Some(arg) => {
                    s2.push(arg);
                }
                None => {
                    l1.push(r);
                    s2.push(substs2_early[i]);
                }
            },
        }
    }

    if other.next().is_some() {
        return None;
    }

    for arg in reg {
        let GenericArgKind::Lifetime(r) = arg.unpack() else {
            unreachable!();
        };
        l2.push(r);
    }

    while l1.len() < num_late1 {
        let idx = l1.len();
        let region = Region::new_bound(
            tcx,
            rustc_middle::ty::INNERMOST,
            BoundRegion { var: BoundVar::from(idx), kind: BoundRegionKind::BrAnon },
        );
        l1.push(region);
        l2.push(region);
    }

    assert!(l1.len() == num_late1);
    assert!(l2.len() == num_late2);

    Some((substs1_early, tcx.mk_args(&s2), l1, l2))
}

pub enum CheckItemFnEither<A, B> {
    BodyId(A),
    ParamNames(B),
}

fn create_reveal_group<'tcx>(
    ctxt: &Context<'tcx>,
    reveal_groups: Option<&mut Vec<vir::ast::RevealGroup>>,
    name: &Fun,
    visibility: vir::ast::Visibility,
    module_path: &vir::ast::Path,
    vattrs: &VerifierAttrs,
    vir_body: &Option<vir::ast::Expr>,
    span: Span,
) -> Result<(), VirErr> {
    if let Some(body) = vir_body {
        if let vir::ast::ExprX::Block(stmts, None) = &body.x {
            let mut members: Vec<Fun> = Vec::new();
            for stmt in stmts.iter() {
                if let vir::ast::StmtX::Expr(expr) = &stmt.x {
                    if let vir::ast::ExprX::Fuel(f, 1, _is_broadcast_use) = &expr.x {
                        members.push(f.clone());
                        continue;
                    }
                }
                return err_span(span, "reveal_group must consist of reveal statements");
            }
            let broadcast_use_by_default_when_this_crate_is_imported =
                if vattrs.broadcast_use_by_default_when_this_crate_is_imported {
                    Some(ctxt.crate_name.clone())
                } else {
                    None
                };
            let groupx = vir::ast::RevealGroupX {
                name: name.clone(),
                visibility,
                owning_module: Some(module_path.clone()),
                broadcast_use_by_default_when_this_crate_is_imported,
                members: Arc::new(members),
            };
            if let Some(groups) = reveal_groups {
                groups.push(ctxt.spanned_new(span, groupx));
            } else {
                return err_span(span, "reveal_group not allowed here");
            }
            return Ok(());
        }
    }
    err_span(span, "reveal_group must have body")
}

fn make_attributes<'tcx>(
    ctxt: &Context<'tcx>,
    def_id: DefId,
    vattrs: &crate::attributes::VerifierAttrs,
    uses_ghost_blocks: bool,
    hidden: Arc<Vec<Fun>>,
    custom_req_err: Option<String>,
    autospec: Option<Fun>,
    print_zero_args: bool,
    print_as_method: bool,
    safety: Safety,
    span: Span,
) -> Result<vir::ast::FunctionAttrs, VirErr> {
    if vattrs.nonlinear && vattrs.spinoff_prover {
        return err_span(
            span,
            "#[verifier::spinoff_prover] is implied for assert by nonlinear_arith",
        );
    }
    let fattrs = FunctionAttrsX {
        uses_ghost_blocks,
        inline: vattrs.inline,
        hidden,
        custom_req_err,
        no_auto_trigger: vattrs.no_auto_trigger,
        broadcast_forall: vattrs.broadcast_forall,
        broadcast_forall_only: false,
        auto_ext_equal: crate::attributes::get_auto_ext_equal_walk_parents(ctxt.tcx, def_id),
        bit_vector: vattrs.bit_vector,
        autospec,
        atomic: vattrs.atomic,
        integer_ring: vattrs.integer_ring,
        is_decrease_by: vattrs.decreases_by,
        check_recommends: vattrs.check_recommends,
        nonlinear: vattrs.nonlinear,
        spinoff_prover: vattrs.spinoff_prover,
        memoize: vattrs.memoize,
        rlimit: vattrs.rlimit,
        print_zero_args,
        print_as_method,
        prophecy_dependent: vattrs.prophecy_dependent,
        size_of_broadcast_proof: vattrs.size_of_broadcast_proof,
        is_type_invariant_fn: vattrs.type_invariant_fn,
        is_external_body: vattrs.external_body,
        is_unsafe: match safety {
            Safety::Safe => false,
            Safety::Unsafe => true,
        },
    };
    Ok(Arc::new(fattrs))
}

pub(crate) fn fixup_unerased_proxy_path(
    path: &vir::ast::Path,
    span: Span,
) -> Result<vir::ast::Path, VirErr> {
    let id = path.last_segment();
    let prefix = "VERUS_UNERASED_PROXY__";
    if id.starts_with(&prefix) {
        let p = path.pop_segment().push_segment(Arc::new(id[prefix.len()..].to_string()));
        Ok(p)
    } else {
        crate::internal_err!(span, "bad use of unerased_proxy attribute")
    }
}

pub(crate) fn check_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    functions: &mut Vec<vir::ast::Function>,
    reveal_groups: Option<&mut Vec<vir::ast::RevealGroup>>,
    id: DefId,
    kind: FunctionKind,
    visibility: vir::ast::Visibility,
    module_path: &vir::ast::Path,
    attrs: &[Attribute],
    sig: &'tcx FnSig<'tcx>,
    // (impl generics, impl def_id)
    self_generics: Option<(&'tcx Generics, DefId)>,
    generics: &'tcx Generics,
    body_id: CheckItemFnEither<&BodyId, &[Ident]>,
    external_trait: Option<DefId>,
    external_fn_specification_via_external_trait: Option<DefId>,
    external_info: &mut ExternalInfo,
    autoderive_action: Option<&AutomaticDeriveAction>,
) -> Result<Option<Fun>, VirErr> {
    let mut this_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);

    let is_verus_spec = this_path.segments.last().expect("segment.last").starts_with(VERUS_SPEC);

    let vattrs = ctxt.get_verifier_attrs(attrs)?;
    let mode = get_mode(Mode::Exec, attrs);

    if vattrs.encoded_const {
        let fn_sig = ctxt.tcx.fn_sig(id).skip_binder();
        if fn_sig.inputs().skip_binder().len() != 0 {
            return err_span(sig.span, "encoded_const must have 0 arguments");
        }

        let body_id = match body_id {
            CheckItemFnEither::BodyId(body_id) => body_id,
            CheckItemFnEither::ParamNames(_) => {
                crate::internal_err!(sig.span, "encoded_const expected CheckItemFnEither::BodyId");
            }
        };

        let ty = fn_sig.output().skip_binder();
        let typ = mid_ty_to_vir(ctxt.tcx, &ctxt.verus_items, id, sig.span, &ty, false)?;

        let fun = check_item_const_or_static(
            ctxt,
            functions,
            sig.span,
            id,
            visibility,
            module_path,
            attrs,
            &typ,
            body_id,
            false,
        )?;
        return Ok(Some(fun));
    }

    if vattrs.unerased_proxy {
        this_path = fixup_unerased_proxy_path(&this_path, sig.span)?;
    }

    let external_trait_from_to = if let Some(to_trait_id) = external_trait {
        let from_trait_id = ctxt.tcx.parent(id);
        let from_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, from_trait_id);
        let to_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, to_trait_id);
        Some((from_path, to_path))
    } else {
        None
    };

    let (path, proxy, visibility, kind, has_self_param, safety) = if vattrs
        .external_fn_specification
        || external_fn_specification_via_external_trait.is_some()
    {
        if is_verus_spec {
            return err_span(
                sig.span,
                "assume_specification attribute not supported with VERUS_SPEC",
            );
        }

        let (external_path, external_item_visibility, kind, has_self_param, safety) =
            handle_external_fn(
                ctxt,
                id,
                kind,
                visibility,
                sig,
                self_generics,
                &body_id,
                mode,
                &vattrs,
                &external_trait_from_to,
                external_fn_specification_via_external_trait,
                external_info,
            )?;

        let proxy = (*ctxt.spanned_new(sig.span, this_path.clone())).clone();

        (external_path, Some(proxy), external_item_visibility, kind, has_self_param, safety)
    } else {
        // No proxy.
        let has_self_param = has_self_parameter(ctxt, id);
        (this_path.clone(), None, visibility, kind, has_self_param, sig.header.safety)
    };

    let name = Arc::new(FunX { path: path.clone() });

    let self_typ_params = if let Some((cg, impl_def_id)) = self_generics {
        Some(check_generics_bounds_no_polarity(
            ctxt.tcx,
            &ctxt.verus_items,
            cg.span,
            Some(cg),
            impl_def_id,
            Some(&mut *ctxt.diagnostics.borrow_mut()),
        )?)
    } else {
        None
    };

    let fn_sig = ctxt.tcx.fn_sig(id);
    // REVIEW: rustc docs refer to skip_binder as "dangerous"
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs().skip_binder();

    let ret_typ_mode = match sig {
        FnSig {
            header: FnHeader { safety, constness: _, asyncness: _, abi: _ },
            decl,
            span: _,
        } => {
            if mode != Mode::Exec && safety == &Safety::Unsafe {
                return err_span(
                    sig.span,
                    format!("'unsafe' only makes sense on exec-mode functions"),
                );
            }
            check_fn_decl(sig.span, ctxt, id, decl, attrs, mode, fn_sig.output().skip_binder())?
        }
    };

    let (sig_typ_params, sig_typ_bounds) = check_generics_bounds_no_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        generics.span,
        Some(generics),
        id,
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;

    let params: Vec<(VarIdent, Span, Option<HirId>, bool)> = match body_id {
        CheckItemFnEither::BodyId(body_id) => {
            let body = find_body(ctxt, body_id);
            let Body { params, value: _ } = body;
            let mut ps = Vec::new();
            for Param { hir_id, pat, ty_span: _, span } in params.iter() {
                let (is_mut_var, name) = pat_to_mut_var(pat)?;
                // is_mut_var: means a parameter is like `mut x: X`
                // is_mut: means a parameter is like `x: &mut X` or `x: Tracked<&mut X>`
                ps.push((name, *span, Some(*hir_id), is_mut_var));
            }
            ps
        }
        CheckItemFnEither::ParamNames(params) => {
            params.iter().map(|p| (no_body_param_to_var(p), p.span, None, false)).collect()
        }
    };

    let mut vir_mut_params: Vec<(vir::ast::Param, Option<Mode>)> = Vec::new();
    let mut vir_params: Vec<(vir::ast::Param, Option<Mode>)> = Vec::new();
    let mut mut_params_redecl: Vec<vir::ast::Stmt> = Vec::new();
    assert!(params.len() == inputs.len());
    for ((name, span, hir_id, is_mut_var), input) in params.into_iter().zip(inputs.iter()) {
        let param_mode = if let Some(hir_id) = hir_id {
            get_var_mode(mode, ctxt.tcx.hir().attrs(hir_id))
        } else {
            assert!(matches!(kind, FunctionKind::TraitMethodDecl { .. }));
            // This case is for a trait method declaration,
            // where the mode will later be overridden by the separate spec method anyway:
            Mode::Exec
        };
        let is_ref_mut = is_mut_ty(ctxt, *input);
        if is_ref_mut.is_some() && mode == Mode::Spec {
            return err_span(span, format!("&mut parameter not allowed for spec functions"));
        }

        let typ = {
            let typ = mid_ty_to_vir(
                ctxt.tcx,
                &ctxt.verus_items,
                id,
                span,
                is_ref_mut.map(|(t, _)| t).unwrap_or(input),
                false,
            )?;
            if let Some((_, decoration)) = is_ref_mut.and_then(|(_, w)| w) {
                Arc::new(TypX::Decorate(decoration, None, typ))
            } else {
                typ
            }
        };

        // is_mut: means a parameter is like `x: &mut X` or `x: Tracked<&mut X>`
        let is_mut = is_ref_mut.is_some();

        let vir_param = ctxt.spanned_new(
            span,
            ParamX {
                name: name.clone(),
                typ: typ.clone(),
                mode: param_mode,
                is_mut,
                unwrapped_info: None,
            },
        );
        if is_mut_var {
            if mode == Mode::Spec {
                return err_span(span, format!("mut argument not allowed for spec functions"));
            }
            if is_mut {
                // REVIEW
                // For all mut params, we introduce a new variable that shadows the original mut
                // param and assign the value of the param to the new variable. This does not
                // work properly when the type of the param is a mutable reference because
                // declaring and assigning to a variable of type `&mut T` is not implemented yet.
                unsupported_err!(span, "mut parameters of &mut types")
            }
            vir_mut_params.push((
                vir_param.clone(),
                is_ref_mut.map(|(_, m)| m).flatten().map(|(mode, _)| mode),
            ));
            let new_binding_pat = ctxt.spanned_typed_new(
                span,
                &typ,
                vir::ast::PatternX::Var { name: name.clone(), mutable: true },
            );
            let new_init_expr =
                ctxt.spanned_typed_new(span, &typ, vir::ast::ExprX::Var(name.clone()));
            if let Some(hir_id) = hir_id {
                ctxt.erasure_info.borrow_mut().hir_vir_ids.push((hir_id, new_binding_pat.span.id));
                ctxt.erasure_info.borrow_mut().hir_vir_ids.push((hir_id, new_init_expr.span.id));
            }
            let redecl = ctxt.spanned_new(
                span,
                vir::ast::StmtX::Decl {
                    pattern: new_binding_pat,
                    mode: Some(mode),
                    init: Some(new_init_expr),
                    els: None,
                },
            );
            mut_params_redecl.push(redecl);
        }
        vir_params.push((vir_param, is_ref_mut.map(|(_, m)| m).flatten().map(|(mode, _)| mode)));
    }

    let n_params = vir_params.len();

    let (vir_body, header, body_hir_id) = match body_id {
        CheckItemFnEither::BodyId(body_id) => {
            let body = find_body(ctxt, body_id);
            let external_body = vattrs.external_body || vattrs.external_fn_specification;
            let mut vir_body = body_to_vir(ctxt, id, body_id, body, mode, external_body)?;
            let header = vir::headers::read_header(&mut vir_body)?;
            (Some(vir_body), header, Some(body.value.hir_id))
        }
        CheckItemFnEither::ParamNames(_params) => {
            let header = vir::headers::read_header_block(&mut vec![])?;
            (None, header, None)
        }
    };

    if vattrs.reveal_group {
        create_reveal_group(
            ctxt,
            reveal_groups,
            &name,
            visibility,
            module_path,
            &vattrs,
            &vir_body,
            sig.span,
        )?;
        return Ok(None);
    }

    match (&kind, header.no_method_body, is_verus_spec, vir_body.is_some()) {
        (FunctionKind::TraitMethodDecl { .. }, false, false, _) => {}
        (FunctionKind::TraitMethodDecl { .. }, true, true, _) => {}
        (FunctionKind::TraitMethodDecl { .. }, false, true, _) => {
            return err_span(
                sig.span,
                "trait method declaration body must end with call to no_method_body()",
            );
        }
        (_, _, true, _) => {
            return err_span(
                sig.span,
                format!("{VERUS_SPEC} can only appear in trait method declarations"),
            );
        }
        (_, false, false, true) => {}
        (_, false, false, false) => {
            return err_span(sig.span, "function must have a body");
        }
        (_, true, _, _) => {
            return err_span(
                sig.span,
                "no_method_body can only appear in trait method declarations",
            );
        }
    }
    if mode == Mode::Spec && (header.require.len() + header.ensure.len()) > 0 {
        return err_span(sig.span, "spec functions cannot have requires/ensures");
    }
    if mode == Mode::Spec && header.returns.is_some() {
        return err_span(sig.span, "spec functions cannot have `returns` clause");
    }
    if mode != Mode::Spec && header.recommend.len() > 0 {
        return err_span(sig.span, "non-spec functions cannot have recommends");
    }
    if mode != Mode::Exec && vattrs.external_fn_specification {
        return err_span(sig.span, "assume_specification should be 'exec'");
    }
    if header.ensure.len() > 0 {
        match (&header.ensure_id_typ, ret_typ_mode.as_ref()) {
            (None, None) => {}
            (None, Some(_)) => {
                return err_span(
                    sig.span,
                    "the return value must be named in a function with an ensures clause",
                );
            }
            (Some(_), None) => {
                return err_span(
                    sig.span,
                    "unexpected named return value for function with default return",
                );
            }
            (Some((_, typ)), Some((ret_typ, _))) => {
                if !vir::ast_util::types_equal(&typ, &ret_typ) {
                    return err_span(
                        sig.span,
                        format!(
                            "return type is {:?}, but ensures expects type {:?}",
                            &ret_typ, &typ
                        ),
                    );
                }
            }
        }
    }

    use vir::ast::UnwrapParameter;
    let mut all_param_names: Vec<vir::ast::VarIdent> = Vec::new();
    let mut all_param_name_set: HashSet<vir::ast::VarIdent> = HashSet::new();
    let mut unwrap_param_map: HashMap<vir::ast::VarIdent, UnwrapParameter> = HashMap::new();
    for unwrap in header.unwrap_parameters.iter() {
        all_param_names.push(unwrap.inner_name.clone());
        unwrap_param_map.insert(unwrap.outer_name.clone(), unwrap.clone());
    }
    for (param, unwrap_mut) in vir_params.iter_mut() {
        all_param_names.push(param.x.name.clone());
        if let Some(unwrap) = unwrap_param_map.get(&param.x.name) {
            if mode != Mode::Exec {
                return err_span(
                    sig.span,
                    "only exec functions can use Ghost(x) or Tracked(x) parameters",
                );
            }
            let mut paramx = param.x.clone();
            paramx.name = unwrap.inner_name.clone();
            paramx.unwrapped_info = Some((unwrap.mode, unwrap.outer_name.clone()));
            *param = vir::def::Spanned::new(param.span.clone(), paramx);
        } else if vir_body.is_some() && unwrap_mut.is_some() {
            let param_user_name = vir::def::user_local_name(&param.x.name);
            return Err(vir::messages::error(
                &param.span,
                format!("parameter {} must be unwrapped", param_user_name),
            )
            .help(format!(
                "use Tracked({}): Tracked<&mut T> to unwrap the tracked argument",
                param_user_name
            )));
        }
    }
    for name in all_param_names.iter() {
        if all_param_name_set.contains(name) {
            return err_span(sig.span, format!("duplicate parameter name {}", name));
        }
        all_param_name_set.insert(name.clone());
    }
    let params: vir::ast::Params = Arc::new(vir_params.into_iter().map(|(p, _)| p).collect());

    let (ret_name, ret_typ, ret_mode) = match (header.ensure_id_typ, ret_typ_mode) {
        (None, None) => (air_unique_var(RETURN_VALUE), unit_typ(), mode),
        (None, Some((typ, mode))) => (air_unique_var(RETURN_VALUE), typ, mode),
        (Some((x, _)), Some((typ, mode))) => (x, typ, mode),
        _ => panic!("internal error: ret_typ"),
    };
    let ret_span = sig.decl.output.span();
    let ret = ctxt.spanned_new(
        ret_span,
        ParamX {
            name: ret_name,
            typ: ret_typ,
            mode: ret_mode,
            is_mut: false,
            unwrapped_info: None,
        },
    );
    let (typ_params, typ_bounds) = {
        let mut typ_params: Vec<vir::ast::Ident> = Vec::new();
        let mut typ_bounds: Vec<vir::ast::GenericBound> = Vec::new();
        if let FunctionKind::TraitMethodDecl { .. } = kind {
            if !vattrs.external_fn_specification {
                typ_params.push(vir::def::trait_self_type_param());
            }
        }
        if let Some((self_typ_params, self_typ_bounds)) = self_typ_params {
            typ_params.append(&mut (*self_typ_params).clone());
            typ_bounds.append(&mut (*self_typ_bounds).clone());
        }
        typ_params.extend_from_slice(&sig_typ_params[..]);
        typ_bounds.extend_from_slice(&sig_typ_bounds[..]);
        let typ_params = Arc::new(typ_params);
        let mut typ_bounds = Arc::new(typ_bounds);

        if let Some((from_path, to_path)) = &external_trait_from_to {
            typ_bounds = vir::traits::rewrite_external_bounds(from_path, to_path, &typ_bounds);
        }
        (typ_params, typ_bounds)
    };

    let body = if vattrs.external_body || vattrs.external_fn_specification || header.no_method_body
    {
        None
    } else {
        vir_body
    };
    let open_closed_present =
        vattrs.publish == Some(AttrPublish::Open) || vattrs.publish == Some(AttrPublish::Closed);
    match kind {
        FunctionKind::TraitMethodImpl { .. } | FunctionKind::TraitMethodDecl { .. }
            if body.is_some() =>
        {
            if mode == Mode::Spec
                && visibility.restricted_to.as_ref() != Some(module_path)
                && body.is_some()
                && !open_closed_present
            {
                return err_span(
                    sig.span,
                    "open/closed is required for implementations of non-private traits",
                );
            }
        }
        FunctionKind::TraitMethodDecl { .. } => {
            if mode == Mode::Spec && open_closed_present && body.is_none() {
                return err_span(
                    sig.span,
                    "trait function declarations cannot be open or closed, as they don't have a body",
                );
            }
        }
        _ => (),
    }
    let autospec = vattrs.autospec.clone().map(|method_name| {
        let this_path =
            crate::rust_to_vir_base::def_id_to_vir_path_ignoring_diagnostic_rename(ctxt.tcx, id);
        let path = autospec_fun(&this_path, method_name.clone());
        Arc::new(FunX { path })
    });

    if vattrs.nonlinear && vattrs.spinoff_prover {
        return err_span(
            sig.span,
            "#[verifier::spinoff_prover] is implied for assert by nonlinear_arith",
        );
    }

    if vattrs.type_invariant_fn {
        check_generics_for_invariant_fn(ctxt.tcx, id, self_generics, generics, sig.span)?;
    }

    let fattrs = make_attributes(
        ctxt,
        id,
        &vattrs,
        vattrs.verus_macro,
        Arc::new(header.hidden),
        vattrs.custom_req_err.clone(),
        autospec,
        n_params == 0,
        has_self_param,
        safety,
        sig.span,
    )?;

    let mut recommend: Vec<vir::ast::Expr> = (*header.recommend).clone();
    if let Some(decrease_when) = &header.decrease_when {
        // Automatically add decrease_when to recommends
        recommend.push(decrease_when.clone());
    }

    // This function is marked 'private' at the source level to prevent the user from
    // calling it. But we translate things to point to it internally, so we need to
    // mark it non-private in order to avoid errors down the line.
    let mut visibility = visibility;
    for b in [true, false] {
        if path == vir::def::nonstatic_call_path(&Some(ctxt.vstd_crate_name.clone()), b) {
            visibility.restricted_to = None;
        }
    }

    // Given a func named 'f' which has mut parameters 'x_0', ..., 'x_n' and body
    // 'f_body', we rewrite it to a function without mut params and body
    // 'let mut x_0 = x_0; ...; let mut x_n = x_n; f_body'.
    let body_with_mut_redecls = if vir_mut_params.is_empty() {
        body
    } else {
        body.map(move |body| {
            SpannedTyped::new(
                &body.span.clone(),
                &body.typ.clone(),
                vir::ast::ExprX::Block(Arc::new(mut_params_redecl), Some(body)),
            )
        })
    };

    // Note: ens_has_return isn't final; it may need to be changed later to make
    // sure it's in sync for trait method impls and trait method decls.
    // See `fixup_ens_has_return_for_trait_method_impls`.
    let (ensure, ens_has_return) = clean_ensures_for_unit_return(&ret, &header.ensure);

    let (body_visibility, opaqueness) = get_body_visibility_and_fuel(
        sig.span,
        &visibility,
        vattrs.publish,
        &header.open_visibility_qualifier,
        vattrs.opaque,
        vattrs.opaque_outside_module,
        mode,
        module_path,
        body_with_mut_redecls.is_some(),
    )?;

    let mut func = FunctionX {
        name: name.clone(),
        proxy,
        kind,
        visibility,
        body_visibility,
        opaqueness,
        owning_module: Some(module_path.clone()),
        mode,
        typ_params,
        typ_bounds,
        params,
        ret,
        ens_has_return,
        require: if mode == Mode::Spec { Arc::new(recommend) } else { header.require },
        returns: header.returns,
        ensure: ensure,
        decrease: header.decrease,
        decrease_when: header.decrease_when,
        decrease_by: header.decrease_by,
        fndef_axioms: None,
        mask_spec: header.invariant_mask,
        unwind_spec: header.unwind_spec,
        item_kind: ItemKind::Function,
        attrs: fattrs,
        body: body_with_mut_redecls,
        extra_dependencies: header.extra_dependencies,
    };

    if vattrs.external_fn_specification {
        func = fix_external_fn_specification_trait_method_decl_typs(sig.span, func)?;
    }
    if let Some(action) = autoderive_action {
        if let Some(body_hir_id) = body_hir_id {
            crate::automatic_derive::modify_derived_item(
                ctxt,
                sig.span,
                body_hir_id,
                action,
                &mut func,
            )?;
        }
    }
    let function = ctxt.spanned_new(sig.span, func);
    let function = if let Some((from_path, to_path)) = &external_trait_from_to {
        vir::traits::rewrite_external_function(from_path, to_path, &function)
    } else {
        function
    };
    functions.push(function);
    if is_verus_spec { Ok(None) } else { Ok(Some(name)) }
}

fn has_self_parameter<'tcx>(ctxt: &Context<'tcx>, id: DefId) -> bool {
    if let Some(assoc_item) = ctxt.tcx.opt_associated_item(id) {
        assoc_item.fn_has_self_parameter
    } else {
        false
    }
}

fn fix_external_fn_specification_trait_method_decl_typs(
    span: Span,
    func: FunctionX,
) -> Result<FunctionX, VirErr> {
    if matches!(func.kind, FunctionKind::ForeignTraitMethodImpl { .. }) {
        // There's nothing to do here. It's fine if the param names of
        // a traim method impl don't line up with the type params of the impl.
        Ok(func)
    } else if let FunctionKind::TraitMethodDecl { .. } = &func.kind {
        let FunctionX {
            name,
            proxy,
            kind,
            visibility,
            body_visibility,
            opaqueness,
            owning_module,
            mode,
            typ_params,
            mut typ_bounds,
            mut params,
            mut ret,
            ens_has_return,
            require,
            ensure,
            returns,
            decrease,
            decrease_when,
            decrease_by,
            fndef_axioms,
            mask_spec,
            unwind_spec,
            item_kind,
            attrs,
            body,
            extra_dependencies,
        } = func;

        unsupported_err_unless!(typ_params.len() == 1, span, "type params");

        let mut typ_substs = HashMap::<Arc<String>, Typ>::new();
        typ_substs.insert(
            typ_params[0].clone(),
            Arc::new(TypX::TypParam(vir::def::trait_self_type_param())),
        );
        typ_bounds = Arc::new(
            typ_bounds
                .iter()
                .map(|typ_bound| {
                    let gbx = match &**typ_bound {
                        GenericBoundX::Trait(path, typs) => {
                            let typs = typs.iter().map(|typ| subst_typ(&typ_substs, typ)).collect();
                            GenericBoundX::Trait(path.clone(), Arc::new(typs))
                        }
                        GenericBoundX::TypEquality(path, typs, name, typ) => {
                            let typs = typs.iter().map(|typ| subst_typ(&typ_substs, typ)).collect();
                            let typ = subst_typ(&typ_substs, typ);
                            GenericBoundX::TypEquality(
                                path.clone(),
                                Arc::new(typs),
                                name.clone(),
                                typ,
                            )
                        }
                        GenericBoundX::ConstTyp(t1, t2) => {
                            let t1 = subst_typ(&typ_substs, t1);
                            let t2 = subst_typ(&typ_substs, t2);
                            GenericBoundX::ConstTyp(t1, t2)
                        }
                    };
                    Arc::new(gbx)
                })
                .collect(),
        );

        let mut typ_params = (*typ_params).clone();
        typ_params[0] = vir::def::trait_self_type_param();
        let typ_params = Arc::new(typ_params);

        //params = params.iter().map(|p| p.new_x(p.x.new_a(subst_typ(&typ_substs, &p.a)))).collect();
        //ret = ret.new_x(ret.x.new_a(&typ_substs, &ret.a));
        params = Arc::new(
            params
                .iter()
                .map(|p| {
                    p.new_x(vir::ast::ParamX {
                        typ: subst_typ(&typ_substs, &p.x.typ),
                        ..p.x.clone()
                    })
                })
                .collect(),
        );
        ret = ret
            .new_x(vir::ast::ParamX { typ: subst_typ(&typ_substs, &ret.x.typ), ..ret.x.clone() });

        unsupported_err_unless!(require.len() == 0, span, "requires clauses");
        unsupported_err_unless!(ensure.len() == 0, span, "ensures clauses");
        unsupported_err_unless!(returns.is_some(), span, "returns clauses");
        unsupported_err_unless!(decrease.len() == 0, span, "decreases clauses");
        unsupported_err_unless!(decrease_when.is_none(), span, "decreases_when clauses");
        unsupported_err_unless!(decrease_by.is_none(), span, "decreases_by clauses");
        unsupported_err_unless!(!attrs.broadcast_forall, span, "broadcast_forall");
        unsupported_err_unless!(matches!(mask_spec, None), span, "opens_invariants");
        unsupported_err_unless!(matches!(unwind_spec, None), span, "unwind");
        unsupported_err_unless!(body.is_none(), span, "opens_invariants");

        Ok(FunctionX {
            name,
            proxy,
            kind,
            visibility,
            body_visibility,
            opaqueness,
            owning_module,
            mode,
            typ_params,
            typ_bounds,
            params,
            ret,
            ens_has_return,
            require,
            ensure,
            returns,
            decrease,
            decrease_when,
            decrease_by,
            fndef_axioms,
            mask_spec,
            unwind_spec,
            item_kind,
            attrs,
            body,
            extra_dependencies,
        })
    } else {
        Ok(func)
    }
}

fn check_generics_for_invariant_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: DefId,
    self_generics: Option<(&'tcx Generics, DefId)>,
    generics: &'tcx Generics<'tcx>,
    span: Span,
) -> Result<(), VirErr> {
    let fn_sig = tcx.fn_sig(id);
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs().skip_binder();

    if inputs.len() != 1 {
        return err_span(span, "#[verifier::type_invariant]: expected 1 parameter");
    }
    if tcx.trait_of_item(id).is_some() {
        return err_span(span, "#[verifier::type_invariant] function cannot be a trait function");
    }

    let ty = crate::rust_to_vir_base::ty_remove_references(&inputs[0]);

    match ty.kind() {
        TyKind::Adt(AdtDef(adt_def_data), substs) => {
            let adt_def = tcx.adt_def(adt_def_data.did);
            if adt_def.is_union() {
                return err_span(
                    span,
                    "not supported: #[verifier::type_invariant] for union types",
                );
            }
            assert!(adt_def.is_struct() || adt_def.is_enum());
            crate::rust_to_vir_base::check_item_external_generics(
                self_generics,
                generics,
                true,
                substs,
                false,
                span,
            )?;

            let datatype_predicates = adt_def.predicates(tcx);
            let func_predicates = tcx.predicates_of(id);
            let preds1 = datatype_predicates.instantiate(tcx, substs).predicates;
            let preds2 = func_predicates.instantiate(tcx, substs).predicates;
            // The 'outlives' predicates don't always line up; I don't know why.
            // But they don't matter for the purpose of this check, so filter them out here.
            let preds1 = preds1
                .into_iter()
                .filter(|p| {
                    !matches!(
                        p.kind().skip_binder(),
                        ClauseKind::RegionOutlives(..) | ClauseKind::TypeOutlives(..)
                    )
                })
                .collect();
            let preds2 = preds2
                .into_iter()
                .filter(|p| {
                    !matches!(
                        p.kind().skip_binder(),
                        ClauseKind::RegionOutlives(..) | ClauseKind::TypeOutlives(..)
                    )
                })
                .collect();
            let preds_match = crate::rust_to_vir_func::predicates_match(tcx, &preds1, &preds2);
            if !preds_match {
                println!("datatype_predicates: {:#?}", preds1);
                println!("func_predicates: {:#?}", preds2);
                return err_span(span, "#[verifier::type_invariant]: trait bounds should match");
            }

            Ok(())
        }
        _ => {
            return err_span(
                span,
                "type_invariant: expected parameter to be a datatype declared in this crate",
            );
        }
    }
}

// &mut T => Some(T, None)
// Ghost<&mut T> => Some(T, Some(Spec))
// Tracked<&mut T> => Some(T, Some(Proof))
// _ => None
fn is_mut_ty<'tcx>(
    ctxt: &Context<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<(&'tcx rustc_middle::ty::Ty<'tcx>, Option<(Mode, TypDecoration)>)> {
    use rustc_middle::ty::*;
    match ty.kind() {
        TyKind::Ref(_, tys, rustc_ast::Mutability::Mut) => Some((tys, None)),
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let did = adt_def_data.did;
            let verus_item = ctxt.verus_items.id_to_name.get(&did);
            if let Some(VerusItem::BuiltinType(
                bt @ (BuiltinTypeItem::Ghost | BuiltinTypeItem::Tracked),
            )) = verus_item
            {
                assert_eq!(args.len(), 1);
                if let GenericArgKind::Type(t) = args[0].unpack() {
                    if let Some((inner, None)) = is_mut_ty(ctxt, t) {
                        let mode_and_decoration = match bt {
                            BuiltinTypeItem::Ghost => (Mode::Spec, TypDecoration::Ghost),
                            BuiltinTypeItem::Tracked => (Mode::Proof, TypDecoration::Tracked),
                            _ => unreachable!(),
                        };
                        return Some((inner, Some(mode_and_decoration)));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

pub(crate) fn remove_ignored_trait_bounds_from_predicates<'tcx>(
    ctxt: &Context<'tcx>,
    in_trait: bool,
    trait_ids: &[DefId],
    ex_trait_assoc: Option<rustc_middle::ty::GenericArg<'tcx>>,
    preds: &mut Vec<Clause<'tcx>>,
) {
    use rustc_middle::ty;
    use rustc_middle::ty::{ConstKind, ScalarInt, ValTree};
    let tcx = ctxt.tcx;
    preds.retain(|p: &Clause<'tcx>| match p.kind().skip_binder() {
        rustc_middle::ty::ClauseKind::<'tcx>::Trait(tp) => {
            if in_trait && trait_ids.contains(&tp.trait_ref.def_id) && tp.trait_ref.args.len() >= 1
            {
                if let GenericArgKind::Type(ty) = tp.trait_ref.args[0].unpack() {
                    match ty.kind() {
                        // ignore Self: T bound for trait T
                        ty::TyKind::Param(param)
                            if param.name == rustc_span::symbol::kw::SelfUpper =>
                        {
                            false
                        }
                        ty::TyKind::Alias(_, _) if Some(tp.trait_ref.args[0]) == ex_trait_assoc => {
                            false
                        }
                        _ => true,
                    }
                } else {
                    true
                }
            } else {
                use crate::verus_items::{BuiltinTraitItem, RustItem, VerusItem};
                let rust_item = crate::verus_items::get_rust_item(tcx, tp.trait_ref.def_id);
                let verus_item = ctxt.verus_items.id_to_name.get(&tp.trait_ref.def_id);
                match rust_item {
                    Some(RustItem::Destruct) => false, // https://github.com/verus-lang/verus/pull/726
                    Some(RustItem::SliceSealed) => false, // https://github.com/verus-lang/verus/pull/1434
                    _ => match verus_item {
                        Some(VerusItem::BuiltinTrait(BuiltinTraitItem::Sealed)) => false,
                        _ => true,
                    },
                }
            }
        }
        rustc_middle::ty::ClauseKind::<'tcx>::ConstArgHasType(cnst, _ty) => {
            if let ConstKind::Value(ty, ValTree::Leaf(ScalarInt::TRUE)) = cnst.kind() {
                match ty.kind() {
                    TyKind::Bool => false,
                    _ => true,
                }
            } else {
                false
            }
        }
        _ => true,
    });
}

pub(crate) fn predicates_match<'tcx>(
    tcx: TyCtxt<'tcx>,
    preds1: &Vec<Clause<'tcx>>,
    preds2: &Vec<Clause<'tcx>>,
) -> bool {
    if preds1.len() != preds2.len() {
        return false;
    }

    // Note: it might actually be impossible for the below check to fail?
    // Since we already passed Rust's typechecking, one of the predicate lists
    // has to be a subset of the other. But we just checked they're the same size.
    // So they have to be equal.
    //
    // Regardless, it makes sense to keep this as a sanity check.

    let preds1 = preds1.iter().map(|p| tcx.anonymize_bound_vars(p.kind()));
    let mut preds2: Vec<_> = preds2.iter().map(|p| tcx.anonymize_bound_vars(p.kind())).collect();

    for p1 in preds1 {
        let mut found = false;
        for i in 0..preds2.len() {
            if p1 == preds2[i] {
                preds2.remove(i);
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    return true;
}

fn all_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: rustc_span::def_id::DefId,
    substs: GenericArgsRef<'tcx>,
    preliminarily_try_to_process_and_eliminate_trait_aliases: bool,
) -> Vec<Clause<'tcx>> {
    let substs = if let Some(index) = tcx.generics_of(id).host_effect_index {
        let b = rustc_middle::ty::Const::from_bool(tcx, true);
        let mut s: Vec<_> = substs.iter().collect();
        s.insert(index, b.into());
        tcx.mk_args(&s)
    } else {
        substs
    };
    let mut trait_alias_clauses: Vec<Clause<'tcx>> = Vec::new();
    let preds = tcx.predicates_of(id);
    if preliminarily_try_to_process_and_eliminate_trait_aliases {
        // raw_ptr.rs uses external_fn_specification for functions with core::ptr::Thin bounds,
        // where core::ptr::Thin is a trait alias (an experimental Rust feature)
        // to core::ptr::Pointee<Metadata = ()>
        // We don't support trait aliases yet.
        // However, to get this case to work, we attempt to expand away trait aliases unto
        // their underlying traits here.
        // This is not fully general and probably doesn't yet work for parameterized trait aliases.
        for (p, _) in preds.predicates {
            match p.kind().skip_binder() {
                rustc_middle::ty::ClauseKind::<'tcx>::Trait(tp) => {
                    if tcx.trait_is_alias(tp.trait_ref.def_id) {
                        let preds = tcx.predicates_of(tp.trait_ref.def_id);
                        trait_alias_clauses
                            .extend(preds.instantiate(tcx, substs).into_iter().map(|(p, _)| p));
                    }
                }
                _ => {}
            }
        }
    }
    let preds = preds.instantiate(tcx, substs);
    let mut clauses = preds.predicates;
    if preliminarily_try_to_process_and_eliminate_trait_aliases {
        clauses.retain(|clause| match clause.kind().skip_binder() {
            rustc_middle::ty::ClauseKind::<'tcx>::Trait(tp) => {
                !tcx.trait_is_alias(tp.trait_ref.def_id)
            }
            _ => true,
        });
    }
    clauses.extend(trait_alias_clauses);
    clauses
}

pub(crate) fn get_external_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    proxy_fun_id: DefId,
    body_id: &BodyId,
    body: &Body<'tcx>,
    sig: &'tcx FnSig<'tcx>,
) -> Result<(rustc_span::def_id::DefId, FunctionKind), VirErr> {
    let err = || {
        err_span(
            sig.span,
            format!("assume_specification encoding error: body should end in call expression"),
        )
    };

    // Get the 'body' of this function (skipping over header and unsafe-block if necessary)
    let expr = match &body.value.kind {
        ExprKind::Block(block_body, _) => match &block_body.expr {
            Some(body_value) => body_value,
            None => {
                return err();
            }
        },
        _ => &body.value,
    };
    let expr = match &expr.kind {
        ExprKind::Block(block_body, _) => match &block_body.expr {
            Some(body_value) => body_value,
            None => {
                return err();
            }
        },
        _ => &expr,
    };

    let types = body_id_to_types(tcx, body_id);

    let (external_id, hir_id) = match &expr.kind {
        ExprKind::Call(fun, _args) => match &fun.kind {
            ExprKind::Path(qpath) => {
                let def = types.qpath_res(&qpath, fun.hir_id);
                match def {
                    rustc_hir::def::Res::Def(_, def_id) => {
                        // We don't need to check the args match or anything,
                        // the type signature check done by the handle_external_fn
                        // is sufficient.
                        (def_id, fun.hir_id)
                    }
                    _ => {
                        return err();
                    }
                }
            }
            _ => {
                return err();
            }
        },
        ExprKind::MethodCall(_name_and_generics, _receiver, _other_args, _fn_span) => {
            // TODO maybe deprecate this; it isn't used with the new
            // 'assume_specification' style
            let def_id =
                types.type_dependent_def_id(expr.hir_id).expect("def id of the method definition");
            (def_id, expr.hir_id)
        }
        _ => {
            return err();
        }
    };

    if let Some(trait_def_id) = tcx.trait_of_item(external_id) {
        // If this is a trait function, then the DefId we have right now points to
        // function definition in the trait definition.
        // We want to resolve to a specific definition in a trait implementation.
        let node_substs = types.node_args(hir_id);
        let param_env = tcx.param_env(proxy_fun_id);
        let normalized_substs = tcx.normalize_erasing_regions(param_env, node_substs);
        let trait_ref = TraitRef::new(tcx, trait_def_id, normalized_substs);
        let candidate = tcx.codegen_select_candidate((param_env, trait_ref));

        match candidate {
            Ok(ImplSource::UserDefined(u)) => {
                let impl_def_id = u.impl_def_id;
                let trait_ref = tcx.impl_trait_ref(impl_def_id).expect("impl_trait_ref");

                let inst = rustc_middle::ty::Instance::try_resolve(
                    tcx,
                    param_env,
                    external_id,
                    normalized_substs,
                );
                let Ok(inst) = inst else {
                    return err_span(
                        sig.span,
                        "Verus Internal Error: handling assume_specification, resolve failed",
                    );
                };
                let Some(inst) = inst else {
                    return err_span(
                        sig.span,
                        "assume_specification cannot be used to specify generic specifications of trait methods; consider using external_trait_specification instead",
                    );
                };
                let rustc_middle::ty::InstanceKind::Item(did) = inst.def else {
                    return err_span(
                        sig.span,
                        "Verus Internal Error: handling assume_specification, resolve failed",
                    );
                };

                let is_default = tcx.impl_of_method(did).is_none();
                unsupported_err_unless!(
                    !is_default,
                    sig.span,
                    "assume_specification for a provided trait method"
                );

                let trait_path = def_id_to_vir_path(tcx, verus_items, trait_def_id);

                let mut types: Vec<Typ> = Vec::new();
                for ty in trait_ref.instantiate(tcx, u.args).args.types() {
                    types.push(mid_ty_to_vir(tcx, &verus_items, did, sig.span, &ty, false)?);
                }

                let kind = FunctionKind::ForeignTraitMethodImpl {
                    method: Arc::new(FunX {
                        path: def_id_to_vir_path(tcx, verus_items, external_id),
                    }),
                    impl_path: def_id_to_vir_path(tcx, verus_items, impl_def_id),
                    trait_path: trait_path,
                    trait_typ_args: Arc::new(types),
                };
                return Ok((did, kind));
            }
            Ok(ImplSource::Builtin(b, _)) => {
                return err_span(
                    sig.span,
                    format!(
                        "Verus assume_specification does not support ImplSource::Builtin '{:?}'",
                        b
                    ),
                );
            }
            Ok(ImplSource::Param(_)) => {
                return err_span(
                    sig.span,
                    "assume_specification not supported for unresolved trait functions",
                );
            }
            Err(_) => {
                crate::internal_err!(sig.span, "expected InstanceDef::Item")
            }
        }
    } else {
        Ok((external_id, FunctionKind::Static))
    }
}

pub(crate) fn check_item_const_or_static<'tcx>(
    ctxt: &Context<'tcx>,
    functions: &mut Vec<vir::ast::Function>,
    span: Span,
    id: DefId,
    visibility: vir::ast::Visibility,
    module_path: &vir::ast::Path,
    attrs: &[Attribute],
    typ: &Typ,
    body_id: &BodyId,
    is_static: bool,
) -> Result<Fun, VirErr> {
    let mut path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);

    let vattrs = ctxt.get_verifier_attrs(attrs)?;
    if vattrs.unerased_proxy {
        path = fixup_unerased_proxy_path(&path, span)?;
    }

    let name = Arc::new(FunX { path: path.clone() });

    let mode_opt = crate::attributes::get_mode_opt(attrs);
    let (func_mode, body_mode, ret_mode) = if is_static {
        // All statics are exec
        // For consistency with const, require the user to mark it 'exec' explicitly
        match mode_opt {
            None => {
                return err_span(
                    span,
                    "explicitly mark the static as `exec` and use an `ensures` clause",
                );
            }
            Some(m) => {
                if m != Mode::Exec {
                    return err_span(span, "a static item can only have mode `exec`");
                }
            }
        }
        (Mode::Exec, Mode::Exec, Mode::Exec)
    } else {
        match mode_opt {
            // By default, a const is dual-use as spec and exec,
            // where the function is considered spec but the return value and body are exec:
            None => (Mode::Spec, Mode::Exec, Mode::Exec),
            // Otherwise, a const is a single-mode function:
            Some(m) => (m, m, m),
        }
    };

    if vattrs.external_fn_specification {
        return err_span(span, "`assume_specification` attribute not supported for const");
    }

    let body = find_body(ctxt, body_id);
    let mut vir_body = body_to_vir(ctxt, id, &body_id, body, body_mode, vattrs.external_body)?;
    let header = vir::headers::read_header(&mut vir_body)?;
    if header.require.len() + header.recommend.len() > 0 {
        return err_span(span, "consts cannot have requires/recommends");
    }
    if ret_mode == Mode::Spec && header.ensure.len() > 0 {
        return err_span(span, "spec consts cannot have ensures");
    }
    if header.returns.is_some() {
        return err_span(span, "consts cannot have `returns` clause");
    }

    let ret_name = air_unique_var(RETURN_VALUE);
    let ret = ctxt.spanned_new(
        span,
        ParamX {
            name: ret_name,
            typ: typ.clone(),
            mode: ret_mode,
            is_mut: false,
            unwrapped_info: None,
        },
    );
    let autospec = vattrs.autospec.clone().map(|method_name| {
        let path = autospec_fun(&path, method_name.clone());
        Arc::new(FunX { path })
    });
    let fattrs = make_attributes(
        ctxt,
        id,
        &vattrs,
        false,
        Arc::new(vec![]),
        vattrs.custom_req_err.clone(),
        autospec,
        false,
        false,
        Safety::Safe,
        span,
    )?;

    let (ensure, ens_has_return) =
        clean_ensures_for_unit_return(&ret, &header.const_static_ensures(&name, is_static));

    let (body_visibility, opaqueness) = get_body_visibility_and_fuel(
        span,
        &visibility,
        vattrs.publish,
        &header.open_visibility_qualifier,
        vattrs.opaque,
        vattrs.opaque_outside_module,
        func_mode,
        module_path,
        !vattrs.external_body,
    )?;

    let func = FunctionX {
        name: name.clone(),
        proxy: None,
        kind: FunctionKind::Static,
        visibility,
        body_visibility,
        opaqueness,
        owning_module: Some(module_path.clone()),
        mode: func_mode,
        typ_params: Arc::new(vec![]),
        typ_bounds: Arc::new(vec![]),
        params: Arc::new(vec![]),
        ret,
        ens_has_return,
        require: Arc::new(vec![]),
        ensure,
        returns: None,
        decrease: Arc::new(vec![]),
        decrease_when: None,
        decrease_by: None,
        fndef_axioms: None,
        mask_spec: None,
        unwind_spec: None,
        item_kind: if is_static { ItemKind::Static } else { ItemKind::Const },
        attrs: fattrs,
        body: if vattrs.external_body { None } else { Some(vir_body) },
        extra_dependencies: vec![],
    };
    let function = ctxt.spanned_new(span, func);
    functions.push(function);
    Ok(name)
}

pub(crate) fn check_foreign_item_fn<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    id: DefId,
    span: Span,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    decl: &'tcx FnDecl<'tcx>,
    idents: &[Ident],
    generics: &'tcx Generics,
) -> Result<(), VirErr> {
    let vattrs = ctxt.get_verifier_attrs(attrs)?;

    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);
    let name = Arc::new(FunX { path });

    if vattrs.external_fn_specification {
        return err_span(span, "assume_specification not supported here");
    }

    let mode = get_mode(Mode::Exec, attrs);

    let fn_sig = ctxt.tcx.fn_sig(id);
    // REVIEW: rustc docs refer to skip_binder as "dangerous"
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs().skip_binder();

    let ret_typ_mode =
        check_fn_decl(span, ctxt, id, decl, attrs, mode, fn_sig.output().skip_binder())?;
    let (typ_params, typ_bounds) = check_generics_bounds_no_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        generics.span,
        Some(generics),
        id,
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;
    let mut vir_params: Vec<vir::ast::Param> = Vec::new();

    assert!(idents.len() == inputs.len());
    for (param, input) in idents.iter().zip(inputs.iter()) {
        let name = no_body_param_to_var(param);
        let is_mut = is_mut_ty(ctxt, *input);
        let typ = mid_ty_to_vir(
            ctxt.tcx,
            &ctxt.verus_items,
            id,
            param.span,
            is_mut.map(|(t, _)| t).unwrap_or(input),
            false,
        )?;
        // REVIEW: the parameters don't have attributes, so we use the overall mode
        let vir_param = ctxt.spanned_new(
            param.span,
            ParamX { name, typ, mode, is_mut: is_mut.is_some(), unwrapped_info: None },
        );
        vir_params.push(vir_param);
    }
    let params = Arc::new(vir_params);
    let (ret_typ, ret_mode, ens_has_return) = match ret_typ_mode {
        None => (unit_typ(), mode, false),
        Some((typ, mode)) => (typ, mode, true),
    };
    let ret_param = ParamX {
        name: air_unique_var(RETURN_VALUE),
        typ: ret_typ,
        mode: ret_mode,
        is_mut: false,
        unwrapped_info: None,
    };
    let ret = ctxt.spanned_new(span, ret_param);

    // No body, so these don't matter
    let body_visibility = vir::ast::BodyVisibility::Visibility(visibility.clone());
    let opaqueness = Opaqueness::Opaque;

    let func = FunctionX {
        name,
        proxy: None,
        kind: FunctionKind::Static,
        visibility,
        body_visibility,
        opaqueness,
        owning_module: None,
        mode,
        typ_params,
        typ_bounds,
        params,
        ret,
        ens_has_return,
        require: Arc::new(vec![]),
        ensure: Arc::new(vec![]),
        returns: None,
        decrease: Arc::new(vec![]),
        decrease_when: None,
        decrease_by: None,
        fndef_axioms: None,
        mask_spec: None,
        unwind_spec: None,
        item_kind: ItemKind::Function,
        attrs: Default::default(),
        body: None,
        extra_dependencies: vec![],
    };
    let function = ctxt.spanned_new(span, func);
    vir.functions.push(function);
    Ok(())
}

fn get_body_visibility_and_fuel(
    span: Span,
    func_visibility: &Visibility,
    publish: Option<AttrPublish>,
    open_visibility_qualifier: &Option<Visibility>,
    opaque: bool,
    opaque_outside_module: bool,
    mode: Mode,
    my_module: &vir::ast::Path,
    has_body: bool,
) -> Result<(BodyVisibility, Opaqueness), VirErr> {
    let private_vis = Visibility { restricted_to: Some(my_module.clone()) };

    if open_visibility_qualifier.is_some() && publish != Some(AttrPublish::Open) {
        crate::internal_err!(
            span,
            "found 'open_visibility_qualifier' declaration but no 'publish' attribute"
        )
    }

    if mode != Mode::Spec {
        if publish == Some(AttrPublish::Open) {
            return err_span(span, "function is marked `open` but it is not a `spec` function");
        }
        if publish == Some(AttrPublish::Closed) {
            return err_span(span, "function is marked `closed` but it is not a `spec` function");
        }
        if opaque || opaque_outside_module {
            return err_span(span, "function is marked `opaque` but it is not a `spec` function");
        }

        // These don't matter for non-spec functions
        Ok((BodyVisibility::Visibility(private_vis), Opaqueness::Opaque))
    } else if !has_body {
        if opaque || opaque_outside_module {
            return err_span(span, "opaque has no effect on a function without a body");
        }

        if publish == Some(AttrPublish::Uninterp) {
            Ok((BodyVisibility::Uninterpreted, Opaqueness::Opaque))
        } else {
            // These don't matter without a body
            Ok((BodyVisibility::Visibility(private_vis), Opaqueness::Opaque))
        }
    } else {
        // mode == Mode::Spec && has_body
        if publish == Some(AttrPublish::Uninterp) {
            return err_span(span, "function is marked `uninterp` but it has a body");
        }

        if opaque && opaque_outside_module {
            return err_span(span, "function is marked both 'opaque' and 'opaque_outside_module'");
        }

        if publish == Some(AttrPublish::Open) && func_visibility == &private_vis {
            return err_span(
                span,
                "function is marked `open` but not marked `pub`; for the body of a function to be visible, the function symbol must also be visible",
            );
        }

        if let Some(vis) = open_visibility_qualifier {
            if !vis.at_least_as_restrictive_as(&func_visibility) {
                return err_span(
                    span,
                    "the function body is declared 'open' to a wider scope than the function itself",
                );
            }
        }

        let body_visibility = if publish == Some(AttrPublish::Open) {
            match open_visibility_qualifier {
                None => func_visibility.clone(),
                Some(vis) => vis.clone(),
            }
        } else {
            private_vis.clone()
        };

        let opaqueness = if opaque {
            Opaqueness::Opaque
        } else if opaque_outside_module {
            Opaqueness::Revealed { visibility: private_vis }
        } else {
            Opaqueness::Revealed {
                // Revealed everywhere the module is visible
                visibility: body_visibility.clone(),
            }
        };

        Ok((BodyVisibility::Visibility(body_visibility), opaqueness))
    }
}
