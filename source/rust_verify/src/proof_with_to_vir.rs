use crate::attributes::{
    VERIFIED_IMPL_PREFIX, VERIFIED_IMPL_TRAIT_PREFIX, VERIFIED_PREFIX, VERIFIED_TRAIT_PREFIX,
};
use crate::resolve_traits::{ResolutionResult, ResolvedItem, resolve_trait_item};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{GenericArgsRef, TyCtxt, TypingEnv};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;

/// Finds the concrete override of a `with` trait method, if one exists.
///
/// The call already resolved to the spec companion, whose blanket impl doesn't expose
/// overrides. Look in the sibling impl companion, reusing the same generic arguments.
pub(crate) fn impl_counterpart<'tcx>(
    span: Span,
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    spec_method: DefId,
    args: GenericArgsRef<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let spec_trait = tcx.trait_of_assoc(spec_method)?;
    let suffix = tcx.item_name(spec_trait).as_str().strip_prefix(VERIFIED_TRAIT_PREFIX)?.to_owned();
    let base = tcx.item_name(spec_method).as_str().strip_prefix(VERIFIED_PREFIX)?.to_owned();

    let impl_trait_name = Symbol::intern(&format!("{VERIFIED_IMPL_TRAIT_PREFIX}{suffix}"));
    let impl_trait = sibling_item(tcx, spec_trait, impl_trait_name)?;
    let impl_method_name = Symbol::intern(&format!("{VERIFIED_IMPL_PREFIX}{base}"));
    let impl_method =
        tcx.associated_items(impl_trait).filter_by_name_unhygienic(impl_method_name).next()?.def_id;

    match resolve_trait_item(span, tcx, typing_env, impl_method, args) {
        Ok(ResolutionResult::Resolved {
            resolved_item: ResolvedItem::FromImpl(did, res_args),
            ..
        }) => Some((did, res_args)),
        _ => None,
    }
}

/// Finds an item named `name` declared next to `def_id`.
fn sibling_item<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, name: Symbol) -> Option<DefId> {
    let parent = tcx.opt_parent(def_id)?;
    if !matches!(tcx.def_kind(parent), DefKind::Mod) {
        return None;
    }
    let children = match parent.as_local() {
        Some(local) => tcx.module_children_local(local),
        None => tcx.module_children(parent),
    };
    children.iter().find(|child| child.ident.name == name).and_then(|child| child.res.opt_def_id())
}
