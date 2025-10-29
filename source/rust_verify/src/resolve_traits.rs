use crate::rustc_trait_selection::infer::TyCtxtInferExt;
use rustc_hir::def_id::DefId;
use rustc_middle::traits::ImplSource;
use rustc_middle::ty::{GenericArgsRef, TraitRef, TyCtxt, TypingEnv};
use rustc_span::Span;
use rustc_trait_selection::traits::BuiltinImplSource;
use vir::ast::VirErr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ResolvedItem<'tcx> {
    FromImpl(DefId, GenericArgsRef<'tcx>),
    FromTrait(DefId, GenericArgsRef<'tcx>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ResolutionResult<'tcx> {
    Unresolved,
    Resolved {
        impl_def_id: DefId,
        impl_args: GenericArgsRef<'tcx>,
        impl_item_args: GenericArgsRef<'tcx>,
        resolved_item: ResolvedItem<'tcx>,
    },
    Builtin(BuiltinImplSource),
}

pub(crate) fn resolve_trait_item<'tcx>(
    span: Span,
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    trait_item_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> Result<ResolutionResult<'tcx>, VirErr> {
    let Some(trait_def_id) = tcx.trait_of_item(trait_item_id) else {
        crate::internal_err!(span, "resolve_trait_method called for non-trait item");
    };

    let normalized_args = tcx.normalize_erasing_regions(typing_env, args);
    let trait_ref = TraitRef::new(tcx, trait_def_id, normalized_args);

    let pseudo_canonical_inp =
        rustc_middle::ty::PseudoCanonicalInput { typing_env, value: trait_ref };
    let candidate = tcx.codegen_select_candidate(pseudo_canonical_inp);

    match candidate {
        Ok(ImplSource::UserDefined(impl_data)) => {
            // Based on the implementation of resolve_associated_item
            // from rustc_ty_utils/src/instance.rs

            let impl_def_id = impl_data.impl_def_id;

            let trait_def = tcx.trait_def(trait_def_id);

            // The 'leaf_def' gives us the most specialized version of the item
            let ancestors = trait_def.ancestors(tcx, impl_data.impl_def_id);
            let Ok(ancestors) = ancestors else {
                crate::internal_err!(span, "ancestors failed");
            };
            let leaf_def = ancestors.leaf_def(tcx, trait_item_id);
            let Some(leaf_def) = leaf_def else {
                crate::internal_err!(span, "leaf_def failed");
            };

            // Get the args you would use to instantiate the impl item.
            // (This works even if there is no "real" impl item because we're using
            // the trait default impl instead)
            let typing_env = typing_env.with_post_analysis_normalized(tcx);
            let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
            let args0 = args.rebase_onto(tcx, trait_def_id, impl_data.args);
            let args1 = rustc_trait_selection::traits::translate_args(
                &infcx,
                param_env,
                impl_data.impl_def_id,
                args0,
                leaf_def.defining_node,
            );
            let impl_item_args = infcx.tcx.erase_regions(args1);

            let item_def_id = leaf_def.item.def_id;

            let resolved_item = match tcx.impl_of_assoc(item_def_id) {
                Some(impl_def_id_containing_item) => {
                    if impl_def_id_containing_item != impl_def_id {
                        crate::internal_err!(
                            span,
                            "ImplDefIds don't match; this may be caused by the use of the unstable specialization feature"
                        );
                    }
                    ResolvedItem::FromImpl(item_def_id, impl_item_args)
                }
                None => ResolvedItem::FromTrait(item_def_id, args),
            };

            Ok(ResolutionResult::Resolved {
                impl_def_id: impl_data.impl_def_id,
                impl_args: impl_data.args,
                impl_item_args,
                resolved_item,
            })
        }
        Ok(ImplSource::Builtin(b, _)) => Ok(ResolutionResult::Builtin(*b)),
        Ok(ImplSource::Param(_)) => Ok(ResolutionResult::Unresolved),
        Err(_) => {
            crate::internal_err!(span, "codegen_select_candidate failed");
        }
    }
}
