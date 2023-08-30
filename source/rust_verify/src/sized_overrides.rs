use rustc_hir::def_id::DefId;
use rustc_infer::traits::query::CanonicalPredicateGoal;
use rustc_infer::traits::EvaluationResult;
use rustc_infer::traits::OverflowError;
use rustc_middle::ty::ParamEnv;
use rustc_middle::ty::Predicate;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::TyKind;
use rustc_middle::ty::{Clause, ImplPolarity, PredicateKind, TraitPredicate};

pub fn evaluate_obligation<'tcx>(
    tcx: TyCtxt<'tcx>,
    obligation: CanonicalPredicateGoal<'tcx>,
) -> Result<EvaluationResult, OverflowError> {
    match obligation.value.value.kind().skip_binder() {
        PredicateKind::Clause(Clause::Trait(TraitPredicate {
            trait_ref,
            constness: _,
            polarity: ImplPolarity::Positive,
        })) => {
            if tcx.lang_items().sized_trait() == Some(trait_ref.def_id) {
                //let res = (verus_rustc_interface::DEFAULT_QUERY_PROVIDERS.evaluate_obligation)(tcx, obligation);
                //if res != Ok(rustc_infer::traits::EvaluationResult::EvaluatedToOk) {
                //    dbg!(&obligation.value);
                //}
                return Ok(rustc_infer::traits::EvaluationResult::EvaluatedToOk);
            }
        }
        _ => {}
    }
    let res = (verus_rustc_interface::DEFAULT_QUERY_PROVIDERS.evaluate_obligation)(tcx, obligation);
    res
}

/*
pub fn check_sized_trait_predicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env_src: DefId,
    predicate: &Predicate,
) -> Option<bool> {
    match predicate.kind().skip_binder() {
        PredicateKind::Clause(Clause::Trait(TraitPredicate {
            trait_ref,
            constness: _,
            polarity: ImplPolarity::Positive,
        })) => {
            if tcx.lang_items().sized_trait() == Some(trait_ref.def_id) {
                if trait_ref.substs.type_at(0).is_trivially_sized() {
                    return Some(true);
                }

                let local_def_id = param_env_src.as_local().unwrap();
                let mut _orig_values = OriginalQueryValues::default();
                let param_env = tcx.param_env(param_env_src);
                let c_pred = tcx.infer_ctxt().canonicalize_query_keep_static(
                    param_env.and(predicate),
                    &mut _orig_values);
                let _ = tcx.evaluate_obligation(c_pred);
                return Some(true);
            }
        }
        _ => { }
    }
    None
}
*/

const EMPTY: [rustc_middle::traits::ObjectSafetyViolation; 0] = [];
pub fn object_safety_violations<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _def_id: rustc_hir::def_id::DefId,
) -> &'tcx [rustc_middle::traits::ObjectSafetyViolation] {
    &EMPTY
}

pub fn check_sized_trait_predicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env_src: DefId,
    predicate: Predicate<'tcx>,
) -> Option<bool> {
    match predicate.kind().skip_binder() {
        PredicateKind::Clause(Clause::Trait(TraitPredicate {
            trait_ref,
            constness: _,
            polarity: ImplPolarity::Positive,
        })) => {
            if tcx.lang_items().sized_trait() == Some(trait_ref.def_id) {
                let ty = trait_ref.substs.type_at(0);
                let param_env = tcx.param_env(param_env_src);
                return Some(ty_is_sized(tcx, param_env, ty));
            }
        }
        _ => {}
    }
    None
}

fn ty_is_sized<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    if ty.is_trivially_sized(tcx) {
        return true;
    }

    let is_definitely_sized = match ty.kind() {
        TyKind::Uint(_)
        | TyKind::Int(_)
        | TyKind::Bool
        | TyKind::Float(_)
        | TyKind::FnDef(..)
        | TyKind::FnPtr(_)
        | TyKind::RawPtr(..)
        | TyKind::Char
        | TyKind::Ref(..)
        | TyKind::Generator(..)
        | TyKind::GeneratorWitness(..)
        | TyKind::Array(..)
        | TyKind::Closure(..)
        | TyKind::Never
        | TyKind::Bound(..)
        | TyKind::Error(_) => {
            unreachable!("Should be handled by trivially_sized");
        }

        TyKind::Str | TyKind::Slice(_) | TyKind::Dynamic(..) => false,
        TyKind::Alias(..) | TyKind::Placeholder(..) | TyKind::Infer(_) => {
            unimplemented!();
        }
        TyKind::Foreign(..) => {
            unimplemented!();
        }

        TyKind::Param(_) => false,

        TyKind::Tuple(tys) => ty_is_sized(tcx, param_env, tys[tys.len() - 1]),

        TyKind::Adt(def, substs) => {
            // TODO exponential blowup
            let mut ok = true;
            let sc = def.sized_constraint(tcx);
            for ty in sc.0.iter() {
                let ty = sc.rebind(*ty).subst(tcx, substs);
                if !ty_is_sized(tcx, param_env, ty) {
                    ok = false;
                    break;
                }
            }
            ok
        }
    };

    if is_definitely_sized {
        return true;
    }

    // Check if it's sized as a result of the environment
    // e.g., for type params
    for pred in param_env.caller_bounds().iter() {
        match pred.kind().skip_binder() {
            PredicateKind::Clause(Clause::Trait(TraitPredicate {
                trait_ref,
                constness: _,
                polarity: ImplPolarity::Positive,
            })) => {
                if tcx.lang_items().sized_trait() == Some(trait_ref.def_id)
                    && trait_ref.substs.type_at(0) == ty
                {
                    return true;
                }
            }
            _ => {}
        }
    }

    false
}
