use vir::messages::AstId;

use rustc_hir::HirId;
use rustc_span::SpanData;

use vir::ast::{AutospecUsage, Fun, Krate, Mode, Path, Pattern, Function};
use vir::modes::ErasureModes;

use rustc_mir_build_verus::verus::{VerusErasureCtxt, set_verus_erasure_ctxt, VarErasure, CallErasure};
use crate::verus_items::{VerusItem, VerusItems};
use std::sync::Arc;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CompilableOperator {
    IntIntrinsic,
    Implies,
    RcNew,
    ArcNew,
    BoxNew,
    SmartPtrClone { is_method: bool },
    GhostExec,
    TrackedNew,
    TrackedExec,
    TrackedExecBorrow,
    TrackedGet,
    TrackedBorrow,
    TrackedBorrowMut,
    UseTypeInvariant,
}

/// Information about each call in the AST (each ExprKind::Call).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedCall {
    /// The call is to a spec or proof function, and should be erased
    Spec,
    /// The call is to a spec or proof function, but may have proof-mode arguments
    SpecAllowProofArgs,
    /// The call is to an operator like == or + that should be compiled.
    CompilableOperator(CompilableOperator),
    /// The call is to a function, and we record the resolved name of the function here.
    Call(Fun, AutospecUsage),
    /// Path and variant of datatype constructor
    Ctor(Path, vir::ast::Ident),
    /// The call is to a dynamically computed function, and is exec
    NonStaticExec,
}

#[derive(Clone)]
pub struct ErasureHints {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    pub vir_crate: Krate,
    /// Connect expression and pattern HirId to corresponding vir AstId
    pub hir_vir_ids: Vec<(HirId, AstId)>,
    /// Details of each call in the first run's HIR
    pub resolved_calls: Vec<(HirId, SpanData, ResolvedCall)>,
    /// Details of some expressions in first run's HIR
    pub resolved_exprs: Vec<(SpanData, vir::ast::Expr)>,
    /// Details of some patterns in first run's HIR
    pub resolved_pats: Vec<(SpanData, Pattern)>,
    /// Results of mode (spec/proof/exec) inference from first run's VIR
    pub erasure_modes: ErasureModes,
    /// Modes specified directly during rust_to_vir
    pub direct_var_modes: Vec<(HirId, Mode)>,
    /// List of #[verifier(external)] functions.  (These don't appear in vir_crate,
    /// so we need to record them separately here.)
    pub external_functions: Vec<Fun>,
    /// List of function spans ignored by the verifier. These should not be erased
    pub ignored_functions: Vec<(rustc_span::def_id::DefId, SpanData)>,
}

fn mode_to_var_erase(mode: Mode) -> VarErasure {
    match mode {
        Mode::Spec => VarErasure::Erase,
        Mode::Exec | Mode::Proof => VarErasure::Keep,
    }
}

fn resolved_call_to_call_erase(
    functions: &HashMap<Fun, Option<Function>>,
    resolved_call: &ResolvedCall
) -> CallErasure {
    match resolved_call {
        ResolvedCall::Spec => CallErasure::EraseAll,
        ResolvedCall::SpecAllowProofArgs => CallErasure::EraseCallButNotArgs,
        ResolvedCall::Call(f_name, autospec_usage) => {
            if !functions.contains_key(f_name) {
                panic!("internal error: function call to {:?} not found", f_name);
            }
            let f = &functions[f_name];
            let f = if let Some(f) = f {
                f
            } else {
                panic!("internal error: call to external function {:?}", f_name);
            };

            let f = match (autospec_usage, &f.x.attrs.autospec) {
                (AutospecUsage::IfMarked, Some(new_f_name)) => {
                    let f = &functions[new_f_name];
                    let f = if let Some(f) = f {
                        f
                    } else {
                        panic!(
                            "internal error: call to external function {:?}",
                            f_name,
                        );
                    };
                    f.clone()
                }
                _ => f.clone()
            };

            if f.x.mode == Mode::Spec {
                CallErasure::EraseAll
            } else {
                CallErasure::Keep
            }
        }
        ResolvedCall::Ctor(..) => {
            // TODO: we should check the mode here and erase if it's spec
            // (ctor might have lifetime bounds)
            CallErasure::Keep
        }
        ResolvedCall::NonStaticExec => CallErasure::Keep,
        ResolvedCall::CompilableOperator(co) => match co {
            | CompilableOperator::IntIntrinsic
            | CompilableOperator::Implies
            | CompilableOperator::RcNew
            | CompilableOperator::ArcNew
            | CompilableOperator::BoxNew
            | CompilableOperator::SmartPtrClone { .. }
            | CompilableOperator::TrackedNew
            | CompilableOperator::TrackedExec
            | CompilableOperator::TrackedExecBorrow
            | CompilableOperator::TrackedGet
            | CompilableOperator::TrackedBorrow
            | CompilableOperator::TrackedBorrowMut
            | CompilableOperator::UseTypeInvariant => CallErasure::Keep,

            CompilableOperator::GhostExec => CallErasure::EraseAll,
        }
    }
}

pub(crate) fn setup_verus_ctxt_for_thir_erasure(
    verus_items: &VerusItems,
    erasure_hints: &ErasureHints,
) {
    let mut id_to_hir: HashMap<AstId, Vec<HirId>> = HashMap::new();
    for (hir_id, vir_id) in &erasure_hints.hir_vir_ids {
        if !id_to_hir.contains_key(vir_id) {
            id_to_hir.insert(*vir_id, vec![]);
        }
        id_to_hir.get_mut(vir_id).unwrap().push(*hir_id);
    }

    let mut vars = HashMap::<HirId, VarErasure>::new();
    for (span, mode) in erasure_hints.erasure_modes.var_modes.iter() {
        for hir_id in &id_to_hir[&span.id] {
            vars.insert(*hir_id, mode_to_var_erase(*mode));
        }
    }

    let mut functions = HashMap::<Fun, Option<Function>>::new();
    for f in &erasure_hints.vir_crate.functions {
        functions.insert(f.x.name.clone(), Some(f.clone())).map(|_| panic!("{:?}", &f.x.name));
    }

    let mut calls = HashMap::<HirId, CallErasure>::new();
    for (hir_id, _, resolved_call) in &erasure_hints.resolved_calls {
        calls.insert(*hir_id, resolved_call_to_call_erase(&functions, resolved_call));
    }

    let verus_erasure_ctxt = VerusErasureCtxt {
        vars,
        calls,
        erased_ghost_value_fn_def_id: *verus_items.name_to_id.get(&VerusItem::ErasedGhostValue).unwrap(),
    };
    set_verus_erasure_ctxt(Arc::new(verus_erasure_ctxt));
}

