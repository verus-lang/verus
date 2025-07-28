use vir::messages::AstId;

use rustc_hir::HirId;
use rustc_span::SpanData;

use vir::ast::{Fun, Function, Krate, Mode, Path, Pattern};
use vir::modes::ErasureModes;

use std::sync::Arc;

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
    ClosureToFnProof(Mode),
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
    /// The call is to a function, and we temporarily record the name of the function here
    /// (both unresolved and resolved), as well as an in_ghost flag.
    /// This is replaced by CallModes as soon as the modes are available.
    CallPlaceholder(Fun, Fun, bool),
    /// The call is to a function with some mode and some parameter modes
    /// (The name may be None for spec functions)
    CallModes(Option<Fun>, Mode, Arc<Vec<Mode>>),
    /// Path and variant of datatype constructor
    Ctor(Path, vir::ast::Ident),
    /// The call is to a dynamically computed function, and is exec
    NonStaticExec,
    /// The call is to a dynamically computed function, and is proof
    NonStaticProof(Arc<Vec<Mode>>),
}

#[derive(Clone)]
pub struct ErasureHints {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    pub vir_crate: Krate,
    /// Connect expression and pattern HirId to corresponding vir AstId
    pub hir_vir_ids: Vec<(HirId, AstId)>,
    /// Details of each call in the first run's HIR
    pub resolved_calls: Vec<(HirId, SpanData, ResolvedCall)>,
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

impl ErasureHints {
    pub(crate) fn resolve_call_modes(&mut self, vir_crate: &Krate) {
        use std::collections::HashMap;
        let mut functions: HashMap<Fun, Function> = HashMap::new();
        for f in vir_crate.functions.iter() {
            functions.insert(f.x.name.clone(), f.clone());
        }
        for (_, _, r) in &mut self.resolved_calls {
            if let ResolvedCall::CallPlaceholder(ufun, rfun, in_ghost) = r {
                // Note: in principle, the unresolved function ufun should always be present,
                // but we currently allow external declarations of resolved trait functions
                // without a corresponding external trait declaration.
                let Some(f) = functions.get(ufun).or_else(|| functions.get(rfun)) else {
                    dbg!(ufun, rfun);
                    panic!("missing function for ResolvedCall::CallPlaceholder");
                };
                if *in_ghost && f.x.mode == Mode::Exec {
                    // This must be an autospec, so change exec -> spec
                    let param_modes = Arc::new(f.x.params.iter().map(|_| Mode::Spec).collect());
                    *r = ResolvedCall::CallModes(None, Mode::Spec, param_modes);
                } else {
                    let param_modes = Arc::new(f.x.params.iter().map(|p| p.x.mode).collect());
                    *r = ResolvedCall::CallModes(Some(rfun.clone()), f.x.mode, param_modes);
                }
            }
        }
    }
}
