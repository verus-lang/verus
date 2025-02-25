use vir::messages::AstId;

use rustc_hir::HirId;
use rustc_span::SpanData;

use vir::ast::{AutospecUsage, Fun, Krate, Mode, Path, Pattern};
use vir::modes::ErasureModes;

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
