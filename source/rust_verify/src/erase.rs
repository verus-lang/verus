use crate::attributes::{get_mode, get_verifier_attrs};
use crate::rust_to_vir_expr::attrs_is_invariant_block;
use crate::spans::from_raw_span;
use crate::unsupported;
use crate::util::vec_map;
use crate::verifier::DiagnosticOutputBuffer;

use air::ast::AstId;

use rustc_ast::ast::{
    AngleBracketedArg, AngleBracketedArgs, Arm, AssocItem, AssocItemKind, BinOpKind, Block, Crate,
    EnumDef, Expr, ExprField, ExprKind, FieldDef, FnDecl, FnRetTy, FnSig, GenericArg, GenericArgs,
    GenericParam, GenericParamKind, Generics, Impl, Item, ItemKind, LitIntType, LitKind, Local,
    LocalKind, ModKind, NodeId, Param, Pat, PatField, PatKind, PathSegment, Stmt, StmtKind,
    StructExpr, StructRest, Trait, Ty, TyKind, Variant, VariantData,
};
use rustc_ast::ptr::P;
use rustc_hir::HirId;
use rustc_span::symbol::{Ident, Symbol};
use rustc_span::{Span, SpanData};

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use vir::ast::{
    Datatype, ExprX, FieldOpr, Fun, Function, GenericBoundX, Krate, Mode, Path, Pattern, PatternX,
    UnaryOpr,
};
use vir::ast_util::get_field;
use vir::modes::{mode_join, ErasureModes};

#[derive(Clone, Copy, Debug)]
pub enum CompilableOperator {
    IntIntrinsic,
    Implies,
    SmartPtrNew,
    SmartPtrClone,
    NewStrLit,
    GhostExec,
    TrackedNew,
    TrackedExec,
    TrackedExecBorrow,
    TrackedGet,
    TrackedBorrow,
    TrackedBorrowMut,
    GhostSplitTuple,
    TrackedSplitTuple,
}

/// Information about each call in the AST (each ExprKind::Call).
#[derive(Clone, Debug)]
pub enum ResolvedCall {
    /// The call is to a spec or proof function, and should be erased
    Spec,
    /// The call is to a spec or proof function, but may have proof-mode arguments
    SpecAllowProofArgs,
    /// The call is to an operator like == or + that should be compiled.
    CompilableOperator(CompilableOperator),
    /// The call is to a function, and we record the resolved name of the function here.
    Call(Fun),
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
