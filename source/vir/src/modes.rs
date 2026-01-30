use crate::ast::{
    AutospecUsage, BinaryOp, ByRef, CallTarget, CallTargetKind, CtorUpdateTail, Datatype,
    DeclProph, Dt, Expr, ExprX, FieldOpr, Fun, Function, FunctionKind, InvAtomicity, ItemKind,
    Krate, Mode, ModeCoercion, MultiOp, MutRefFutureSourceName, OverflowBehavior, Path, Pattern,
    PatternBinding, PatternX, Place, PlaceX, ReadKind, SpannedTyped, Stmt, StmtX, Typ,
    TypDecoration, TypX, UnaryOp, UnaryOpr, UnfinalizedReadKind, UnwindSpec, VarIdent, VirErr,
};
use crate::ast_util::{get_field, is_unit, path_as_vstd_name, typ_to_diagnostic_str};
use crate::def::user_local_name;
use crate::messages::{Span, error};
use crate::messages::{error_bare, error_with_label};
use crate::util::vec_map_result;
use air::scope_map::ScopeMap;
use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::mem::swap;
use std::rc::Rc;
use std::sync::Arc;

// Exec <= Proof <= Spec
pub fn mode_le(m1: Mode, m2: Mode) -> bool {
    match (m1, m2) {
        (_, Mode::Spec) => true,
        (Mode::Exec, _) => true,
        _ if m1 == m2 => true,
        _ => false,
    }
}

// least upper bound
pub fn mode_join(m1: Mode, m2: Mode) -> Mode {
    match (m1, m2) {
        (_, Mode::Spec) => Mode::Spec,
        (Mode::Spec, _) => Mode::Spec,
        (Mode::Exec, m) => m,
        (m, Mode::Exec) => m,
        (Mode::Proof, Mode::Proof) => Mode::Proof,
    }
}

// least upper bound
pub fn mode_meet(m1: Mode, m2: Mode) -> Mode {
    match (m1, m2) {
        (_, Mode::Exec) => Mode::Exec,
        (Mode::Exec, _) => Mode::Exec,
        (Mode::Spec, m) => m,
        (m, Mode::Spec) => m,
        (Mode::Proof, Mode::Proof) => Mode::Proof,
    }
}

#[derive(Clone, Debug)]
enum Proph {
    No,
    Yes(ProphReason),
}

#[derive(Clone, Debug)]
enum ProphVar {
    No,
    Yes(ProphVarReason),
}

#[derive(Clone, Debug)]
struct ProphReason {
    span: Span,
    kind: ProphReasonKind,
}

#[derive(Clone, Debug)]
enum ProphReasonKind {
    MutRefFuture(MutRefFutureSourceName),
    AfterBorrow,
    HasResolved,
    SpecFunction(Span),
    Var(VarIdent, ProphVarReason),
}

#[derive(Clone, Debug)]
enum ProphVarReason {
    Explicit(Span),
    Inferred(Rc<ProphReason>),
}

#[derive(Clone, Copy)]
enum NoProphReason {
    NonPropheticSpecFnBody,
    Return,
    ExecFnCall,
    ProofFnCall,
    DecreasesClause,
    NonSpecDecl,
    AssignToNonProphPlace,
    MutBorrow,
    MutBorrowArgument,
    Index,
    LoopCondition,
    GhostWrap,
    TrackedWrap,
    LetElse,
    OpenInvariantArg,
}

#[derive(Clone, Copy)]
enum OuterProphReason {
    ExecFnCall,
    ProofFnCall,
    AssignToNonProphPlace,
    MutBorrow,
    Loop,
    Return,
    Break,
    Continue,
    OpenInvariant,
    NonSpecClosure,
    LetElse,
}

impl Proph {
    fn join(self, other: Proph) -> Proph {
        match (self, other) {
            (Proph::No, other) => other,
            (other, Proph::No) => other,
            (Proph::Yes(r1), Proph::Yes(r2)) => {
                // Prioritize the simpler reason
                if matches!(r1.kind, ProphReasonKind::Var(..))
                    && !matches!(r2.kind, ProphReasonKind::Var(..))
                {
                    Proph::Yes(r2)
                } else {
                    Proph::Yes(r1)
                }
            }
        }
    }

    fn check(&self, span: &Span, reason: NoProphReason) -> Result<(), VirErr> {
        let Proph::Yes(proph_reason) = self else {
            return Ok(());
        };
        let (reason_str, short) = match reason {
            NoProphReason::NonPropheticSpecFnBody => ("body of non-prophetic spec function", ""),
            NoProphReason::Return => ("return value", "this return value"),
            NoProphReason::ExecFnCall => ("argument to exec-mode function", "this argument"),
            NoProphReason::ProofFnCall => {
                ("argument to proof-mode function with tracked parameters", "this argument")
            }
            NoProphReason::DecreasesClause => ("'decreases' clause", "this decreases-measure"),
            NoProphReason::NonSpecDecl => ("declaration of non-ghost variables", "this expression"),
            NoProphReason::MutBorrow => ("mutable borrow", "this operand"),
            NoProphReason::MutBorrowArgument => ("mutable borrow", "this operand"),
            NoProphReason::Index => ("index into array or slice", "index"),
            NoProphReason::LoopCondition => ("loop condition", "this condition"),
            NoProphReason::GhostWrap => ("'Ghost' wrapper", "operand of this wrapper"),
            NoProphReason::TrackedWrap => ("'Tracked' wrapper", "operand of this wrapper"),
            NoProphReason::LetElse => ("let-else statement", "this matched expression"),
            NoProphReason::OpenInvariantArg => ("invariant statement", "this operand"),
            NoProphReason::AssignToNonProphPlace => {
                ("assignment to non-prophetic location", "this expression")
            } //NoProphReason::AssignToNonProphSpecPlace => "assignment to ghost location that is not marked prophetic",
              //NoProphReason::AssignToNonSpecPlace => "assignment to non-ghost location",
        };
        let mut err = error(span, format!("prophetic value not allowed for {:}", reason_str));
        err = proph_reason.annotate_err(err);
        if !short.is_empty() {
            err = err.primary_label(span, format!("{:} is expected to be non-prophetic", short));
        }
        match reason {
            NoProphReason::NonPropheticSpecFnBody => {
                err = err.help("consider marking this function prophetic with the `#[verifier::prophetic]` attribute");
            }
            //NoProphReason::AssignToNonProphSpecPlace => {
            //    err = err.help("consider annotating the declaration of this variable with the `#[verifier::prophetic]` attribute");
            //}
            NoProphReason::DecreasesClause => {
                err = err.help("prophetic values cannot soundly be used for termination reasoning because they are not bounded a priori");
            }
            _ => {}
        }
        Err(err)
    }

    fn outer_check(&self, span: &Span, reason: OuterProphReason) -> Result<(), VirErr> {
        let Proph::Yes(proph_reason) = self else {
            return Ok(());
        };
        let reason_str = match reason {
            OuterProphReason::ExecFnCall => "call to exec-mode function",
            OuterProphReason::ProofFnCall => "call to proof-mode function with tracked parameters",
            OuterProphReason::AssignToNonProphPlace => "assignment to non-prophetic location",
            OuterProphReason::MutBorrow => "mutable borrow",
            OuterProphReason::Loop => "loop",
            OuterProphReason::Return => "return",
            OuterProphReason::Break => "break",
            OuterProphReason::Continue => "continue",
            OuterProphReason::OpenInvariant => "opening an invariant",
            OuterProphReason::NonSpecClosure => "closure",
            OuterProphReason::LetElse => "let-else statement",
        };
        let mut err = error_with_label(
            span,
            format!("{:} cannot occur in prophecy-conditional context", reason_str),
            "this operation cannot be performed conditionally when the condition depends on a prophecy",
        );
        err = proph_reason.annotate_err(err);
        Err(err)
    }

    fn to_inferred_proph_var(&self) -> ProphVar {
        match self {
            Proph::No => ProphVar::No,
            Proph::Yes(reason) => ProphVar::Yes(ProphVarReason::Inferred(Rc::new(reason.clone()))),
        }
    }
}

/// For any expression that can't be allowed in prophecy-conditional context
/// i.e., if it should be an error to do this:
/// ```
/// if proph_value() {
///    e;
/// }
/// ```
/// Then either this function should return a reason, OR it needs to be checked as part
/// of the main `check_expr` function.
///
/// When in doubt, make it an error.
///
/// The main purpose of splitting this function out is to make it easy to add a check when
/// someone adds a new variant to ExprX
fn outer_reason_by_expr_kind(e: &Expr) -> Option<OuterProphReason> {
    match &e.x {
        ExprX::Const(_)
            | ExprX::Var(_)
            | ExprX::VarLoc(_)
            | ExprX::VarAt(..)
            | ExprX::ConstVar(..)
            | ExprX::StaticVar(..)
            | ExprX::Loc(_)
            | ExprX::Call(..) // requires more complex checks
            | ExprX::Ctor(..)
            | ExprX::NullaryOpr(_)
            | ExprX::Unary(..)
            | ExprX::UnaryOpr(..)
            | ExprX::Binary(..)
            | ExprX::BinaryOpr(..)
            | ExprX::Multi(..)
            | ExprX::Quant(..)
            | ExprX::Closure(..)
            | ExprX::ArrayLiteral(_)
            | ExprX::ExecFnByName(_)
            | ExprX::Choose { .. }
            | ExprX::WithTriggers { .. }
            | ExprX::Assign { .. } // requires more complex checks
            | ExprX::AssignToPlace { .. } // requires more complex checks
            | ExprX::Fuel(..)
            | ExprX::RevealString(..)
            | ExprX::Header(..)
            | ExprX::AssertAssume { .. }
            | ExprX::AssertAssumeUserDefinedTypeInvariant { .. }
            | ExprX::AssertBy { .. }
            | ExprX::AssertQuery { .. }
            | ExprX::AssertCompute { .. }
            | ExprX::If(..)
            | ExprX::Match(..)
            | ExprX::Ghost { .. }
            | ExprX::ProofInSpec(..)
            | ExprX::Block(..)
            | ExprX::AirStmt(..)
            | ExprX::NeverToAny(..)
            | ExprX::Nondeterministic
            | ExprX::UseLeftWhereRightCanHaveNoAssignments(..)
            | ExprX::ReadPlace(..)
            // all borrow types checked in the main function
            | ExprX::ImplicitReborrowOrSpecRead(..)
            | ExprX::BorrowMut(..)
            | ExprX::TwoPhaseBorrowMut(..)
        => None,
        ExprX::NonSpecClosure { .. } => Some(OuterProphReason::NonSpecClosure),
        ExprX::Loop { .. } => Some(OuterProphReason::Loop),
        ExprX::OpenInvariant { .. } => Some(OuterProphReason::OpenInvariant),
        ExprX::Return(..) => Some(OuterProphReason::Return),
        ExprX::BreakOrContinue { is_break: true, .. } => Some(OuterProphReason::Break),
        ExprX::BreakOrContinue { is_break: false, .. } => Some(OuterProphReason::Continue),
    }
}

impl ProphVar {
    fn to_proph(&self, name: &VarIdent, use_span: &Span) -> Proph {
        match self {
            ProphVar::No => Proph::No,
            ProphVar::Yes(reason) => Proph::Yes(ProphReason {
                span: use_span.clone(),
                kind: ProphReasonKind::Var(name.clone(), reason.clone()),
            }),
        }
    }
}

impl ProphReason {
    fn annotate_err(&self, err: crate::messages::Message) -> crate::messages::Message {
        let mut err = err;
        if let ProphReasonKind::Var(name, ProphVarReason::Inferred(_)) = &self.kind {
            err = err.secondary_label(
                &self.span,
                format!("the variable `{:}` is inferred as prophetic", user_local_name(name)),
            );
        }
        let mut root = self;
        while let ProphReasonKind::Var(_, ProphVarReason::Inferred(r)) = &root.kind {
            root = &r;
        }
        match &root.kind {
            ProphReasonKind::Var(_, ProphVarReason::Inferred(_)) => unreachable!(),
            ProphReasonKind::Var(name, ProphVarReason::Explicit(decl_span)) => {
                err = err.secondary_label(
                    &root.span,
                    format!("the variable `{:}` is marked prophetic", user_local_name(name)),
                );
                err = err.secondary_label(decl_span, "variable marked prophetic at declaration");
            }
            ProphReasonKind::MutRefFuture(source_name) => {
                err = err.secondary_label(
                    &root.span,
                    format!("the `{:}` builtin is prophetic", source_name.as_str()),
                );
            }
            ProphReasonKind::AfterBorrow => {
                err = err.secondary_label(&root.span, "the `after_borrow` builtin is prophetic");
            }
            ProphReasonKind::HasResolved => {
                err = err.secondary_label(&root.span, "the `has_resolved` builtin is prophetic");
            }
            ProphReasonKind::SpecFunction(decl_span) => {
                err = err.secondary_label(&root.span, "the result of this call is prophetic");
                err = err.secondary_label(
                    &decl_span,
                    "function is declared prophetic at this definition",
                );
            }
        }
        err
    }
}

fn function_allows_proph(function: &Function) -> (Option<NoProphReason>, Option<OuterProphReason>) {
    match function.x.mode {
        Mode::Spec => (None, None),
        Mode::Exec => (Some(NoProphReason::ExecFnCall), Some(OuterProphReason::ExecFnCall)),
        Mode::Proof => {
            let mut any_non_spec = false;
            for param in function.x.params.iter() {
                if param.x.mode != Mode::Spec {
                    any_non_spec = true;
                    break;
                }
            }
            any_non_spec |= function.x.ret.x.mode != Mode::Spec && !is_unit(&function.x.ret.x.typ);

            if any_non_spec {
                (Some(NoProphReason::ProofFnCall), Some(OuterProphReason::ProofFnCall))
            } else {
                (None, None)
            }
        }
    }
}

fn mode_proph_join(m1: (Mode, Proph), m2: (Mode, Proph)) -> (Mode, Proph) {
    (mode_join(m1.0, m2.0), m1.1.join(m2.1))
}

/// Represents Rust ghost blocks
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Ghost {
    /// Not in a ghost block
    Exec,
    /// In a ghost block
    Ghost,
}

/// Indicates we should eagerly coerce up to the given mode, when possible.
/// This does *not* impose any extra checks; the caller of any function which takes an Expect
/// argument is still responsible for checking the result.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Expect(Mode);

impl Expect {
    fn join(&self, mode: Mode) -> Mode {
        mode_join(self.0, mode)
    }

    fn meet(&self, mode: Mode) -> Mode {
        mode_meet(self.0, mode)
    }

    /// Use the lowest mode to have no effect
    fn none() -> Self {
        Expect(Mode::Exec)
    }
}

#[derive(Clone, Debug)]
pub struct ErasureModes {
    // Modes of variables in Var, Assign, Decl
    pub var_modes: Vec<(Span, Mode)>,
    // Modes of calls and struct Ctors
    pub ctor_modes: Vec<(Span, Mode)>,
}

impl Ghost {
    fn of_mode(mode: Mode) -> Ghost {
        match mode {
            Mode::Spec | Mode::Proof => Ghost::Ghost,
            Mode::Exec => Ghost::Exec,
        }
    }

    fn join_mode(self, mode: Mode) -> Mode {
        match self {
            Ghost::Ghost => mode_join(mode, Mode::Proof),
            Ghost::Exec => mode,
        }
    }
}

struct SpecialPaths {
    pub(crate) create_open_invariant_credit_name: String,
    pub(crate) spend_open_invariant_credit_name: String,
    pub(crate) exec_nonstatic_call_name: String,
}

impl SpecialPaths {
    pub fn new(vstd_crate_name: Arc<String>) -> Self {
        let create_open_invariant_credit_name = path_as_vstd_name(
            &crate::def::create_open_invariant_credit_path(&Some(vstd_crate_name.clone())),
        )
        .expect("could not find path to create_open_invariant_credit");
        let spend_open_invariant_credit_name = path_as_vstd_name(
            &crate::def::spend_open_invariant_credit_path(&Some(vstd_crate_name.clone())),
        )
        .expect("could not find path to spend_open_invariant_credit");
        let exec_nonstatic_call_name = path_as_vstd_name(&crate::def::nonstatic_call_path(
            &Some(vstd_crate_name.clone()),
            false,
        ))
        .expect("could not find path to exec_nonstatic_call");
        Self {
            create_open_invariant_credit_name,
            spend_open_invariant_credit_name,
            exec_nonstatic_call_name,
        }
    }

    pub fn is_create_or_spend_open_invariant_credit_path(&self, path: &Path) -> bool {
        match path_as_vstd_name(path) {
            None => false,
            Some(s) => {
                s == *self.create_open_invariant_credit_name
                    || s == *self.spend_open_invariant_credit_name
            }
        }
    }

    pub fn is_exec_nonstatic_call_path(&self, path: &Path) -> bool {
        match path_as_vstd_name(path) {
            None => false,
            Some(s) => s == *self.exec_nonstatic_call_name,
        }
    }
}

struct Ctxt {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) datatypes: HashMap<Path, Datatype>,
    pub(crate) traits: HashSet<Path>,
    pub(crate) check_ghost_blocks: bool,
    pub(crate) fun_mode: Mode,
    pub(crate) special_paths: SpecialPaths,
    pub(crate) new_mut_ref: bool,
}

pub(crate) struct TypeInvInfo {
    pub ctor_needs_check: HashMap<crate::messages::AstId, bool>,
    pub field_loc_needs_check: HashMap<crate::messages::AstId, bool>,
}

pub type ReadKindFinals = HashMap<u64, ReadKind>;

/// Accumulated data recorded during mode checking
struct Record {
    pub(crate) erasure_modes: ErasureModes,
    /// Modes of InferSpecForLoopIter
    infer_spec_for_loop_iter_modes: Option<Vec<(Span, Mode)>>,
    type_inv_info: TypeInvInfo,
    read_kind_finals: ReadKindFinals,
    var_modes: HashMap<VarIdent, Mode>,
    /// Modes of all PlaceX::Temporary nodes
    temporary_modes: HashMap<crate::messages::AstId, Mode>,
    /// Modes of the ImplicitReborrow nodes
    infer_spec_for_implicit_reborrows: Option<HashMap<crate::messages::AstId, bool>>,
}

#[derive(Debug)]
enum VarMode {
    Infer(Span),
    /// We know mode to be spec, but propheticness hasn't been inferred yet
    SpecInferProph,
    Mode(Mode, ProphVar),
}

// Temporary state pushed and popped during mode checking
struct State {
    // for each variable: (is_mutable, mode)
    // mode = None is used for short-term internal inference -- we allow "let x1 ... x1 = x2;"
    // where x2 retroactively determines the mode of x1, where no uses if x1
    // are allowed between "let x1" and "x1 = x2;"
    pub(crate) vars: ScopeMap<VarIdent, VarMode>,
    pub(crate) in_forall_stmt: bool,
    pub(crate) in_proof_in_spec: bool,
    // Are we in a syntactic ghost block?
    // If not, Ghost::Exec (corresponds to exec mode).
    // If yes (corresponding to proof/spec mode), say whether variables are tracked or not.
    // (note that tracked may be false even in proof mode,
    // and tracked is allowed in spec mode, although that would be needlessly constraining)
    pub(crate) block_ghostness: Ghost,
    pub(crate) ret_mode: Option<Mode>,
    pub(crate) atomic_insts: Option<AtomicInstCollector>,
}

mod typing {
    use super::*;

    pub(super) struct Typing<'a> {
        // don't use these fields directly; use * and push_*
        internal_state: &'a mut State,
        internal_undo: Option<Box<dyn for<'b> FnOnce(&'b mut State)>>,
    }

    impl Drop for Typing<'_> {
        fn drop(&mut self) {
            let f: Box<dyn for<'b> FnOnce(&'b mut State)> =
                self.internal_undo.take().expect("drop-undo");
            f(&mut self.internal_state);
        }
    }

    impl Typing<'_> {
        pub(super) fn new<'a>(state: &'a mut State) -> Typing<'a> {
            Typing { internal_state: state, internal_undo: Some(Box::new(|_| {})) }
        }

        pub(super) fn push_var_scope<'a>(&'a mut self) -> Typing<'a> {
            self.internal_state.vars.push_scope(true);
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(|state| {
                    state.vars.pop_scope();
                })),
            }
        }

        pub(super) fn push_var_multi_scope<'a>(&'a mut self) -> Typing<'a> {
            let vars_scope_count = self.internal_state.vars.num_scopes();
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(move |state: &mut State| {
                    while state.vars.num_scopes() != vars_scope_count {
                        state.vars.pop_scope();
                    }
                })),
            }
        }

        // For use after push_var_multi_scope (otherwise, use push_var_scope)
        pub(super) fn add_var_multi_scope<'a>(&mut self) {
            self.internal_state.vars.push_scope(true);
        }

        pub(super) fn push_in_forall_stmt<'a>(
            &'a mut self,
            mut in_forall_stmt: bool,
        ) -> Typing<'a> {
            swap(&mut in_forall_stmt, &mut self.internal_state.in_forall_stmt);
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(move |state| {
                    state.in_forall_stmt = in_forall_stmt;
                })),
            }
        }

        pub(super) fn push_in_proof_in_spec<'a>(
            &'a mut self,
            mut in_proof_in_spec: bool,
        ) -> Typing<'a> {
            swap(&mut in_proof_in_spec, &mut self.internal_state.in_proof_in_spec);
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(move |state| {
                    state.in_proof_in_spec = in_proof_in_spec;
                })),
            }
        }

        pub(super) fn push_block_ghostness<'a>(
            &'a mut self,
            mut block_ghostness: Ghost,
        ) -> Typing<'a> {
            swap(&mut block_ghostness, &mut self.internal_state.block_ghostness);
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(move |state| {
                    state.block_ghostness = block_ghostness;
                })),
            }
        }

        pub(super) fn push_ret_mode<'a>(&'a mut self, mut ret_mode: Option<Mode>) -> Typing<'a> {
            swap(&mut ret_mode, &mut self.internal_state.ret_mode);
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(move |state| {
                    state.ret_mode = ret_mode;
                })),
            }
        }

        pub(super) fn push_atomic_insts<'a>(
            &'a mut self,
            mut atomic_insts: Option<AtomicInstCollector>,
        ) -> Typing<'a> {
            swap(&mut atomic_insts, &mut self.internal_state.atomic_insts);
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(move |state| {
                    state.atomic_insts = atomic_insts;
                })),
            }
        }

        // If we want to catch a VirErr, use this to make sure state is restored upon catching the error
        pub(super) fn push_restore_on_error<'a>(&'a mut self) -> Typing<'a> {
            self.push_var_scope()
        }

        pub(super) fn assert_zero_scopes(&self) {
            assert_eq!(self.internal_state.vars.num_scopes(), 0);
        }

        pub(super) fn to_be_inferred(&self, x: &VarIdent) -> Option<Span> {
            if let VarMode::Infer(span) =
                self.internal_state.vars.get(x).expect("internal error: missing mode")
            {
                Some(span.clone())
            } else {
                None
            }
        }

        pub(super) fn proph_to_be_inferred(&self, x: &VarIdent) -> bool {
            if let VarMode::SpecInferProph =
                self.internal_state.vars.get(x).expect("internal error: missing mode")
            {
                true
            } else {
                false
            }
        }

        pub(super) fn insert_var_mode(&mut self, x: &VarIdent, mode: VarMode) {
            self.internal_state
                .vars
                .insert(x.clone(), mode)
                .expect("internal error: Typing insert");
        }

        pub(super) fn insert(&mut self, x: &VarIdent, mode: Mode, pv: Option<ProphVar>) {
            if let Some(pv) = pv {
                self.insert_var_mode(x, VarMode::Mode(mode, pv))
            } else {
                assert!(mode == Mode::Spec);
                self.insert_var_mode(x, VarMode::SpecInferProph);
            }
        }

        pub(super) fn infer_as(&mut self, x: &VarIdent, mode: Mode, pv: ProphVar) {
            assert!(self.to_be_inferred(x).is_some());
            self.internal_state.vars.replace(x.clone(), VarMode::Mode(mode, pv)).expect("infer_as");
        }

        pub(super) fn infer_proph_as(&mut self, x: &VarIdent, pv: ProphVar) {
            assert!(self.proph_to_be_inferred(x));
            self.internal_state
                .vars
                .replace(x.clone(), VarMode::Mode(Mode::Spec, pv))
                .expect("infer_as");
        }

        pub(super) fn update_atomic_insts<'a>(&'a mut self) -> &'a mut Option<AtomicInstCollector> {
            &mut self.internal_state.atomic_insts
        }
    }

    impl std::ops::Deref for Typing<'_> {
        type Target = State;

        fn deref(&self) -> &State {
            &self.internal_state
        }
    }
}
use typing::Typing;

impl State {
    fn get<'a>(&'a self, x: &VarIdent, span: &Span) -> Result<(Mode, &'a ProphVar), VirErr> {
        if let VarMode::Mode(mode, proph) = self.vars.get(x).expect("internal error: missing mode")
        {
            Ok((*mode, proph))
        } else {
            return Err(error(span, "uninitialized infer-mode variable"));
        }
    }
}

// One tricky thing in mode-checking is that an invariant block needs to have
// *at most one* atomic instruction in it.
// Thus, we can't just declare everything inside it to be 'proof' code,
// but we can't allow it all to be 'exec' code either.
// Instead, we need to measure *how much* exec code there is.
//
// Our plan is to pass around this AtomicInstCollector object. We instantiate a fresh
// one when we begin an atomic block; as we traverse the atomic block, we collect
// relevant information; when we're done with the block,
// we look at what we picked up and error if necessary.
// For simplicity, we just wait until the end of the block for the validation,
// rather than erroring as soon as we find something bad.
//
// Note that we aren't interested in local manipulations like field accesses,
// even if it's exec code. (We just need to make sure any exec code is terminating.)
// What we're really interested in is *calls*. Any call can either be "atomic"
// (if it is marked as such as its definition) or "non-atomic" (anything else).
// Any non-atomic call at all is an error. It's also an error to have >= 2 atomic calls.
//
// We disallow loops entirely. (It would be OK to allow proof-only loops, but those
// currently aren't supported at all.) We don't do anything fancy for branching statements.
// In principle, we could do something fancy and allow 1 atomic instruction in each branch,
// but for now we just error if there is more than 1 atomic call in the AST.

#[derive(Default, Clone)]
struct AtomicInstCollector {
    atomics: Vec<Span>,
    non_atomics: Vec<Span>,
    loops: Vec<Span>,
}

impl AtomicInstCollector {
    fn new() -> AtomicInstCollector {
        Default::default()
    }

    fn add_atomic(&mut self, span: &Span) {
        self.atomics.push(span.clone());
    }

    fn add_non_atomic(&mut self, span: &Span) {
        self.non_atomics.push(span.clone());
    }

    fn add_loop(&mut self, span: &Span) {
        self.loops.push(span.clone());
    }

    /// Check that the collected operations are well-formed; error if not
    /// `is_atomic_fn` is for error-reporting purposes; if 'true', then the check
    /// is for a fn marked #[verifier(atomic)]. Otherwise, it's for a invariant block.
    pub fn validate(&self, inv_block_span: &Span, is_atomic_fn: bool) -> Result<(), VirErr> {
        let context = if is_atomic_fn { "atomic function" } else { "open_atomic_invariant" };

        if self.loops.len() > 0 {
            return Err(error_with_label(
                inv_block_span,
                format!("{context:} cannot contain an 'exec' loop"),
                "this invariant block contains a loop",
            )
            .secondary_span(&self.loops[0]));
        } else if self.non_atomics.len() > 0 {
            let mut e =
                error(inv_block_span, format!("{context:} cannot contain non-atomic operations"));
            for i in 0..min(self.non_atomics.len(), 3) {
                e = e.secondary_label(&self.non_atomics[i], "non-atomic here");
            }
            return Err(e);
        } else if self.atomics.len() > 1 {
            let mut e = error(
                inv_block_span,
                format!("{context:} cannot contain more than 1 atomic operation"),
            );
            for i in 0..min(self.atomics.len(), 3) {
                e = e.secondary_label(&self.atomics[i], "atomic here");
            }
            return Err(e);
        }
        Ok(())
    }
}

fn add_pattern(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    mode: Mode,
    proph_var: Option<ProphVar>,
    pattern: &Pattern,
) -> Result<(), VirErr> {
    let mut decls = vec![];
    add_pattern_rec(ctxt, record, typing, &mut decls, mode, pattern, false)?;
    for decl in decls {
        let PatternBoundDecl { span: _, name, mode } = decl;
        typing.insert(&name, mode, proph_var.clone());
        record.var_modes.insert(name.clone(), mode);
    }
    Ok(())
}

struct PatternBoundDecl {
    span: Span,
    name: VarIdent,
    mode: Mode,
}

fn add_pattern_rec(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    decls: &mut Vec<PatternBoundDecl>,
    mode: Mode,
    pattern: &Pattern,
    // Is the parent node of this node an 'Or'
    in_or: bool,
) -> Result<(), VirErr> {
    // Testing this condition prevents us from adding duplicate spans into var_modes
    if !(in_or && matches!(&pattern.x, PatternX::Or(..)))
        && !matches!(&pattern.x, PatternX::Wildcard(true))
        && !matches!(&pattern.x, PatternX::Expr(_))
        && !matches!(&pattern.x, PatternX::ImmutRef(_))
        && !matches!(&pattern.x, PatternX::MutRef(_))
    {
        record.erasure_modes.var_modes.push((pattern.span.clone(), mode));
    }

    match &pattern.x {
        PatternX::Wildcard(_dd) => Ok(()),
        PatternX::Var(PatternBinding { name: x, user_mut: _, by_ref, typ: _, copy: _ }) => {
            check_binding(&pattern.span, by_ref, mode)?;
            decls.push(PatternBoundDecl { span: pattern.span.clone(), name: x.clone(), mode });
            Ok(())
        }
        PatternX::Binding {
            binding: PatternBinding { name: x, user_mut: _, by_ref, typ: _, copy: _ },
            sub_pat,
        } => {
            check_binding(&pattern.span, by_ref, mode)?;
            add_pattern_rec(ctxt, record, typing, decls, mode, sub_pat, false)?;
            decls.push(PatternBoundDecl { span: pattern.span.clone(), name: x.clone(), mode });
            Ok(())
        }
        PatternX::Constructor(dt, variant, patterns) => {
            let variant = match dt {
                Dt::Path(path) => {
                    let datatype = &ctxt.datatypes[path];
                    Some(
                        datatype
                            .x
                            .variants
                            .iter()
                            .find(|v| v.name == *variant)
                            .expect("missing variant"),
                    )
                }
                Dt::Tuple(_arity) => None,
            };

            for binder in patterns.iter() {
                let field_mode = match variant {
                    Some(variant) => get_field(&variant.fields, &binder.name).a.1,
                    None => Mode::Exec, // mode of a tuple field is Exec
                };
                add_pattern_rec(
                    ctxt,
                    record,
                    typing,
                    decls,
                    mode_join(field_mode, mode),
                    &binder.a,
                    false,
                )?;
            }
            Ok(())
        }
        PatternX::Or(pat1, pat2) => {
            let mut decls1 = vec![];
            let mut decls2 = vec![];
            add_pattern_rec(ctxt, record, typing, &mut decls1, mode, pat1, true)?;
            add_pattern_rec(ctxt, record, typing, &mut decls2, mode, pat2, true)?;

            // Rust type-checking should have made sure that both sides
            // of the pattern bound the same variables with the same types.
            // But we need to check that they have the same modes.

            assert!(decls1.len() == decls2.len());
            for d1 in decls1 {
                let d2 = decls2
                    .iter()
                    .find(|d| d.name == d1.name)
                    .expect("both sides of 'or' pattern should bind the same variables");

                if d1.mode != d2.mode {
                    let e = error_bare(format!(
                        "variable `{}` has different modes across alternatives separated by `|`",
                        user_local_name(&d1.name)
                    ));
                    let e = e.primary_label(&d1.span, format!("has mode `{}`", d1.mode));
                    let e = e.primary_label(&d2.span, format!("has mode `{}`", d2.mode));
                    return Err(e);
                }

                decls.push(d1);
            }

            Ok(())
        }
        PatternX::Expr(expr) => {
            check_expr_in_pattern(expr)?;
            check_expr_has_mode(ctxt, record, typing, mode, expr, mode, &Proph::No)?;
            Ok(())
        }
        PatternX::Range(expr1, expr2) => {
            if let Some(expr1) = expr1 {
                check_expr_in_pattern(expr1)?;
                check_expr_has_mode(ctxt, record, typing, mode, expr1, mode, &Proph::No)?;
            }
            if let Some((expr2, _ineq_op)) = expr2 {
                check_expr_in_pattern(expr2)?;
                check_expr_has_mode(ctxt, record, typing, mode, expr2, mode, &Proph::No)?;
            }
            Ok(())
        }
        PatternX::ImmutRef(sub_pat) => {
            add_pattern_rec(ctxt, record, typing, decls, mode, sub_pat, false)
        }
        PatternX::MutRef(sub_pat) => {
            add_pattern_rec(ctxt, record, typing, decls, mode, sub_pat, false)
        }
    }
}

fn check_binding(span: &Span, by_ref: &ByRef, mode: Mode) -> Result<(), VirErr> {
    match (by_ref, mode) {
        (ByRef::MutRef, Mode::Spec | Mode::Proof) => {
            // Supporting this for Mode::Proof would be nice but requires thought for how
            // to implement.
            Err(error(span, "a 'mut ref' binding in a pattern is only allowed for exec mode"))
        }
        (ByRef::No | ByRef::ImmutRef, _) => Ok(()),
        (_, Mode::Exec) => Ok(()),
    }
}

fn check_expr_in_pattern(expr: &Expr) -> Result<(), VirErr> {
    match &expr.x {
        ExprX::ConstVar(_, _) => Ok(()),
        ExprX::Const(_) => Ok(()),
        ExprX::Binary(
            BinaryOp::Arith(crate::ast::ArithOp::Sub(OverflowBehavior::Allow)),
            expr1,
            expr2,
        ) => {
            check_expr_in_pattern(expr1)?;
            check_expr_in_pattern(expr2)
        }
        _ => Err(error(&expr.span, "Verus Internal Error: bad PatternX::Expr")),
    }
}

fn get_var_loc_mode(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    expr_inner_mode: Option<Mode>,
    expr: &Expr,
) -> Result<(Mode, Proph), VirErr> {
    let (x_mode, x_proph) = match &expr.x {
        ExprX::VarLoc(x) => {
            let (x_mode, x_proph) = typing.get(x, &expr.span)?;
            let x_proph = x_proph.to_proph(x, &expr.span);

            record.erasure_modes.var_modes.push((expr.span.clone(), x_mode));

            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && x_mode != Mode::Exec
            {
                return Err(error(&expr.span, "exec code cannot mutate non-exec variable"));
            }

            (x_mode, x_proph)
        }
        ExprX::Unary(
            UnaryOp::CoerceMode { op_mode, from_mode, to_mode, kind: ModeCoercion::BorrowMut },
            e1,
        ) => {
            if ctxt.check_ghost_blocks {
                if (*op_mode == Mode::Exec) != (typing.block_ghostness == Ghost::Exec) {
                    return Err(error(
                        &expr.span,
                        format!("cannot perform operation with mode {}", op_mode),
                    ));
                }
            }
            if outer_mode != *op_mode {
                return Err(error(
                    &expr.span,
                    format!("cannot perform operation with mode {}", op_mode),
                ));
            }
            let (mode1, proph1) =
                get_var_loc_mode(ctxt, record, typing, outer_mode, Some(*to_mode), e1)?;
            if !mode_le(mode1, *from_mode) {
                return Err(error(
                    &expr.span,
                    format!("expected mode {}, found mode {}", *from_mode, mode1),
                ));
            }
            (*to_mode, proph1)
        }
        ExprX::UnaryOpr(
            UnaryOpr::Field(FieldOpr { datatype, variant: _, field, get_variant, check: _ }),
            rcvr,
        ) => {
            let (rcvr_mode, rcvr_proph) =
                get_var_loc_mode(ctxt, record, typing, outer_mode, expr_inner_mode, rcvr)?;
            record
                .type_inv_info
                .field_loc_needs_check
                .insert(expr.span.id, rcvr_mode != Mode::Spec);
            let field_mode = match datatype {
                Dt::Path(path) => {
                    let datatype = &ctxt.datatypes[path].x;
                    assert!(datatype.variants.len() == 1);
                    let (_, field_mode, _) = &datatype.variants[0]
                        .fields
                        .iter()
                        .find(|x| x.name == *field)
                        .expect("datatype field valid")
                        .a;
                    *field_mode
                }
                Dt::Tuple(_arity) => Mode::Exec,
            };
            let call_mode = if *get_variant { Mode::Spec } else { rcvr_mode };
            (mode_join(call_mode, field_mode), rcvr_proph)
        }
        ExprX::Block(stmts, Some(e1)) if stmts.len() == 0 => {
            // For now, only support the special case for Tracked::borrow_mut.
            get_var_loc_mode(ctxt, record, typing, outer_mode, None, e1)?
        }
        ExprX::Ghost { alloc_wrapper: false, tracked: true, expr: e1 } => {
            // For now, only support the special case for Tracked::borrow_mut.
            let mut typing = typing.push_block_ghostness(Ghost::Ghost);
            let mode = get_var_loc_mode(ctxt, record, &mut typing, outer_mode, None, e1)?;
            mode
        }
        _ => {
            panic!("unexpected loc {:?}", expr);
        }
    };
    Ok((x_mode, x_proph))
}

fn check_place_has_mode(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    place: &Place,
    expected: Mode,
    access: PlaceAccess,
    outer_proph: &Proph,
) -> Result<Proph, VirErr> {
    let (mode, p) = check_place(
        ctxt,
        record,
        typing,
        outer_mode,
        place,
        access,
        Expect(expected),
        outer_proph,
    )?;
    if is_unit(&place.typ) {
        return Ok(Proph::No);
    }
    if !mode_le(mode, expected) {
        Err(error(&place.span, format!("expression has mode {}, expected mode {}", mode, expected)))
    } else {
        Ok(p)
    }
}

#[derive(Copy, Clone)]
enum PlaceAccess {
    Read,
    MutAssign,
    MutBorrow,
}

impl PlaceAccess {
    fn is_mut(&self) -> bool {
        match self {
            PlaceAccess::MutAssign | PlaceAccess::MutBorrow => true,
            PlaceAccess::Read => false,
        }
    }
}

struct ProofModeMutRefNote(Place, Place);

fn check_place(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    place: &Place,
    access: PlaceAccess,
    expect: Expect,
    outer_proph: &Proph,
) -> Result<(Mode, Proph), VirErr> {
    let mut note = None;
    let (place_mode, proph) = check_place_rec(
        ctxt,
        record,
        typing,
        &mut note,
        outer_mode,
        place,
        access,
        expect,
        outer_proph,
    )?;

    let mut context_mode = typing.block_ghostness.join_mode(outer_mode);
    if typing.in_forall_stmt || typing.in_proof_in_spec {
        context_mode = Mode::Spec;
    }

    let final_mode = match access {
        PlaceAccess::Read => {
            // For non-mutating: coerce the mode to whatever is necessary for the context.

            // We also apply coerce to the "expected mode" here in order to compute the optimal
            // mode to put into var_modes (see below)

            let coerced_mode = mode_join(mode_join(place_mode, context_mode), expect.0);
            coerced_mode
        }
        PlaceAccess::MutAssign => {
            // If mutating assignment: we can't coerce the mode;
            // thus, if a coercion is needed, then we produce an error.
            //
            // Note that we only need to do this coercion at the top-level Place node,
            // since for example, it's okay to do `x.foo = ...` in ghost code
            // even if `x` is exec but x.foo is ghost.
            let coerced_mode = mode_join(place_mode, context_mode);

            if coerced_mode == Mode::Proof && place_mode == Mode::Exec {
                // There are some special cases to allow mutating an
                // exec-place via a mutable reference in proof code.
                if !ok_to_assign_exec_place_in_erased_code(ctxt, place) {
                    let mut e = error_with_label(
                        &place.span,
                        format!("cannot mutate {place_mode}-mode place in {context_mode}-code"),
                        if note.is_some() {
                            format!("this place may have mode {place_mode}")
                        } else {
                            format!("this place has mode {place_mode}")
                        },
                    );
                    if let Some(note) = note {
                        e = e.secondary_label(&note.1.span, "this mutable reference has mode `tracked`, but may point to an exec-mode location");
                        e = e.help(format!("Verus assumes any mutable reference may point to an exec-mode location unless it can determine otherwise based on the type. You can use the `Tracked` wrapper to force Verus to treat the location as tracked, e.g., try `&mut Tracked<{}>`", typ_to_diagnostic_str(&note.0.typ)));
                    }
                    return Err(e);
                }
            } else if coerced_mode != place_mode {
                return Err(error_with_label(
                    &place.span,
                    format!("cannot mutate {place_mode}-mode place in {context_mode}-code"),
                    "this place has mode {place_mode}",
                ));
            }

            coerced_mode
        }
        PlaceAccess::MutBorrow => {
            // Don't coerce because we want to be able to take
            // mut-borrows to exec places from proof code.
            // (This is safe because we still cannot modify the exec state through the reference)
            place_mode
        }
    };

    // How we do erasure depends on whether we are accessing the place mutably or not.
    // For an expression like `x.f`, if the local variable `x` is non-spec and `x.f` is spec,
    // then for *mutations* we want to keep the expression during erasure.
    // So then `consume(x); x.f = ...` will give an "x has been moved" error.
    // However, if we're just reading from the place, we want to erase the whole expression.
    // Thus, for non-mut, we record the mode of the *whole expression*, and for mut,
    // we stor the mode of the local (the second case is in `check_place_rec`).
    if !access.is_mut() {
        if let Some(var_place) = crate::ast_util::place_get_local(place) {
            record.erasure_modes.var_modes.push((var_place.span.clone(), final_mode));
        }
    }

    Ok((final_mode, proph))
}

fn check_place_rec(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    note: &mut Option<ProofModeMutRefNote>,
    outer_mode: Mode,
    place: &Place,
    access: PlaceAccess,
    expect: Expect,
    outer_proph: &Proph,
) -> Result<(Mode, Proph), VirErr> {
    let (mode, proph) = check_place_rec_inner(
        ctxt,
        record,
        typing,
        note,
        outer_mode,
        place,
        access,
        expect,
        outer_proph,
    )?;
    if ctxt.check_ghost_blocks
        && matches!(typing.block_ghostness, Ghost::Exec)
        && mode != Mode::Exec
        && !(matches!(&place.x, PlaceX::Temporary(..)) && is_unit(&place.typ))
    {
        return Err(error(
            &place.span,
            if matches!(&place.x, PlaceX::Temporary(..)) {
                format!("cannot use {mode}-mode expression in executable context")
            } else {
                format!("cannot access {mode}-mode place in executable context")
            },
        ));
    }
    Ok((mode, proph))
}

fn check_place_rec_inner(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    note: &mut Option<ProofModeMutRefNote>,
    outer_mode: Mode,
    place: &Place,
    access: PlaceAccess,
    expect: Expect,
    outer_proph: &Proph,
) -> Result<(Mode, Proph), VirErr> {
    match &place.x {
        PlaceX::Field(FieldOpr { datatype, variant, field, get_variant: _, check: _ }, p) => {
            let (mode, proph) = check_place_rec(
                ctxt,
                record,
                typing,
                note,
                outer_mode,
                p,
                access,
                expect,
                outer_proph,
            )?;

            let field_mode = match datatype {
                Dt::Path(path) => {
                    let datatype = &ctxt.datatypes[path];
                    let field = get_field(&datatype.x.get_variant(variant).fields, field);
                    field.a.1
                }
                Dt::Tuple(_) => Mode::Exec,
            };

            Ok((mode_join(mode, field_mode), proph))
        }
        PlaceX::DerefMut(p) => {
            let (mode, proph) = check_place_rec(
                ctxt,
                record,
                typing,
                note,
                outer_mode,
                p,
                access,
                expect,
                outer_proph,
            )?;
            if mode == Mode::Spec && access.is_mut() {
                // In principle we could allow mutating the 'current' field a ghost mutable
                // reference. However, this probably has unintuitive behavior (i.e., it wouldn't
                // cause an update to any other place) so I disallow it.
                return Err(error(
                    &place.span,
                    &format!("cannot mutate through a spec-mode mutable reference"),
                ));
            }

            // The 'dereference' of a mutable reference is always considered an exec place,
            // even if the reference itself is only tracked.
            if mode == Mode::Proof {
                // If this case occurs, make a note of it in case we need it for diagnostics
                *note = Some(ProofModeMutRefNote(place.clone(), p.clone()));
            }

            Ok((Mode::Exec, proph))
        }
        PlaceX::Local(var) => {
            let (mode, proph) = typing.get(var, &place.span)?;
            let proph = proph.to_proph(var, &place.span);

            // Other case is handled in `check_place`; see the explanation there.
            if access.is_mut() {
                record.erasure_modes.var_modes.push((place.span.clone(), mode));
            }

            Ok((mode, proph))
        }
        PlaceX::Temporary(e) => {
            let (mode, proph) =
                check_expr(ctxt, record, typing, outer_mode, expect, e, outer_proph)?;

            if ctxt.new_mut_ref {
                if record.temporary_modes.contains_key(&place.span.id) {
                    return Err(error(
                        &place.span,
                        &format!("Verus Internal Error: duplicate PlaceX::Temporary ID"),
                    ));
                }
                record.temporary_modes.insert(place.span.id, mode);
            }

            Ok((mode, proph))
        }
        PlaceX::ModeUnwrap(p, wrapper_mode) => {
            let (mode, proph) = check_place_rec(
                ctxt,
                record,
                typing,
                note,
                outer_mode,
                p,
                access,
                expect,
                outer_proph,
            )?;
            let mode = mode_join(mode, wrapper_mode.to_mode());
            Ok((mode, proph))
        }
        PlaceX::WithExpr(..) => {
            return Err(error(
                &place.span,
                &format!("Verus Internal Error: WithExpr node shouldn't exist yet"),
            ));
        }
        PlaceX::Index(p, idx, _kind, _needs_bounds_check) => {
            let idx_expect = match typing.block_ghostness {
                Ghost::Exec => Expect(Mode::Exec),
                Ghost::Ghost => Expect(Mode::Spec),
            };

            let (place_mode, place_proph) = check_place_rec(
                ctxt,
                record,
                typing,
                note,
                outer_mode,
                p,
                access,
                expect,
                outer_proph,
            )?;
            let (idx_mode, idx_proph) =
                check_expr(ctxt, record, typing, outer_mode, idx_expect, idx, outer_proph)?;

            if ctxt.check_ghost_blocks
                && matches!(typing.block_ghostness, Ghost::Exec)
                && idx_mode != Mode::Exec
            {
                return Err(error(
                    &place.span,
                    format!("cannot use {idx_mode}-mode expression in executable context"),
                ));
            }

            idx_proph.check(&place.span, NoProphReason::Index)?;

            // Why not return mode_join(place_mode, idx_mode)?
            // This function returns the mode of the place itself, not the mode of the
            // expression, so the mode of the indexed place is the same as the mode
            // of the slice/array place.
            // e.g.,
            //   tracked[spec] -> tracked
            //   exec[spec] -> exec
            // If we try to do `exec[spec]` outside a ghost block, it will get caught by
            // the above check.
            Ok((place_mode, place_proph))
        }
    }
}

/// Determine if it's okay to assign to the given place in tracked mode even if the
/// place is determined to be Exec.
///
/// This should be sound if either of the following are true:
///  1. The type is a ZST
///  2. The type is tracked (and thus couldn't exist in an exec-mode place to begin with)
///
/// For (1), we're keeping our check a little weaker,
///
/// It would be really nice to support `Option<T>`, but the problem is that this is a non-ZST;
/// even if T is tracked, it's possible to create an `Option<T>` in exec-mode via `None`
/// and prohibiting this would be difficult to do.
fn ok_to_assign_exec_place_in_erased_code(ctxt: &Ctxt, place: &Place) -> bool {
    // Always say no if this doesn't involve a mutable reference.
    // This isn't really necessary as a restriction, but it's only for mutable references
    // that we need this extra allowance in the first place.
    if !crate::ast_util::place_has_deref_mut(place) {
        return false;
    }

    // TODO(new_mut_ref): need to make sure type is correct up to decoration
    // for this check to make sense
    match &*place.typ {
        TypX::Decorate(TypDecoration::Ghost | TypDecoration::Tracked, _, _) => {
            return true;
        }
        _ => {}
    }

    let mut place = place;
    loop {
        if type_is_non_exec(ctxt, &place.typ) {
            return true;
        }
        match &place.x {
            PlaceX::Local(_) | PlaceX::Temporary(_) => {
                break;
            }
            PlaceX::DerefMut(_) => {
                break;
            }
            PlaceX::Field(_, p)
            | PlaceX::ModeUnwrap(p, _)
            | PlaceX::WithExpr(_, p)
            | PlaceX::Index(p, ..) => {
                place = p;
            }
        }
    }

    false
}

/// Is it impossible for this type to appear in exec mode?
fn type_is_non_exec(ctxt: &Ctxt, typ: &Typ) -> bool {
    match &**typ {
        TypX::Decorate(
            TypDecoration::Ref
            | TypDecoration::MutRef
            | TypDecoration::Box
            | TypDecoration::Rc
            | TypDecoration::Arc,
            _,
            t,
        ) => type_is_non_exec(ctxt, t),
        TypX::Datatype(dt, typ_args, _) => {
            match dt {
                Dt::Tuple(_) => {
                    for t in typ_args.iter() {
                        if type_is_non_exec(ctxt, t) {
                            return true;
                        }
                    }
                    false
                }
                Dt::Path(path) => {
                    // TODO(new_mut_ref): should allow, e.g., Option<T> where T is non-exec
                    let datatype = &ctxt.datatypes[path];
                    datatype.x.mode != Mode::Exec
                }
            }
        }
        _ => false,
    }
}

fn check_expr_has_mode(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    expr: &Expr,
    expected: Mode,
    outer_proph: &Proph,
) -> Result<Proph, VirErr> {
    let (mode, proph) =
        check_expr(ctxt, record, typing, outer_mode, Expect(expected), expr, outer_proph)?;
    if is_unit(&expr.typ) {
        return Ok(Proph::No);
    }
    if !mode_le(mode, expected) {
        Err(error(&expr.span, format!("expression has mode {}, expected mode {}", mode, expected)))
    } else {
        Ok(proph)
    }
}

fn check_expr(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    expect: Expect,
    expr: &Expr,
    outer_proph: &Proph,
) -> Result<(Mode, Proph), VirErr> {
    let (mode, _, proph) =
        check_expr_handle_mut_arg(ctxt, record, typing, outer_mode, expect, expr, outer_proph)?;
    Ok((mode, proph))
}

fn check_expr_handle_mut_arg(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    expect: Expect,
    expr: &Expr,
    outer_proph: &Proph,
) -> Result<(Mode, Option<Mode>, Proph), VirErr> {
    if let Some(r) = outer_reason_by_expr_kind(expr) {
        outer_proph.outer_check(&expr.span, r)?;
    }

    let mode_proph = match &expr.x {
        ExprX::Const(_) => Ok((Mode::Exec, Proph::No)),
        ExprX::Var(x) | ExprX::VarLoc(x) | ExprX::VarAt(x, _) => {
            let (x_mode, proph) = typing.get(x, &expr.span)?;
            let proph = proph.to_proph(x, &expr.span);

            if typing.in_forall_stmt || typing.in_proof_in_spec {
                // Proof variables may be used as spec, but not as proof inside forall statements.
                // This protects against effectively consuming a linear proof variable
                // multiple times for different instantiations of the forall variables.
                return Ok((Mode::Spec, None, proph));
            }

            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && matches!(&expr.x, ExprX::VarAt(..))
            {
                return Err(error(&expr.span, &format!("cannot use `old` in exec-code")));
            }

            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && x_mode != Mode::Exec
            {
                return Err(error(
                    &expr.span,
                    &format!("cannot use {x_mode} variable in exec-code"),
                ));
            }

            let mode = if matches!(&expr.x, ExprX::VarAt(..)) {
                Mode::Spec
            } else {
                mode_join(outer_mode, x_mode)
            };

            let mode =
                if ctxt.check_ghost_blocks { typing.block_ghostness.join_mode(mode) } else { mode };
            record.erasure_modes.var_modes.push((expr.span.clone(), mode));
            return Ok((mode, Some(x_mode), proph));
        }
        ExprX::ConstVar(x, _) | ExprX::StaticVar(x) => {
            let function = match ctxt.funs.get(x) {
                None => {
                    let name = crate::ast_util::path_as_friendly_rust_name(&x.path);
                    return Err(error(&expr.span, format!("cannot find constant {}", name)));
                }
                Some(f) => f.clone(),
            };
            let kind = if matches!(&expr.x, ExprX::ConstVar(..)) { "const" } else { "static" };
            if ctxt.check_ghost_blocks {
                if function.x.mode == Mode::Exec && typing.block_ghostness != Ghost::Exec {
                    return Err(error(
                        &expr.span,
                        format!("cannot read {} with mode {}", kind, function.x.mode),
                    ));
                }
                if function.x.ret.x.mode != Mode::Exec && typing.block_ghostness == Ghost::Exec {
                    return Err(error(
                        &expr.span,
                        format!("cannot read {} with mode {}", kind, function.x.mode),
                    ));
                }
            }
            if !mode_le(outer_mode, function.x.mode) {
                return Err(error(
                    &expr.span,
                    format!("cannot read {} with mode {}", kind, function.x.mode),
                ));
            }
            let mode = function.x.ret.x.mode;
            let mode =
                if ctxt.check_ghost_blocks { typing.block_ghostness.join_mode(mode) } else { mode };
            record.erasure_modes.var_modes.push((expr.span.clone(), mode));
            Ok((mode, Proph::No))
        }
        ExprX::Call(
            CallTarget::Fun(crate::ast::CallTargetKind::ProofFn(param_modes, ret_mode), _, _, _, _),
            es,
            None,
        ) => {
            // es = [FnProof, (...args...)]
            assert!(es.len() == 2);
            let binders = if let ExprX::Ctor(Dt::Tuple(_), _, binders, None) = &es[1].x {
                binders
            } else {
                return Err(error(&expr.span, "arguments must be a tuple"));
            };
            let mode_error_msg = "cannot call function with mode proof";
            if ctxt.check_ghost_blocks {
                if typing.block_ghostness == Ghost::Exec {
                    return Err(error(&expr.span, mode_error_msg));
                }
            }
            if outer_mode != Mode::Proof {
                return Err(error(&expr.span, mode_error_msg));
            }
            outer_proph.outer_check(&expr.span, OuterProphReason::ProofFnCall)?;
            let p = check_expr_has_mode(
                ctxt,
                record,
                typing,
                Mode::Proof,
                &es[0],
                Mode::Proof,
                &Proph::No,
            )?;
            p.check(&expr.span, NoProphReason::ProofFnCall)?;
            assert!(param_modes.len() == binders.len());
            for (param_mode, binder) in param_modes.iter().zip(binders.iter()) {
                let arg = &binder.a;
                let p = check_expr_has_mode(
                    ctxt,
                    record,
                    typing,
                    Mode::Proof,
                    arg,
                    *param_mode,
                    &Proph::No,
                )?;
                p.check(&expr.span, NoProphReason::ProofFnCall)?;
            }

            Ok((*ret_mode, Proph::No))
        }
        ExprX::Call(CallTarget::Fun(kind, x, _, _, autospec_usage), es, None) => {
            assert!(*autospec_usage == AutospecUsage::Final);

            let function = match ctxt.funs.get(x) {
                None => {
                    let name = crate::ast_util::path_as_friendly_rust_name(&x.path);
                    return Err(error(&expr.span, format!("cannot find function {}", name)));
                }
                Some(f) => f.clone(),
            };

            let mut out_proph = if function.x.attrs.prophecy_dependent {
                match kind {
                    CallTargetKind::DynamicResolved { resolved, .. } => {
                        let resolved_function = ctxt.funs.get(resolved).unwrap();
                        if resolved_function.x.attrs.prophecy_dependent {
                            Proph::Yes(ProphReason {
                                span: expr.span.clone(),
                                kind: ProphReasonKind::SpecFunction(resolved_function.span.clone()),
                            })
                        } else {
                            Proph::No
                        }
                    }
                    _ => Proph::Yes(ProphReason {
                        span: expr.span.clone(),
                        kind: ProphReasonKind::SpecFunction(function.span.clone()),
                    }),
                }
            } else {
                Proph::No
            };
            let (disallow_arg_proph, outer_proph_reason) = function_allows_proph(&function);
            if let Some(outer_proph_reason) = outer_proph_reason {
                outer_proph.outer_check(&expr.span, outer_proph_reason)?;
            }

            if function.x.mode == Mode::Exec {
                match typing.update_atomic_insts() {
                    None => {}
                    Some(ai) => {
                        if function.x.attrs.atomic {
                            ai.add_atomic(&expr.span);
                        } else {
                            // A call to `create_open_invariant_credit` or `spend_open_invariant_credit`
                            // is a no-op, so it's fine to include in an atomic block. And it's useful
                            // to be able to do so, so that we can nest an opening of an invariant
                            // inside an opening of another invariant. So we special-case these calls
                            // to not treat them as non-atomic.
                            if !ctxt
                                .special_paths
                                .is_create_or_spend_open_invariant_credit_path(&x.path)
                            {
                                ai.add_non_atomic(&expr.span);
                            }
                        }
                    }
                }
            }
            let mode_error_msg = || {
                if ctxt.special_paths.is_exec_nonstatic_call_path(&x.path) {
                    format!("to call a non-static function in ghost code, it must be a spec_fn")
                } else {
                    let name = crate::ast_util::path_as_friendly_rust_name(&x.path);
                    format!("cannot call function `{}` with mode {}", name, function.x.mode)
                }
            };
            if ctxt.check_ghost_blocks {
                if (function.x.mode == Mode::Exec) != (typing.block_ghostness == Ghost::Exec) {
                    return Err(error(&expr.span, mode_error_msg()));
                }
            }
            if !mode_le(outer_mode, function.x.mode) {
                return Err(error(&expr.span, mode_error_msg()));
            }
            for (param, arg) in function.x.params.iter().zip(es.iter()) {
                let param_mode = mode_join(outer_mode, param.x.mode);
                if param.x.is_mut {
                    if typing.in_forall_stmt {
                        return Err(error(
                            &arg.span,
                            "cannot call function with &mut parameter inside 'assert ... by' statements",
                        ));
                    }
                    if typing.in_proof_in_spec {
                        return Err(error(
                            &arg.span,
                            "cannot call function with &mut parameter inside spec",
                        ));
                    }
                    let (arg_mode_read, arg_mode_write, proph) = check_expr_handle_mut_arg(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        Expect::none(),
                        arg,
                        outer_proph,
                    )?;
                    proph.check(&arg.span, NoProphReason::MutBorrowArgument)?;
                    let arg_mode_write = if let Some(arg_mode_write) = arg_mode_write {
                        arg_mode_write
                    } else {
                        return Err(error(
                            &arg.span,
                            format!("cannot write to argument with mode {}", param_mode),
                        ));
                    };
                    if arg_mode_read != param_mode {
                        return Err(error(
                            &arg.span,
                            format!(
                                "expected mode {}, &mut argument has mode {}",
                                param_mode, arg_mode_read
                            ),
                        ));
                    }
                    if arg_mode_write != param_mode {
                        return Err(error(
                            &arg.span,
                            format!(
                                "expected mode {}, &mut argument has mode {}",
                                param_mode, arg_mode_write
                            ),
                        ));
                    }
                } else {
                    let p = check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        param_mode,
                        arg,
                        param.x.mode,
                        outer_proph,
                    )?;
                    if let Some(disallow_arg_proph) = disallow_arg_proph {
                        p.check(&arg.span, disallow_arg_proph)?;
                    };
                    out_proph = out_proph.join(p);
                }
            }
            Ok((function.x.ret.x.mode, out_proph))
        }
        ExprX::Call(CallTarget::FnSpec(e0), es, None) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot call spec function from exec mode"));
            }
            let mut proph =
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, e0, Mode::Spec, outer_proph)?;
            for arg in es.iter() {
                let p = check_expr_has_mode(
                    ctxt,
                    record,
                    typing,
                    Mode::Spec,
                    arg,
                    Mode::Spec,
                    outer_proph,
                )?;
                proph = proph.join(p);
            }
            Ok((Mode::Spec, proph))
        }
        ExprX::Call(CallTarget::BuiltinSpecFun(_f, _typs, _impl_paths), es, None) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot call spec function from exec mode"));
            }
            let mut proph = Proph::No;
            for arg in es.iter() {
                let p = check_expr_has_mode(
                    ctxt,
                    record,
                    typing,
                    Mode::Spec,
                    arg,
                    Mode::Spec,
                    outer_proph,
                )?;
                proph = proph.join(p);
            }
            Ok((Mode::Spec, proph))
        }
        ExprX::Call(_, _, Some(_)) => {
            return Err(error(&expr.span, "ExprX::Call should not have post_args at this point"));
        }
        ExprX::ArrayLiteral(es) => {
            let modes = vec_map_result(es, |e| {
                check_expr(ctxt, record, typing, outer_mode, expect, e, outer_proph)
            })?;
            Ok(modes.into_iter().fold((Mode::Exec, Proph::No), mode_proph_join))
        }
        ExprX::Ctor(dt, variant, binders, update) => {
            let (variant_opt, mut mode) = match dt {
                Dt::Path(path) => {
                    let datatype = &ctxt.datatypes[path];
                    let variant = datatype.x.get_variant(variant);
                    let mode = datatype.x.mode;
                    (Some(variant), mode)
                }
                Dt::Tuple(_) => (None, Mode::Exec),
            };

            let get_field_mode = |field_ident: &crate::ast::Ident| {
                match variant_opt {
                    Some(variant) => get_field(&variant.fields, field_ident).a.1,
                    None => Mode::Exec, // tuple field is Mode exec
                }
            };

            let mut proph = Proph::No;

            for arg in binders.iter() {
                let field_mode = get_field_mode(&arg.name);
                let field_expect = Expect(expect.join(field_mode));
                let (arg_mode, arg_proph) = check_expr(
                    ctxt,
                    record,
                    typing,
                    mode_join(outer_mode, field_mode),
                    field_expect,
                    &arg.a,
                    outer_proph,
                )?;
                if !mode_le(arg_mode, field_mode) {
                    // allow this arg by weakening whole struct's mode
                    mode = mode_join(mode, arg_mode);
                }
                proph = proph.join(arg_proph);
            }
            if let Some(CtorUpdateTail { place, taken_fields }) = update {
                let place_expect = if typing.block_ghostness == Ghost::Exec {
                    Expect(Mode::Exec)
                } else {
                    let mut place_expect = Expect(Mode::Spec);
                    for (taken_field, _) in taken_fields.iter() {
                        let field_mode = get_field_mode(taken_field);
                        let field_mode_expect = expect.join(field_mode);
                        place_expect = Expect(place_expect.meet(field_mode_expect));
                    }
                    place_expect
                };

                let (place_mode, place_proph) = check_place(
                    ctxt,
                    record,
                    typing,
                    outer_mode,
                    place,
                    PlaceAccess::Read,
                    place_expect,
                    outer_proph,
                )?;

                for (taken_field, _) in taken_fields.iter() {
                    let field_mode = get_field_mode(taken_field);
                    let arg_mode = mode_join(place_mode, field_mode);
                    if !mode_le(arg_mode, field_mode) {
                        // allow this arg by weakening whole struct's mode
                        mode = mode_join(mode, arg_mode);
                    }
                }

                proph = proph.join(place_proph);
            }

            record.type_inv_info.ctor_needs_check.insert(expr.span.id, mode != Mode::Spec);
            if !matches!(dt, Dt::Tuple(_)) {
                record.erasure_modes.ctor_modes.push((expr.span.clone(), mode));
            }

            // Now that we've computed the final mode of this struct expr, go back through
            // all the 'take_fields' and see which ones require moves.
            if let Some(CtorUpdateTail { place: _, taken_fields }) = update {
                for (taken_field, read_kind) in taken_fields.iter() {
                    let field_mode = get_field_mode(taken_field);
                    let arg_mode = mode_join(field_mode, mode);

                    let final_read_kind = match arg_mode {
                        Mode::Spec => ReadKind::Spec,
                        _ => read_kind.preliminary_kind,
                    };
                    record.read_kind_finals.insert(read_kind.id, final_read_kind);
                }
            }

            Ok((mode, proph))
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(_)) => Ok((Mode::Exec, Proph::No)),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TraitBound(..)) => Ok((Mode::Spec, Proph::No)),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(..)) => {
            Ok((Mode::Spec, Proph::No))
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(..)) => Ok((Mode::Spec, Proph::No)),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter) => {
            Ok((Mode::Spec, Proph::No))
        }
        ExprX::Unary(UnaryOp::CoerceMode { op_mode, from_mode, to_mode, kind }, e1) => {
            // same as a call to an op_mode function with parameter from_mode and return to_mode
            if ctxt.check_ghost_blocks {
                if (*op_mode == Mode::Exec) != (typing.block_ghostness == Ghost::Exec) {
                    return Err(error(
                        &expr.span,
                        format!("cannot perform operation with mode {}", op_mode),
                    ));
                }
            }
            if !mode_le(outer_mode, *op_mode) {
                return Err(error(
                    &expr.span,
                    format!("cannot perform operation with mode {}", op_mode),
                ));
            }
            let param_mode = mode_join(outer_mode, *from_mode);
            match kind {
                ModeCoercion::BorrowMut => {
                    let proph = check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        param_mode,
                        e1,
                        *from_mode,
                        outer_proph,
                    )?;
                    return Ok((*to_mode, Some(*to_mode), proph));
                }
                ModeCoercion::Constructor | ModeCoercion::Field => {
                    let (mode, proph) = check_expr(
                        ctxt,
                        record,
                        typing,
                        param_mode,
                        Expect(expect.join(*from_mode)),
                        e1,
                        outer_proph,
                    )?;
                    if *kind == ModeCoercion::Constructor {
                        let m = if !mode_le(mode, *from_mode) { mode } else { *to_mode };
                        let m = expect.join(m);
                        if m != Mode::Spec {
                            let reason = if *from_mode == Mode::Proof {
                                NoProphReason::TrackedWrap
                            } else {
                                NoProphReason::GhostWrap
                            };
                            proph.check(&expr.span, reason)?;
                        }
                        Ok((m, proph))
                    } else {
                        Ok((mode_join(mode, *to_mode), proph))
                    }
                }
            }
        }
        ExprX::Unary(UnaryOp::HeightTrigger, _) => {
            panic!("direct access to 'height' is not allowed")
        }
        ExprX::Unary(UnaryOp::InferSpecForLoopIter { .. }, e1) => {
            // InferSpecForLoopIter is a loop-invariant hint that always has mode spec.
            // If the expression already has mode spec (e.g. because the function calls
            // are all autospec), then keep the expression.
            // Otherwise, make a note that the expression had mode exec,
            // so that check_function can replace the expression with NoInferSpecForLoopIter.
            let mut typing = typing.push_restore_on_error();
            let mode_opt = check_expr(
                ctxt,
                record,
                &mut typing,
                outer_mode,
                Expect(Mode::Spec),
                e1,
                outer_proph,
            );
            let (mode, proph) = mode_opt.unwrap_or((Mode::Exec, Proph::No));
            if let Some(infer_spec) = record.infer_spec_for_loop_iter_modes.as_mut() {
                infer_spec.push((expr.span.clone(), mode));
            } else {
                return Err(error(
                    &expr.span,
                    "infer_spec_for_loop_iter is only allowed in function body",
                ));
            }
            Ok((Mode::Spec, proph))
        }
        ExprX::Unary(UnaryOp::MutRefFuture(source_name), e1) => {
            check_expr(ctxt, record, typing, Mode::Spec, Expect(Mode::Spec), e1, outer_proph)?;
            let proph = Proph::Yes(ProphReason {
                span: expr.span.clone(),
                kind: ProphReasonKind::MutRefFuture(*source_name),
            });
            Ok((Mode::Spec, proph))
        }
        ExprX::Unary(UnaryOp::MutRefCurrent, e1) => {
            let (_m, proph) =
                check_expr(ctxt, record, typing, Mode::Spec, Expect(Mode::Spec), e1, outer_proph)?;
            Ok((Mode::Spec, proph))
        }
        ExprX::Unary(_, e1) => {
            check_expr(ctxt, record, typing, outer_mode, expect, e1, outer_proph)
        }
        ExprX::UnaryOpr(UnaryOpr::Box(_), _) => panic!("unexpected box"),
        ExprX::UnaryOpr(UnaryOpr::Unbox(_), _) => panic!("unexpected box"),
        ExprX::UnaryOpr(UnaryOpr::HasType(_), _) => panic!("internal error: HasType in modes.rs"),
        ExprX::UnaryOpr(UnaryOpr::IsVariant { .. }, e1) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot test variant in exec mode"));
            }
            check_expr(ctxt, record, typing, outer_mode, Expect(Mode::Spec), e1, outer_proph)
        }
        ExprX::UnaryOpr(
            UnaryOpr::Field(FieldOpr { datatype, variant, field, get_variant, check: _ }),
            e1,
        ) => {
            if *get_variant && ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot get variant in exec mode"));
            }
            let (e1_mode_read, e1_mode_write, proph) = check_expr_handle_mut_arg(
                ctxt,
                record,
                typing,
                outer_mode,
                expect,
                e1,
                outer_proph,
            )?;

            record
                .type_inv_info
                .field_loc_needs_check
                .insert(expr.span.id, e1_mode_write != None && e1_mode_write != Some(Mode::Spec));

            let field_mode = match datatype {
                Dt::Path(path) => {
                    let datatype = &ctxt.datatypes[path];
                    let field = get_field(&datatype.x.get_variant(variant).fields, field);
                    field.a.1
                }
                Dt::Tuple(_) => Mode::Exec,
            };
            let mode_read =
                if *get_variant { Mode::Spec } else { mode_join(e1_mode_read, field_mode) };
            if let Some(e1_mode_write) = e1_mode_write {
                return Ok((mode_read, Some(mode_join(e1_mode_write, field_mode)), proph));
            } else {
                Ok((mode_read, proph))
            }
        }
        ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(_kind, min_mode), e1) => {
            let joined_mode = mode_join(outer_mode, *min_mode);
            let (mode, proph) =
                check_expr(ctxt, record, typing, joined_mode, Expect(*min_mode), e1, outer_proph)?;
            Ok((mode_join(*min_mode, mode), proph))
        }
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), e1) => {
            let p =
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, e1, Mode::Spec, outer_proph)?;
            Ok((Mode::Spec, p))
        }
        ExprX::Loc(e) => {
            return check_expr_handle_mut_arg(
                ctxt,
                record,
                typing,
                outer_mode,
                expect,
                e,
                outer_proph,
            );
        }
        ExprX::Binary(op, e1, e2) => {
            let op_mode = match op {
                BinaryOp::Eq(mode) => *mode,
                BinaryOp::HeightCompare { .. } => Mode::Spec,
                BinaryOp::Implies => Mode::Spec,
                _ => Mode::Exec,
            };
            let outer_mode = match op {
                // because Implies isn't compiled, make it spec-only
                BinaryOp::Implies => Mode::Spec,
                BinaryOp::HeightCompare { .. } => Mode::Spec,
                _ => outer_mode,
            };
            let (mode1, proph1) =
                check_expr(ctxt, record, typing, outer_mode, Expect(op_mode), e1, outer_proph)?;
            let outer_proph2 = if op.short_circuits() {
                outer_proph.clone().join(proph1.clone())
            } else {
                outer_proph.clone()
            };
            let (mode2, proph2) =
                check_expr(ctxt, record, typing, outer_mode, Expect(op_mode), e2, &outer_proph2)?;
            Ok((mode_join(op_mode, mode_join(mode1, mode2)), proph1.join(proph2)))
        }
        ExprX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), e1, e2) => {
            let proph1 =
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, e1, Mode::Spec, outer_proph)?;
            let proph2 =
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, e2, Mode::Spec, outer_proph)?;
            Ok((Mode::Spec, proph1.join(proph2)))
        }
        ExprX::Multi(MultiOp::Chained(_), es) => {
            let mut proph = Proph::No;
            for e in es.iter() {
                let p = check_expr_has_mode(
                    ctxt,
                    record,
                    typing,
                    Mode::Spec,
                    e,
                    Mode::Spec,
                    outer_proph,
                )?;
                proph = proph.join(p);
            }
            Ok((Mode::Spec, proph))
        }
        ExprX::Quant(_, binders, e1) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use forall/exists in exec mode"));
            }
            let mut typing = typing.push_var_scope();
            for binder in binders.iter() {
                typing.insert(&binder.name, Mode::Spec, Some(ProphVar::No));
            }
            let proph = check_expr_has_mode(
                ctxt,
                record,
                &mut typing,
                Mode::Spec,
                e1,
                Mode::Spec,
                outer_proph,
            )?;
            Ok((Mode::Spec, proph))
        }
        ExprX::Closure(params, body) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use spec_fn closure in 'exec' mode"));
            }
            let mut typing = typing.push_var_scope();
            for binder in params.iter() {
                typing.insert(&binder.name, Mode::Spec, Some(ProphVar::No));
            }
            let mut typing = typing.push_atomic_insts(None);
            let p = check_expr_has_mode(
                ctxt,
                record,
                &mut typing,
                Mode::Spec,
                body,
                Mode::Spec,
                outer_proph,
            )?;
            Ok((Mode::Spec, p))
        }
        ExprX::NonSpecClosure {
            params,
            proof_fn_modes,
            ret,
            requires,
            ensures,
            body,
            external_spec,
        } => {
            // This should not be filled in yet
            assert!(external_spec.is_none());
            let (is_proof, param_modes, ret_mode, closure_mode) =
                if let Some((param_modes, ret_mode)) = proof_fn_modes {
                    (true, param_modes.clone(), *ret_mode, Mode::Proof)
                } else {
                    let param_modes = Arc::new(params.iter().map(|_| Mode::Exec).collect());
                    (false, param_modes, Mode::Exec, Mode::Exec)
                };

            if !is_proof && (typing.block_ghostness != Ghost::Exec || outer_mode != Mode::Exec) {
                return Err(error(
                    &expr.span,
                    "closure in ghost code must be marked as a spec_fn by wrapping it in `closure_to_fn_spec` (this should happen automatically in the Verus syntax macro)",
                ));
            }
            if is_proof && (typing.block_ghostness == Ghost::Exec || outer_mode != Mode::Proof) {
                return Err(error(&expr.span, "proof closure can only appear in proof mode"));
            }
            let mut typing = typing.push_var_scope();
            assert!(param_modes.len() == params.len());
            for (param_mode, binder) in param_modes.iter().zip(params.iter()) {
                typing.insert(&binder.name, *param_mode, Some(ProphVar::No));
            }
            let mut typing = typing.push_atomic_insts(None);
            let mut typing = typing.push_ret_mode(Some(ret_mode));

            {
                let mut ghost_typing = typing.push_block_ghostness(Ghost::Ghost);
                for req in requires.iter() {
                    check_expr_has_mode(
                        ctxt,
                        record,
                        &mut ghost_typing,
                        Mode::Spec,
                        req,
                        Mode::Spec,
                        &Proph::No,
                    )?;
                }

                let mut ens_typing = ghost_typing.push_var_scope();
                ens_typing.insert(&ret.name, ret_mode, Some(ProphVar::No));
                for ens in ensures.iter() {
                    check_expr_has_mode(
                        ctxt,
                        record,
                        &mut ens_typing,
                        Mode::Spec,
                        ens,
                        Mode::Spec,
                        &Proph::No,
                    )?;
                }
            }

            let p = check_expr_has_mode(
                ctxt,
                record,
                &mut typing,
                outer_mode,
                body,
                ret_mode,
                &Proph::No,
            )?;
            p.check(&expr.span, NoProphReason::Return)?;

            Ok((closure_mode, Proph::No))
        }
        ExprX::ExecFnByName(fun) => {
            let function = ctxt.funs.get(fun).unwrap();
            if function.x.mode != Mode::Exec {
                // Could probably support 'proof' functions (in ghost code) as well
                return Err(error(
                    &expr.span,
                    "cannot use a function as a value unless it as mode 'exec'",
                ));
            }

            record.erasure_modes.var_modes.push((expr.span.clone(), Mode::Exec));

            Ok((outer_mode, Proph::No))
        }
        ExprX::Choose { params, cond, body } => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use choose in exec mode"));
            }
            let mut typing = typing.push_var_scope();
            for binder in params.iter() {
                typing.insert(&binder.name, Mode::Spec, Some(ProphVar::No));
            }
            let proph1 = check_expr_has_mode(
                ctxt,
                record,
                &mut typing,
                Mode::Spec,
                cond,
                Mode::Spec,
                &outer_proph,
            )?;
            let proph2 = check_expr_has_mode(
                ctxt,
                record,
                &mut typing,
                Mode::Spec,
                body,
                Mode::Spec,
                &outer_proph,
            )?;
            let proph = proph1.join(proph2);
            Ok((Mode::Spec, proph))
        }
        ExprX::WithTriggers { triggers, body } => {
            for trigger in triggers.iter() {
                for term in trigger.iter() {
                    check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        Mode::Spec,
                        term,
                        Mode::Spec,
                        outer_proph,
                    )?;
                }
            }
            let proph = check_expr_has_mode(
                ctxt,
                record,
                typing,
                Mode::Spec,
                body,
                Mode::Spec,
                outer_proph,
            )?;
            Ok((Mode::Spec, proph))
        }
        ExprX::AssignToPlace { place, rhs, op: _, resolve: _ } => {
            if typing.in_forall_stmt {
                return Err(error(
                    &expr.span,
                    "assignment is not allowed in 'assert ... by' statement",
                ));
            }
            if typing.in_proof_in_spec {
                return Err(error(&expr.span, "assignment is not allowed inside spec"));
            }
            if let (PlaceX::Local(xl), ExprX::ReadPlace(pr, _)) = (&place.x, &rhs.x) {
                if let PlaceX::Local(xr) = &pr.x {
                    // Special case mode inference just for our encoding of "let tracked pat = ..."
                    // in Rust as "let xl; ... { let pat ... xl = xr; }".
                    if let Some(span) = typing.to_be_inferred(xl) {
                        let (mode, pv) = typing.get(xr, &rhs.span)?;
                        typing.infer_as(xl, mode, pv.clone());
                        record.var_modes.insert(xl.clone(), mode);
                        record.erasure_modes.var_modes.push((span, mode));
                    }
                }
            }

            let (lhs_mode, lhs_proph, rhs_proph) = match &place.x {
                PlaceX::Local(xl) if typing.proph_to_be_inferred(xl) => {
                    // Special case the delayed inference of a variable's propheticness
                    let rhs_proph = check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        rhs,
                        Mode::Spec,
                        outer_proph,
                    )?;
                    let pv = rhs_proph.to_inferred_proph_var();
                    typing.infer_proph_as(xl, pv);
                    let (lhs_mode, lhs_proph) = check_place(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        place,
                        PlaceAccess::MutAssign,
                        Expect::none(),
                        outer_proph,
                    )?;
                    (lhs_mode, lhs_proph, rhs_proph)
                }
                _ => {
                    let (lhs_mode, lhs_proph) = check_place(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        place,
                        PlaceAccess::MutAssign,
                        Expect::none(),
                        outer_proph,
                    )?;
                    let rhs_proph = check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        rhs,
                        lhs_mode,
                        outer_proph,
                    )?;
                    (lhs_mode, lhs_proph, rhs_proph)
                }
            };

            if matches!(lhs_proph, Proph::No) {
                outer_proph.outer_check(&expr.span, OuterProphReason::AssignToNonProphPlace)?;
                rhs_proph.check(&expr.span, NoProphReason::AssignToNonProphPlace)?;
            }

            Ok((lhs_mode, Proph::No))
        }
        ExprX::Assign { lhs, rhs, op: _ } => {
            if typing.in_forall_stmt {
                return Err(error(
                    &expr.span,
                    "assignment is not allowed in 'assert ... by' statement",
                ));
            }
            if typing.in_proof_in_spec {
                return Err(error(&expr.span, "assignment is not allowed inside spec"));
            }
            if let (ExprX::VarLoc(xl), ExprX::ReadPlace(pr, _)) = (&lhs.x, &rhs.x) {
                if let PlaceX::Local(xr) = &pr.x {
                    // Special case mode inference just for our encoding of "let tracked pat = ..."
                    // in Rust as "let xl; ... { let pat ... xl = xr; }".
                    if let Some(span) = typing.to_be_inferred(xl) {
                        let (mode, pv) = typing.get(xr, &rhs.span)?;
                        typing.infer_as(xl, mode, pv.clone());
                        record.var_modes.insert(xl.clone(), mode);
                        record.erasure_modes.var_modes.push((span, mode));
                    }
                }
            }

            let (x_mode, lhs_proph, rhs_proph) = match &lhs.x {
                ExprX::VarLoc(xl) if typing.proph_to_be_inferred(xl) => {
                    // Special case the delayed inference of a variable's propheticness
                    let rhs_proph = check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        rhs,
                        Mode::Spec,
                        outer_proph,
                    )?;
                    let pv = rhs_proph.to_inferred_proph_var();
                    typing.infer_proph_as(xl, pv);
                    let (x_mode, lhs_proph) =
                        get_var_loc_mode(ctxt, record, typing, outer_mode, None, lhs)?;
                    if !mode_le(outer_mode, x_mode) {
                        return Err(error(
                            &expr.span,
                            format!("cannot assign to {x_mode} variable from {outer_mode} mode"),
                        ));
                    }
                    (x_mode, lhs_proph, rhs_proph)
                }
                _ => {
                    let (x_mode, lhs_proph) =
                        get_var_loc_mode(ctxt, record, typing, outer_mode, None, lhs)?;
                    if !mode_le(outer_mode, x_mode) {
                        return Err(error(
                            &expr.span,
                            format!("cannot assign to {x_mode} variable from {outer_mode} mode"),
                        ));
                    }
                    let rhs_proph = check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        rhs,
                        x_mode,
                        outer_proph,
                    )?;
                    (x_mode, lhs_proph, rhs_proph)
                }
            };

            if matches!(lhs_proph, Proph::No) {
                outer_proph.outer_check(&expr.span, OuterProphReason::AssignToNonProphPlace)?;
                rhs_proph.check(&expr.span, NoProphReason::AssignToNonProphPlace)?;
            }

            Ok((x_mode, Proph::No))
        }
        ExprX::Fuel(_, _, _) => {
            if typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use reveal/hide in exec mode")
                    .help("wrap the reveal call in a `proof` block"));
            }
            Ok((outer_mode, Proph::No))
        }
        ExprX::RevealString(_) => {
            if typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use reveal_strlit in exec mode")
                    .help("wrap the reveal_strlit call in a `proof` block"));
            }
            Ok((outer_mode, Proph::No))
        }
        ExprX::Header(_) => panic!("internal error: Header shouldn't exist here"),
        ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: true, expr, fun: _ } => {
            check_expr_has_mode(ctxt, record, typing, outer_mode, expr, Mode::Proof, outer_proph)?;
            Ok((outer_mode, Proph::No))
        }
        ExprX::AssertAssumeUserDefinedTypeInvariant { .. } => {
            panic!("internal error: AssertAssumeUserDefinedTypeInvariant shouldn't exist here")
        }
        ExprX::AssertAssume { is_assume: _, expr: e, msg: _ } => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use assert or assume in exec mode"));
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e, Mode::Spec, outer_proph)?;
            Ok((outer_mode, Proph::No))
        }
        ExprX::AssertBy { vars, require, ensure, proof } => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use 'assert ... by' in exec mode")
                    .help("use a `proof` block"));
            }
            // REVIEW: we could allow proof vars when vars.len() == 0,
            // but we'd have to implement the proper lifetime checking in erase.rs
            let mut typing = typing.push_in_forall_stmt(true);
            let mut typing = typing.push_var_scope();
            for var in vars.iter() {
                typing.insert(&var.name, Mode::Spec, Some(ProphVar::No));
            }
            {
                check_expr_has_mode(
                    ctxt,
                    record,
                    &mut typing,
                    Mode::Spec,
                    require,
                    Mode::Spec,
                    outer_proph,
                )?;
                check_expr_has_mode(
                    ctxt,
                    record,
                    &mut typing,
                    Mode::Spec,
                    ensure,
                    Mode::Spec,
                    outer_proph,
                )?;
            }
            check_expr_has_mode(
                ctxt,
                record,
                &mut typing,
                Mode::Proof,
                proof,
                Mode::Proof,
                outer_proph,
            )?;
            Ok((Mode::Proof, Proph::No))
        }
        ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use assert in exec mode"));
            }
            for req in requires.iter() {
                check_expr_has_mode(
                    ctxt,
                    record,
                    typing,
                    Mode::Spec,
                    req,
                    Mode::Spec,
                    outer_proph,
                )?;
            }
            for ens in ensures.iter() {
                check_expr_has_mode(
                    ctxt,
                    record,
                    typing,
                    Mode::Spec,
                    ens,
                    Mode::Spec,
                    outer_proph,
                )?;
            }
            check_expr_has_mode(
                ctxt,
                record,
                typing,
                Mode::Proof,
                proof,
                Mode::Proof,
                outer_proph,
            )?;
            Ok((Mode::Proof, Proph::No))
        }
        ExprX::AssertCompute(e, _) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use assert in exec mode"));
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e, Mode::Spec, outer_proph)?;
            Ok((Mode::Proof, Proph::No))
        }
        ExprX::If(e1, e2, e3) => {
            let condition_expect = match typing.block_ghostness {
                Ghost::Exec => Expect(Mode::Exec),
                Ghost::Ghost => Expect(Mode::Spec),
            };
            let (mode1, cond_proph) =
                check_expr(ctxt, record, typing, outer_mode, condition_expect, e1, outer_proph)?;
            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode1 != Mode::Exec
            {
                return Err(error(&expr.span, "condition must have mode exec"));
            }

            let mode_branch = match (outer_mode, mode1) {
                (Mode::Exec, Mode::Spec) => Mode::Proof,
                _ => outer_mode,
            };
            let outer_proph_branch = outer_proph.clone().join(cond_proph.clone());
            let (mode2, proph2) =
                check_expr(ctxt, record, typing, mode_branch, expect, e2, &outer_proph_branch)?;
            match e3 {
                None => Ok((mode2, cond_proph.join(proph2))),
                Some(e3) => {
                    let (mode3, proph3) = check_expr(
                        ctxt,
                        record,
                        typing,
                        mode_branch,
                        expect,
                        e3,
                        &outer_proph_branch,
                    )?;
                    Ok((mode_join(mode2, mode3), cond_proph.join(proph2).join(proph3)))
                }
            }
        }
        ExprX::Match(e1, arms) => {
            let scrutinee_expect = Expect::none();
            let guard_condition_expect = match typing.block_ghostness {
                Ghost::Exec => Expect(Mode::Exec),
                Ghost::Ghost => Expect(Mode::Spec),
            };

            let (mode1, proph1) = check_place(
                ctxt,
                record,
                typing,
                outer_mode,
                e1,
                PlaceAccess::Read,
                scrutinee_expect,
                outer_proph,
            )?;
            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode1 != Mode::Exec
            {
                return Err(error(&expr.span, "exec code cannot match on non-exec value"));
            }

            match (mode1, arms.len()) {
                (Mode::Spec, 0) => {
                    // We treat spec types as inhabited,
                    // so empty matches on spec values would be unsound.
                    return Err(error(&expr.span, "match must have at least one arm"));
                }
                _ => {}
            }
            let mut final_mode = outer_mode;
            let mut final_proph = proph1.clone();
            let mut arm_outer_proph = outer_proph.clone().join(proph1);
            let proph_for_binders = match &arm_outer_proph {
                Proph::No => ProphVar::No,
                Proph::Yes(reason) => {
                    ProphVar::Yes(ProphVarReason::Inferred(Rc::new(reason.clone())))
                }
            };
            for arm in arms.iter() {
                let mut typing = typing.push_var_scope();
                add_pattern(
                    ctxt,
                    record,
                    &mut typing,
                    mode1,
                    Some(proph_for_binders.clone()),
                    &arm.x.pattern,
                )?;
                let arm_outer_mode = match (outer_mode, mode1) {
                    (Mode::Exec, Mode::Spec | Mode::Proof) => Mode::Proof,
                    (m, _) => m,
                };
                let (guard_mode, guard_proph) = check_expr(
                    ctxt,
                    record,
                    &mut typing,
                    arm_outer_mode,
                    guard_condition_expect,
                    &arm.x.guard,
                    &arm_outer_proph,
                )?;
                arm_outer_proph = arm_outer_proph.join(guard_proph.clone());
                // REVIEW: does this need to accumulate modes from previous guards?
                // By the formalism, yes, but right now it seems to be redundant with
                // the ghost-blocks check.
                let arm_outer_mode = match (arm_outer_mode, guard_mode) {
                    (Mode::Exec, Mode::Spec | Mode::Proof) => Mode::Proof,
                    (m, _) => m,
                };
                let (arm_mode, arm_proph) = check_expr(
                    ctxt,
                    record,
                    &mut typing,
                    arm_outer_mode,
                    expect,
                    &arm.x.body,
                    &arm_outer_proph,
                )?;
                final_mode = mode_join(final_mode, arm_mode);
                final_proph = final_proph.join(guard_proph).join(arm_proph);
            }
            Ok((final_mode, final_proph))
        }
        ExprX::Loop {
            cond,
            body,
            invs,
            decrease,
            loop_isolation: _,
            allow_complex_invariants: _,
            is_for_loop: _,
            label: _,
        } => {
            // We could also allow this for proof, if we check it for termination
            if ctxt.check_ghost_blocks && typing.block_ghostness != Ghost::Exec {
                return Err(error(&expr.span, "cannot use while in proof or spec mode"));
            }
            match typing.update_atomic_insts() {
                None => {}
                Some(ai) => ai.add_loop(&expr.span),
            }
            if let Some(cond) = cond {
                let cond_proph = check_expr_has_mode(
                    ctxt,
                    record,
                    typing,
                    outer_mode,
                    cond,
                    Mode::Exec,
                    &Proph::No,
                )?;
                cond_proph.check(&cond.span, NoProphReason::LoopCondition)?;
            }
            check_expr_has_mode(ctxt, record, typing, outer_mode, body, Mode::Exec, &Proph::No)?;
            for inv in invs.iter() {
                let mut typing = typing.push_block_ghostness(Ghost::Ghost);
                check_expr_has_mode(
                    ctxt,
                    record,
                    &mut typing,
                    Mode::Spec,
                    &inv.inv,
                    Mode::Spec,
                    outer_proph,
                )?;
            }
            for dec in decrease.iter() {
                let mut typing = typing.push_block_ghostness(Ghost::Ghost);
                let dec_proph = check_expr_has_mode(
                    ctxt,
                    record,
                    &mut typing,
                    Mode::Spec,
                    dec,
                    Mode::Spec,
                    outer_proph,
                )?;
                dec_proph.check(&dec.span, NoProphReason::DecreasesClause)?;
            }
            Ok((Mode::Exec, Proph::No))
        }
        ExprX::Return(e1) => {
            if ctxt.check_ghost_blocks {
                match (ctxt.fun_mode, typing.block_ghostness) {
                    (Mode::Exec, Ghost::Exec) => {}
                    (Mode::Proof, _) => {}
                    (Mode::Spec, _) => {}
                    (Mode::Exec, _) => {
                        return Err(error(
                            &expr.span,
                            "cannot return from non-exec code in exec function",
                        ));
                    }
                }
            } else {
                match (ctxt.fun_mode, outer_mode) {
                    (Mode::Exec, Mode::Exec) => {}
                    (Mode::Proof, _) => {}
                    (Mode::Spec, _) => {}
                    (Mode::Exec, _) => {
                        return Err(error(
                            &expr.span,
                            "cannot return from non-exec code in exec function",
                        ));
                    }
                }
            }
            if typing.in_forall_stmt {
                return Err(error(
                    &expr.span,
                    "return is not allowed in 'assert ... by' statements",
                ));
            }
            if typing.in_proof_in_spec {
                return Err(error(&expr.span, "return is not allowed inside spec"));
            }
            match (e1, typing.ret_mode) {
                (None, _) => {}
                (Some(v), None) if is_unit(&v.typ) => {}
                (_, None) => panic!("internal error: missing return type"),
                (Some(e1), Some(ret_mode)) => {
                    let proph = check_expr_has_mode(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        e1,
                        ret_mode,
                        outer_proph,
                    )?;
                    proph.check(&expr.span, NoProphReason::Return)?;
                }
            }
            Ok((Mode::Exec, Proph::No))
        }
        ExprX::BreakOrContinue { label: _, is_break: _ } => Ok((Mode::Exec, Proph::No)),
        ExprX::Ghost { alloc_wrapper, tracked, expr: e1 } => {
            let block_ghostness = match (typing.block_ghostness, alloc_wrapper, tracked) {
                (Ghost::Exec, false, false) => {
                    if !is_unit(&e1.typ) {
                        return Err(error(&expr.span, "proof block must have type ()"));
                    }
                    Ghost::Ghost
                }
                (_, false, false) => {
                    return Err(error(&expr.span, "already in proof mode"));
                }
                (Ghost::Exec, false, true) => {
                    return Err(error(
                        &expr.span,
                        "cannot mark expression as tracked in exec mode",
                    ));
                }
                (Ghost::Ghost, false, true) => Ghost::Ghost,
                (Ghost::Exec, true, _) => Ghost::Ghost,
                (Ghost::Ghost, true, _) => {
                    return Err(error(
                        &expr.span,
                        "Ghost(...) or Tracked(...) can only be used in exec mode",
                    ));
                }
            };
            let mut typing = typing.push_block_ghostness(block_ghostness);
            let outer_mode = match (outer_mode, block_ghostness) {
                (Mode::Exec, Ghost::Ghost) => Mode::Proof,
                _ => outer_mode,
            };
            let m = if *tracked { Mode::Proof } else { Mode::Spec };
            let inner_mode = check_expr_handle_mut_arg(
                ctxt,
                record,
                &mut typing,
                outer_mode,
                Expect(expect.join(m)),
                e1,
                outer_proph,
            )?;
            let mode = if *alloc_wrapper {
                let (inner_read, inner_write, inner_proph) = inner_mode;
                let target_mode = if *tracked { Mode::Proof } else { Mode::Spec };
                if !mode_le(inner_read, target_mode) {
                    return Err(error(
                        &expr.span,
                        format!(
                            "expression has mode {}, expected mode {}",
                            inner_read, target_mode
                        ),
                    ));
                }
                let outer_write = if inner_write == Some(inner_read) && inner_read == target_mode {
                    Some(Mode::Exec)
                } else {
                    None
                };
                (Mode::Exec, outer_write, inner_proph)
            } else {
                inner_mode
            };
            if mode.0 != Mode::Spec {
                mode.2.check(
                    &expr.span,
                    if *tracked { NoProphReason::TrackedWrap } else { NoProphReason::GhostWrap },
                )?;
            }
            return Ok(mode);
        }
        ExprX::ProofInSpec(e1) => {
            match (typing.block_ghostness, outer_mode) {
                (Ghost::Ghost, Mode::Spec) => {}
                (Ghost::Ghost, Mode::Proof) => {
                    return Err(error(&expr.span, "already in proof mode"));
                }
                _ => {
                    // The syntax macro should never lead us to this case
                    return Err(error(&expr.span, "unexpected proof block"));
                }
            }
            if !is_unit(&e1.typ) {
                return Err(error(&expr.span, "proof block must have type ()"));
            }
            let mut typing = typing.push_in_proof_in_spec(true);
            check_expr(ctxt, record, &mut typing, Mode::Proof, Expect(Mode::Spec), e1, outer_proph)
        }
        ExprX::Block(ss, Some(e1)) if ss.len() == 0 => {
            return check_expr_handle_mut_arg(
                ctxt,
                record,
                typing,
                outer_mode,
                expect,
                e1,
                outer_proph,
            );
        }
        ExprX::Block(ss, e1) => {
            let mut typing = typing.push_var_multi_scope();
            for stmt in ss.iter() {
                typing.add_var_multi_scope();
                check_stmt(ctxt, record, &mut typing, outer_mode, stmt, outer_proph)?;
            }
            let mode = match e1 {
                None => (outer_mode, Proph::No),
                Some(expr) => {
                    check_expr(ctxt, record, &mut typing, outer_mode, expect, expr, outer_proph)?
                }
            };
            Ok(mode)
        }
        ExprX::OpenInvariant(inv, binder, body, atomicity) => {
            if outer_mode == Mode::Spec {
                return Err(error(&expr.span, "Cannot open invariant in Spec mode."));
            }

            record.var_modes.insert(binder.name.clone(), Mode::Proof);

            let mut ghost_typing = typing.push_block_ghostness(Ghost::Ghost);
            let (mode1, proph1) = check_expr(
                ctxt,
                record,
                &mut ghost_typing,
                outer_mode,
                Expect(Mode::Proof),
                inv,
                outer_proph,
            )?;
            proph1.check(&expr.span, NoProphReason::OpenInvariantArg)?;
            drop(ghost_typing);

            if mode1 != Mode::Proof {
                return Err(error(&inv.span, "Invariant must be Proof mode."));
            }
            let mut typing = typing.push_var_scope();

            typing.insert(&binder.name, Mode::Proof, Some(ProphVar::No));

            if *atomicity == InvAtomicity::NonAtomic
                || typing.atomic_insts.is_some()
                || outer_mode != Mode::Exec
            {
                // If we're a nested atomic block, we don't need to create a new
                // AtomicInstCollector. We just rely on the outer one.
                // Also, if we're already in Proof mode, then we just recurse in Proof
                // mode, and we don't need to do the atomicity check at all.
                // And of course, we don't do atomicity checks for the 'NonAtomic'
                // invariant type.
                let _ = check_expr(
                    ctxt,
                    record,
                    &mut typing,
                    outer_mode,
                    Expect::none(),
                    body,
                    outer_proph,
                )?;
            } else {
                let mut typing = typing.push_atomic_insts(Some(AtomicInstCollector::new()));
                let _ = check_expr(
                    ctxt,
                    record,
                    &mut typing,
                    outer_mode,
                    Expect::none(),
                    body,
                    outer_proph,
                )?;
                typing
                    .atomic_insts
                    .as_ref()
                    .expect("my_atomic_insts")
                    .validate(&body.span, false)?;
            }

            Ok((Mode::Exec, Proph::No))
        }
        ExprX::AirStmt(_) => Ok((Mode::Exec, Proph::No)),
        ExprX::NeverToAny(e) => {
            let expect = Expect(expect.meet(Mode::Proof));
            let (mode, _p) = check_expr(ctxt, record, typing, outer_mode, expect, e, outer_proph)?;
            if mode == Mode::Spec {
                return Err(error(&expr.span, "never-to-any coercion is not allowed in spec mode"));
            }
            Ok((mode, Proph::No))
        }
        ExprX::Nondeterministic => {
            panic!("Nondeterministic is not created by user code right now");
        }
        ExprX::ImplicitReborrowOrSpecRead(place, _, _)
            if expect.0 == Mode::Spec || outer_mode == Mode::Spec =>
        {
            if let Some(m) = &mut record.infer_spec_for_implicit_reborrows {
                let found = m.insert(expr.span.id, true);
                assert!(found.is_none());
            }

            let (_mode, proph) = check_place(
                ctxt,
                record,
                typing,
                outer_mode,
                place,
                PlaceAccess::Read,
                Expect(Mode::Spec),
                outer_proph,
            )?;
            Ok((Mode::Spec, proph))
        }
        ExprX::BorrowMut(place)
        | ExprX::TwoPhaseBorrowMut(place)
        | ExprX::ImplicitReborrowOrSpecRead(place, _, _) => {
            if matches!(&expr.x, ExprX::ImplicitReborrowOrSpecRead(..)) {
                if let Some(m) = &mut record.infer_spec_for_implicit_reborrows {
                    let found = m.insert(expr.span.id, false);
                    assert!(found.is_none());
                } else {
                    panic!("non-spec code expected infer_spec_for_implicit_reborrows");
                }
            }

            if typing.in_forall_stmt {
                return Err(error(
                    &expr.span,
                    "mutable borrow is not allowed in 'assert ... by' statement",
                ));
            }
            if typing.in_proof_in_spec || outer_mode == Mode::Spec {
                return Err(error(&expr.span, "mutable borrow is not allowed in spec context"));
            }

            outer_proph.outer_check(&expr.span, OuterProphReason::MutBorrow)?;

            let (mode, proph) = check_place(
                ctxt,
                record,
                typing,
                outer_mode,
                place,
                PlaceAccess::MutBorrow,
                Expect::none(),
                outer_proph,
            )?;
            match mode {
                Mode::Exec => {}
                Mode::Proof => {}
                Mode::Spec => {
                    return Err(error(
                        &place.span,
                        "cannot take mutable borrow of ghost-mode place",
                    ));
                }
            }
            proph.check(&expr.span, NoProphReason::MutBorrow)?;
            Ok((mode_join(mode, typing.block_ghostness.join_mode(outer_mode)), Proph::No))
        }
        ExprX::UnaryOpr(UnaryOpr::HasResolved(_t), e) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use `has_resolved` in exec mode"));
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e, Mode::Spec, outer_proph)?;
            let proph = Proph::Yes(ProphReason {
                span: expr.span.clone(),
                kind: ProphReasonKind::HasResolved,
            });
            Ok((Mode::Spec, proph))
        }
        ExprX::ReadPlace(place, read_kind) => {
            let (mode, proph) = check_place(
                ctxt,
                record,
                typing,
                outer_mode,
                place,
                PlaceAccess::Read,
                expect,
                outer_proph,
            )?;

            let final_read_kind = match mode {
                Mode::Spec => ReadKind::Spec,
                _ => read_kind.preliminary_kind,
            };
            record.read_kind_finals.insert(read_kind.id, final_read_kind);

            // TODO(new_mut_ref) if the ReadKind is spec, we should check that it really is spec

            let p = if matches!(read_kind.preliminary_kind, ReadKind::SpecAfterBorrow) {
                Proph::Yes(ProphReason {
                    span: expr.span.clone(),
                    kind: ProphReasonKind::AfterBorrow,
                })
            } else {
                proph
            };

            Ok((mode, p))
        }
        ExprX::UseLeftWhereRightCanHaveNoAssignments(..) => {
            panic!("UseLeftWhereRightCanHaveNoAssignments shouldn't be created yet");
        }
    };
    let (mode, proph) = mode_proph?;
    Ok((mode, None, proph))
}

fn check_stmt(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    stmt: &Stmt,
    outer_proph: &Proph,
) -> Result<(), VirErr> {
    match &stmt.x {
        StmtX::Expr(e) => {
            let expect = match typing.block_ghostness {
                Ghost::Exec => Expect(Mode::Exec),
                Ghost::Ghost => Expect(Mode::Spec),
            };
            let _ = check_expr(ctxt, record, typing, outer_mode, expect, e, outer_proph)?;
            Ok(())
        }
        StmtX::Decl { pattern, mode: None, init, els: _ } => {
            // Special case mode inference just for our encoding of "let tracked pat = ..."
            // in Rust as "let xl; ... { let pat ... xl = xr; }".
            match (&pattern.x, init) {
                (
                    PatternX::Var(PatternBinding {
                        name: x,
                        user_mut: _,
                        by_ref: _,
                        typ: _,
                        copy: _,
                    }),
                    None,
                ) => {
                    typing.insert_var_mode(x, VarMode::Infer(pattern.span.clone()));
                }
                _ => panic!("internal error: unexpected mode = None"),
            }
            Ok(())
        }
        StmtX::Decl { pattern, mode: Some((mode, proph_marker)), init, els } => {
            match proph_marker {
                DeclProph::Default => {}
                DeclProph::Prophetic | DeclProph::DelayedInfer => {
                    if *mode != Mode::Spec {
                        return Err(error(&stmt.span, "only a ghost variable can be prophetic"));
                    }
                }
            };
            let mode = if typing.block_ghostness != Ghost::Exec && *mode == Mode::Exec {
                Mode::Spec
            } else {
                *mode
            };
            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode != Mode::Exec
                && init.is_some()
            {
                return Err(error(&stmt.span, "exec code cannot initialize non-exec variables"));
            }
            if !mode_le(outer_mode, mode) {
                return Err(error(&stmt.span, format!("pattern cannot have mode {}", mode)));
            }
            let proph = match init.as_ref() {
                None => Proph::No,
                Some(place) => check_place_has_mode(
                    ctxt,
                    record,
                    typing,
                    outer_mode,
                    place,
                    mode,
                    PlaceAccess::Read,
                    outer_proph,
                )?,
            };
            if mode != Mode::Spec {
                if let Some(init) = init {
                    // Probably unreachable because we already checked mode
                    proph.check(&init.span, NoProphReason::NonSpecDecl)?;
                }
            }
            let proph_var = match proph_marker {
                DeclProph::DelayedInfer if init.is_none() => None,
                DeclProph::Default | DeclProph::DelayedInfer => {
                    match proph.clone().join(outer_proph.clone()) {
                        Proph::Yes(reason) => {
                            Some(ProphVar::Yes(ProphVarReason::Inferred(Rc::new(reason))))
                        }
                        Proph::No => Some(ProphVar::No),
                    }
                }
                DeclProph::Prophetic => {
                    Some(ProphVar::Yes(ProphVarReason::Explicit(stmt.span.clone())))
                }
            };
            add_pattern(ctxt, record, typing, mode, proph_var, pattern)?;
            match els.as_ref() {
                None => {}
                Some(expr) => {
                    if mode != Mode::Exec {
                        return Err(error(&stmt.span, "let-else only work in exec mode"));
                    }
                    proph.check(&stmt.span, NoProphReason::LetElse)?;
                    outer_proph.outer_check(&stmt.span, OuterProphReason::LetElse)?;
                    check_expr_has_mode(ctxt, record, typing, outer_mode, expr, mode, outer_proph)?;
                }
            }
            Ok(())
        }
    }
}

fn check_function(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    function: &mut Function,
    new_mut_ref: bool,
) -> Result<(), VirErr> {
    // Reset this, we only need it per-function
    record.type_inv_info =
        TypeInvInfo { ctor_needs_check: HashMap::new(), field_loc_needs_check: HashMap::new() };
    record.var_modes = HashMap::new();
    record.temporary_modes = HashMap::new();

    let mut fun_typing = typing.push_var_scope();

    if function.x.attrs.prophecy_dependent {
        if function.x.mode != Mode::Spec {
            return Err(error(
                &function.span,
                "prophetic attribute can only be applied to 'spec' functions",
            ));
        }
    }

    if let FunctionKind::TraitMethodImpl { method, trait_path, .. } = &function.x.kind {
        let our_trait = ctxt.traits.contains(trait_path);
        let (expected_params, expected_ret_mode, expected_proph): (Vec<Mode>, Mode, bool) =
            if our_trait {
                let trait_method = &ctxt.funs[method];
                let expect_mode = trait_method.x.mode;
                let expect_proph = trait_method.x.attrs.prophecy_dependent;
                if function.x.mode != expect_mode {
                    return Err(error(
                        &function.span,
                        format!("function must have mode {}", expect_mode),
                    ));
                }
                (
                    trait_method.x.params.iter().map(|f| f.x.mode).collect(),
                    trait_method.x.ret.x.mode,
                    expect_proph,
                )
            } else {
                (function.x.params.iter().map(|_| Mode::Exec).collect(), Mode::Exec, false)
            };
        assert!(expected_params.len() == function.x.params.len());
        for (param, expect) in function.x.params.iter().zip(expected_params.iter()) {
            let expect_mode = *expect;
            if param.x.mode != expect_mode {
                return Err(error(
                    &param.span,
                    format!("parameter must have mode {}", expect_mode),
                ));
            }
        }
        if function.x.ret.x.mode != expected_ret_mode {
            return Err(error(
                &function.span,
                format!("function return value must have mode {}", expected_ret_mode),
            ));
        }
        if function.x.attrs.prophecy_dependent && !expected_proph {
            return Err(error(
                &function.span,
                format!(
                    "implementation of trait function cannot be marked prophetic if the trait function is not"
                ),
            ));
        }
    }

    for param in function.x.params.iter() {
        if !mode_le(function.x.mode, param.x.mode) {
            return Err(error(
                &function.span,
                format!("parameter {} cannot have mode {}", param.x.name, param.x.mode),
            ));
        }
        let inner_param_mode =
            if let Some((mode, _)) = param.x.unwrapped_info { mode } else { param.x.mode };
        fun_typing.insert(&param.x.name, inner_param_mode, Some(ProphVar::No));
    }

    for expr in function.x.require.iter() {
        let mut req_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
        check_expr_has_mode(
            ctxt,
            record,
            &mut req_typing,
            Mode::Spec,
            expr,
            Mode::Spec,
            &Proph::No,
        )?;
    }

    let mut ens_typing = fun_typing.push_var_scope();
    if function.x.ens_has_return {
        ens_typing.insert(&function.x.ret.x.name, function.x.ret.x.mode, Some(ProphVar::No));
    }
    for expr in function.x.ensure.0.iter().chain(function.x.ensure.1.iter()) {
        let mut ens_typing = ens_typing.push_block_ghostness(Ghost::Ghost);
        check_expr_has_mode(
            ctxt,
            record,
            &mut ens_typing,
            Mode::Spec,
            expr,
            Mode::Spec,
            &Proph::No,
        )?;
    }
    drop(ens_typing);

    if let Some(expr) = &function.x.returns {
        let mut ret_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
        check_expr_has_mode(
            ctxt,
            record,
            &mut ret_typing,
            Mode::Spec,
            expr,
            Mode::Spec,
            &Proph::No,
        )?;
    }

    for expr in function.x.decrease.iter() {
        let mut dec_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
        let proph = check_expr_has_mode(
            ctxt,
            record,
            &mut dec_typing,
            Mode::Spec,
            expr,
            Mode::Spec,
            &Proph::No,
        )?;
        proph.check(&expr.span, NoProphReason::DecreasesClause)?;
    }
    if let Some(mask_spec) = &function.x.mask_spec {
        for expr in mask_spec.exprs().iter() {
            let mut dec_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
            check_expr_has_mode(
                ctxt,
                record,
                &mut dec_typing,
                Mode::Spec,
                expr,
                Mode::Spec,
                &Proph::No,
            )?;
        }
    }
    match &function.x.unwind_spec {
        None | Some(UnwindSpec::MayUnwind | UnwindSpec::NoUnwind) => {}
        Some(UnwindSpec::NoUnwindWhen(expr)) => {
            let mut dec_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
            check_expr_has_mode(
                ctxt,
                record,
                &mut dec_typing,
                Mode::Spec,
                expr,
                Mode::Spec,
                &Proph::No,
            )?;
        }
    }

    let ret_mode = if function.x.ens_has_return {
        let ret_mode = function.x.ret.x.mode;
        if !matches!(function.x.item_kind, ItemKind::Const) && !mode_le(function.x.mode, ret_mode) {
            return Err(error(
                &function.span,
                format!("return type cannot have mode {}", ret_mode),
            ));
        }
        if function.x.body.is_none()
            && !matches!(&function.x.kind, FunctionKind::TraitMethodDecl { .. })
        {
            // can't erase return values in external_body functions, so:
            // (note: proof functions that are external_body are usually implemented
            // as `unimplemented!()` and don't actually return anything, so it should
            // be fine.)
            if function.x.mode == Mode::Exec && function.x.mode != ret_mode {
                return Err(error(
                    &function.span,
                    format!(
                        "because function has no body, return type cannot have mode {}",
                        ret_mode
                    ),
                ));
            }
        }
        Some(ret_mode)
    } else {
        None
    };
    if let Some(body) = &function.x.body {
        let mut body_typing = fun_typing.push_ret_mode(ret_mode);
        let mut body_typing = body_typing.push_block_ghostness(Ghost::of_mode(function.x.mode));
        assert!(record.infer_spec_for_loop_iter_modes.is_none());
        record.infer_spec_for_loop_iter_modes = Some(Vec::new());
        record.infer_spec_for_implicit_reborrows = Some(HashMap::new());

        let proph = check_expr_has_mode(
            ctxt,
            record,
            &mut body_typing,
            function.x.mode,
            body,
            function.x.ret.x.mode,
            &Proph::No,
        )?;

        if !function.x.attrs.prophecy_dependent {
            proph.check(
                &body.span,
                if function.x.mode == Mode::Spec {
                    NoProphReason::NonPropheticSpecFnBody
                } else {
                    NoProphReason::Return
                },
            )?;
        }

        // Replace InferSpecForLoopIter None if it fails to have mode spec
        // (if it's mode spec, leave as is to be processed by sst_to_air and loop_inference)
        let loop_spec = record.infer_spec_for_loop_iter_modes.as_ref().expect("infer_spec");
        let borrow_spec = record.infer_spec_for_implicit_reborrows.as_ref().expect("borrow_spec");
        if loop_spec.len() > 0 || borrow_spec.len() > 0 {
            let mut functionx = function.x.clone();
            functionx.body = Some(crate::ast_visitor::map_expr_visitor(body, &|expr: &Expr| {
                match &expr.x {
                    ExprX::Unary(op @ UnaryOp::InferSpecForLoopIter { .. }, e) => {
                        let mode_opt = loop_spec.iter().find(|(span, _)| span.id == expr.span.id);
                        if let Some((_, Mode::Spec)) = mode_opt {
                            // InferSpecForLoopIter must be spec mode
                            // to be usable for invariant inference
                            Ok(expr.clone())
                        } else {
                            // Otherwise, abandon the expression and return NoInferSpecForLoopIter,
                            // which will be converted to None in sst_to_air
                            let no_infer = crate::ast::NullaryOpr::NoInferSpecForLoopIter;
                            let e = e.new_x(ExprX::NullaryOpr(no_infer));
                            Ok(expr.new_x(ExprX::Unary(*op, e)))
                        }
                    }
                    ExprX::ImplicitReborrowOrSpecRead(place, two_phase, inner_span) => {
                        let is_spec = *borrow_spec.get(&expr.span.id).unwrap();
                        if is_spec {
                            Ok(expr.new_x(ExprX::ReadPlace(
                                place.clone(),
                                UnfinalizedReadKind {
                                    preliminary_kind: ReadKind::Spec,
                                    id: u64::MAX,
                                },
                            )))
                        } else {
                            match &place.x {
                                PlaceX::Temporary(e) => {
                                    // &mut * Temporary(e) simplifies to e
                                    Ok(e.clone())
                                }
                                _ => {
                                    let dtyp = match &*place.typ {
                                        TypX::MutRef(t) => t,
                                        _ => panic!("expected MutRef type"),
                                    };
                                    let deref_e = SpannedTyped::new(
                                        &inner_span,
                                        dtyp,
                                        PlaceX::DerefMut(place.clone()),
                                    );
                                    let borrowx = if *two_phase {
                                        ExprX::TwoPhaseBorrowMut(deref_e)
                                    } else {
                                        ExprX::BorrowMut(deref_e)
                                    };
                                    Ok(expr.new_x(borrowx))
                                }
                            }
                        }
                    }
                    _ => Ok(expr.clone()),
                }
            })?);
            *function = function.new_x(functionx);
        }
        record.infer_spec_for_loop_iter_modes = None;
        record.infer_spec_for_implicit_reborrows = None;

        if function.x.mode != Mode::Spec || function.x.ret.x.mode != Mode::Spec {
            let functionx = &mut Arc::make_mut(&mut *function).x;
            crate::user_defined_type_invariants::annotate_user_defined_invariants(
                functionx,
                &record.type_inv_info,
                &ctxt.funs,
                &ctxt.datatypes,
                new_mut_ref,
            )?;
            if new_mut_ref {
                if let Some(body) = &mut functionx.body {
                    *body = crate::resolution_inference::infer_resolution(
                        &functionx.params,
                        &body,
                        &record.read_kind_finals,
                        &ctxt.datatypes,
                        &ctxt.funs,
                        &record.var_modes,
                        &record.temporary_modes,
                    );
                }
            }
        }
    }
    drop(fun_typing);
    typing.assert_zero_scopes();
    Ok(())
}

pub fn check_crate(
    krate: &Krate,
    new_mut_ref: bool,
) -> Result<(Krate, ErasureModes, ReadKindFinals), VirErr> {
    let mut funs: HashMap<Fun, Function> = HashMap::new();
    let mut datatypes: HashMap<Path, Datatype> = HashMap::new();
    for function in krate.functions.iter() {
        funs.insert(function.x.name.clone(), function.clone());
    }
    for datatype in krate.datatypes.iter() {
        match &datatype.x.name {
            Dt::Path(path) => {
                datatypes.insert(path.clone(), datatype.clone());
            }
            Dt::Tuple(_) => {
                panic!("Verus internal error: modes.rs does not expect Tuples in Krate");
            }
        }
    }
    let erasure_modes = ErasureModes { var_modes: vec![], ctor_modes: vec![] };
    let vstd_crate_name = Arc::new(crate::def::VERUSLIB.to_string());
    let special_paths = SpecialPaths::new(vstd_crate_name);
    let mut ctxt = Ctxt {
        funs,
        datatypes,
        traits: krate.traits.iter().map(|t| t.x.name.clone()).collect(),
        check_ghost_blocks: false,
        fun_mode: Mode::Exec,
        special_paths,
        new_mut_ref,
    };
    let type_inv_info =
        TypeInvInfo { ctor_needs_check: HashMap::new(), field_loc_needs_check: HashMap::new() };
    let mut record = Record {
        erasure_modes,
        infer_spec_for_loop_iter_modes: None,
        type_inv_info,
        read_kind_finals: HashMap::new(),
        var_modes: HashMap::new(),
        temporary_modes: HashMap::new(),
        infer_spec_for_implicit_reborrows: None,
    };
    let mut state = State {
        vars: ScopeMap::new(),
        in_forall_stmt: false,
        in_proof_in_spec: false,
        block_ghostness: Ghost::Exec,
        ret_mode: None,
        atomic_insts: None,
    };
    let mut typing = Typing::new(&mut state);
    let mut kratex = (**krate).clone();
    for function in kratex.functions.iter_mut() {
        ctxt.check_ghost_blocks = function.x.attrs.uses_ghost_blocks;
        ctxt.fun_mode = function.x.mode;
        if function.x.attrs.atomic {
            let mut typing = typing.push_atomic_insts(Some(AtomicInstCollector::new()));
            check_function(&ctxt, &mut record, &mut typing, function, new_mut_ref)?;
            typing.atomic_insts.as_ref().expect("atomic_insts").validate(&function.span, true)?;
        } else {
            check_function(&ctxt, &mut record, &mut typing, function, new_mut_ref)?;
        }
    }
    Ok((Arc::new(kratex), record.erasure_modes, record.read_kind_finals))
}
