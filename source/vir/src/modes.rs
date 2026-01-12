use crate::ast::{
    AutospecUsage, BinaryOp, ByRef, CallTarget, CallTargetKind, CtorUpdateTail, Datatype, Dt, Expr,
    ExprX, FieldOpr, Fun, Function, FunctionKind, InvAtomicity, ItemKind, Krate, Mode,
    ModeCoercion, MultiOp, OverflowBehavior, Path, Pattern, PatternBinding, PatternX, Place,
    PlaceX, ReadKind, Stmt, StmtX, UnaryOp, UnaryOpr, UnwindSpec, VarIdent, VirErr,
};
use crate::ast_util::{get_field, is_unit, path_as_vstd_name};
use crate::def::user_local_name;
use crate::messages::{Span, error};
use crate::messages::{error_bare, error_with_label};
use crate::util::vec_map_result;
use air::scope_map::ScopeMap;
use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::mem::swap;
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

/// Represents Rust ghost blocks
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Ghost {
    /// Not in a ghost block
    Exec,
    /// In a ghost block
    Ghost,
}

#[derive(Clone, Debug)]
pub struct ErasureModes {
    // Modes of conditions in If
    pub condition_modes: Vec<(Span, Mode)>,
    // Modes of variables in Var, Assign, Decl
    pub var_modes: Vec<(Span, Mode)>,
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
}

#[derive(Debug)]
enum VarMode {
    Infer(Span),
    Mode(Mode),
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
    pub(crate) allow_prophecy_dependence: bool,
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

        pub(super) fn push_allow_prophecy_dependence<'a>(
            &'a mut self,
            mut allow_prophecy_dependence: bool,
        ) -> Typing<'a> {
            swap(
                &mut allow_prophecy_dependence,
                &mut self.internal_state.allow_prophecy_dependence,
            );
            Typing {
                internal_state: self.internal_state,
                internal_undo: Some(Box::new(move |state| {
                    state.allow_prophecy_dependence = allow_prophecy_dependence;
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

        pub(super) fn insert_var_mode(&mut self, x: &VarIdent, mode: VarMode) {
            self.internal_state
                .vars
                .insert(x.clone(), mode)
                .expect("internal error: Typing insert");
        }

        pub(super) fn insert(&mut self, x: &VarIdent, mode: Mode) {
            self.insert_var_mode(x, VarMode::Mode(mode))
        }

        pub(super) fn infer_as(&mut self, x: &VarIdent, mode: Mode) {
            assert!(self.to_be_inferred(x).is_some());
            self.internal_state.vars.replace(x.clone(), VarMode::Mode(mode)).expect("infer_as");
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
    fn get(&self, x: &VarIdent, span: &Span) -> Result<Mode, VirErr> {
        if let VarMode::Mode(mode) = self.vars.get(x).expect("internal error: missing mode") {
            Ok(*mode)
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
    pattern: &Pattern,
) -> Result<(), VirErr> {
    let mut decls = vec![];
    add_pattern_rec(ctxt, record, typing, &mut decls, mode, pattern, false)?;
    for decl in decls {
        let PatternBoundDecl { span: _, name, mode } = decl;
        typing.insert(&name, mode);
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
        PatternX::Var(PatternBinding { name: x, mutable: _, by_ref, typ: _, copy: _ }) => {
            check_binding(&pattern.span, by_ref, mode)?;
            decls.push(PatternBoundDecl { span: pattern.span.clone(), name: x.clone(), mode });
            Ok(())
        }
        PatternX::Binding {
            binding: PatternBinding { name: x, mutable: _, by_ref, typ: _, copy: _ },
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
            check_expr_has_mode(ctxt, record, typing, mode, expr, mode)?;
            Ok(())
        }
        PatternX::Range(expr1, expr2) => {
            if let Some(expr1) = expr1 {
                check_expr_in_pattern(expr1)?;
                check_expr_has_mode(ctxt, record, typing, mode, expr1, mode)?;
            }
            if let Some((expr2, _ineq_op)) = expr2 {
                check_expr_in_pattern(expr2)?;
                check_expr_has_mode(ctxt, record, typing, mode, expr2, mode)?;
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
    init_not_mut: bool,
) -> Result<Mode, VirErr> {
    let x_mode = match &expr.x {
        ExprX::VarLoc(x) => {
            let x_mode = typing.get(x, &expr.span)?;

            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && x_mode != Mode::Exec
            {
                return Err(error(&expr.span, "exec code cannot mutate non-exec variable"));
            }

            x_mode
        }
        ExprX::Unary(
            UnaryOp::CoerceMode { op_mode, from_mode, to_mode, kind: ModeCoercion::BorrowMut },
            e1,
        ) => {
            assert!(!init_not_mut);
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
            let mode1 = get_var_loc_mode(
                ctxt,
                record,
                typing,
                outer_mode,
                Some(*to_mode),
                e1,
                init_not_mut,
            )?;
            if !mode_le(mode1, *from_mode) {
                return Err(error(
                    &expr.span,
                    format!("expected mode {}, found mode {}", *from_mode, mode1),
                ));
            }
            *to_mode
        }
        ExprX::UnaryOpr(
            UnaryOpr::Field(FieldOpr { datatype, variant: _, field, get_variant, check: _ }),
            rcvr,
        ) => {
            let rcvr_mode = get_var_loc_mode(
                ctxt,
                record,
                typing,
                outer_mode,
                expr_inner_mode,
                rcvr,
                init_not_mut,
            )?;
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
            mode_join(call_mode, field_mode)
        }
        ExprX::Block(stmts, Some(e1)) if stmts.len() == 0 => {
            // For now, only support the special case for Tracked::borrow_mut.
            get_var_loc_mode(ctxt, record, typing, outer_mode, None, e1, init_not_mut)?
        }
        ExprX::Ghost { alloc_wrapper: false, tracked: true, expr: e1 } => {
            // For now, only support the special case for Tracked::borrow_mut.
            let mut typing = typing.push_block_ghostness(Ghost::Ghost);
            let mode =
                get_var_loc_mode(ctxt, record, &mut typing, outer_mode, None, e1, init_not_mut)?;
            mode
        }
        _ => {
            panic!("unexpected loc {:?}", expr);
        }
    };
    if x_mode == Mode::Spec && init_not_mut {
        return Err(error(
            &expr.span,
            "delayed assignment to non-mut let not allowed for spec variables",
        ));
    }
    match &expr.x {
        ExprX::Ghost { .. } => {}
        _ => {
            let push_mode = expr_inner_mode.unwrap_or(x_mode);
            record.erasure_modes.var_modes.push((expr.span.clone(), push_mode));
        }
    }
    Ok(x_mode)
}

fn check_place_has_mode(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    place: &Place,
    expected: Mode,
    access: PlaceAccess,
) -> Result<(), VirErr> {
    let mode = check_place(ctxt, record, typing, outer_mode, place, access)?;
    if is_unit(&place.typ) {
        return Ok(());
    }
    if !mode_le(mode, expected) {
        Err(error(&place.span, format!("expression has mode {}, expected mode {}", mode, expected)))
    } else {
        Ok(())
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

fn check_place(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    place: &Place,
    access: PlaceAccess,
) -> Result<Mode, VirErr> {
    let place_mode = check_place_rec(ctxt, record, typing, outer_mode, place, access)?;

    let mut context_mode = typing.block_ghostness.join_mode(outer_mode);
    if typing.in_forall_stmt || typing.in_proof_in_spec {
        context_mode = Mode::Spec;
    }

    let final_mode = match access {
        PlaceAccess::Read => {
            // For non-mutating: coerce the mode to whatever is necessary for the context

            let coerced_mode = mode_join(place_mode, context_mode);
            coerced_mode
        }
        PlaceAccess::MutAssign => {
            // If mutating assignment: we can't coerce the mode;
            // thus, if a coercion is needed, then we produce an error.
            //
            // Note that we only need to do this coercion at the top-level Place node,
            // since for example, it's okay to do `x.foo = ...` if `x` is exec but foo is ghost.
            let coerced_mode = mode_join(place_mode, context_mode);

            if coerced_mode != place_mode {
                // TODO(new_mut_ref): we need a better diagnostic here to explain what's going on
                // when the user tries to modify a mut ref
                // (e.g., "note: x is a proof mode variable but points to an exec-mode place...")
                return Err(error(
                    &place.span,
                    &format!("cannot mutate {place_mode}-mode place in {context_mode}-code"),
                ));
            }

            place_mode
        }
        PlaceAccess::MutBorrow => {
            // Don't coerce because we want to be able to take
            // mut-borrows to exec places from proof code.
            // (This is safe because we still cannot modify the exec state through the reference)
            place_mode
        }
    };

    if let Some(var_place) = crate::ast_util::place_get_local(place) {
        record.erasure_modes.var_modes.push((var_place.span.clone(), final_mode));
    }

    Ok(final_mode)
}

fn check_place_rec(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    place: &Place,
    access: PlaceAccess,
) -> Result<Mode, VirErr> {
    let mode = check_place_rec_inner(ctxt, record, typing, outer_mode, place, access)?;
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
    Ok(mode)
}

fn check_place_rec_inner(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    place: &Place,
    access: PlaceAccess,
) -> Result<Mode, VirErr> {
    match &place.x {
        PlaceX::Field(FieldOpr { datatype, variant, field, get_variant: _, check: _ }, p) => {
            let mode = check_place_rec(ctxt, record, typing, outer_mode, p, access)?;

            let field_mode = match datatype {
                Dt::Path(path) => {
                    let datatype = &ctxt.datatypes[path];
                    let field = get_field(&datatype.x.get_variant(variant).fields, field);
                    field.a.1
                }
                Dt::Tuple(_) => Mode::Exec,
            };

            Ok(mode_join(mode, field_mode))
        }
        PlaceX::DerefMut(p) => {
            let mode = check_place_rec(ctxt, record, typing, outer_mode, p, access)?;
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
            Ok(Mode::Exec)
        }
        PlaceX::Local(var) => typing.get(var, &place.span),
        PlaceX::Temporary(e) => {
            let mode = check_expr(ctxt, record, typing, outer_mode, e)?;
            if ctxt.new_mut_ref {
                if record.temporary_modes.contains_key(&place.span.id) {
                    return Err(error(
                        &place.span,
                        &format!("Verus Internal Error: duplicate PlaceX::Temporary ID"),
                    ));
                }
                record.temporary_modes.insert(place.span.id, mode);
            }
            Ok(mode)
        }
        PlaceX::ModeUnwrap(p, wrapper_mode) => {
            let mode = check_place_rec(ctxt, record, typing, outer_mode, p, access)?;
            Ok(mode_join(mode, wrapper_mode.to_mode()))
        }
        PlaceX::WithExpr(..) => {
            return Err(error(
                &place.span,
                &format!("Verus Internal Error: WithExpr node shouldn't exist yet"),
            ));
        }
        PlaceX::Index(p, idx, _kind, _needs_bounds_check) => {
            let place_mode = check_place_rec(ctxt, record, typing, outer_mode, p, access)?;
            let idx_mode = check_expr(ctxt, record, typing, outer_mode, idx)?;

            if ctxt.check_ghost_blocks
                && matches!(typing.block_ghostness, Ghost::Exec)
                && idx_mode != Mode::Exec
            {
                return Err(error(
                    &place.span,
                    format!("cannot use {idx_mode}-mode expression in executable context"),
                ));
            }

            // Why not return mode_join(place_mode, idx_mode)?
            // This function returns the mode of the place itself, not the mode of the
            // expression, so the mode of the indexed place is the same as the mode
            // of the slice/array place.
            // e.g.,
            //   tracked[spec] -> tracked
            //   exec[spec] -> exec
            // If we try to do `exec[spec]` outside a ghost block, it will get caught by
            // the above check.
            Ok(place_mode)
        }
    }
}

fn check_expr_has_mode(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    expr: &Expr,
    expected: Mode,
) -> Result<(), VirErr> {
    let mode = check_expr(ctxt, record, typing, outer_mode, expr)?;
    if is_unit(&expr.typ) {
        return Ok(());
    }
    if !mode_le(mode, expected) {
        Err(error(&expr.span, format!("expression has mode {}, expected mode {}", mode, expected)))
    } else {
        Ok(())
    }
}

fn check_expr(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    expr: &Expr,
) -> Result<Mode, VirErr> {
    Ok(check_expr_handle_mut_arg(ctxt, record, typing, outer_mode, expr)?.0)
}

fn check_expr_handle_mut_arg(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    expr: &Expr,
) -> Result<(Mode, Option<Mode>), VirErr> {
    let mode = match &expr.x {
        ExprX::Const(_) => Ok(Mode::Exec),
        ExprX::Var(x) | ExprX::VarLoc(x) | ExprX::VarAt(x, _) => {
            if typing.in_forall_stmt || typing.in_proof_in_spec {
                // Proof variables may be used as spec, but not as proof inside forall statements.
                // This protects against effectively consuming a linear proof variable
                // multiple times for different instantiations of the forall variables.
                return Ok((Mode::Spec, None));
            }

            let x_mode = typing.get(x, &expr.span)?;

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
            return Ok((mode, Some(x_mode)));
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
            Ok(mode)
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
            check_expr_has_mode(ctxt, record, typing, Mode::Proof, &es[0], Mode::Proof)?;
            assert!(param_modes.len() == binders.len());
            for (param_mode, binder) in param_modes.iter().zip(binders.iter()) {
                let arg = &binder.a;
                check_expr_has_mode(ctxt, record, typing, Mode::Proof, arg, *param_mode)?;
            }
            Ok(*ret_mode)
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

            if !typing.allow_prophecy_dependence && function.x.attrs.prophecy_dependent {
                let resolved_fn_is_prophecy_dependent = match kind {
                    CallTargetKind::DynamicResolved { resolved, .. } => {
                        ctxt.funs.get(resolved).unwrap().x.attrs.prophecy_dependent
                    }
                    _ => true,
                };
                if resolved_fn_is_prophecy_dependent {
                    return Err(error(
                        &expr.span,
                        "cannot call prophecy-dependent function in prophecy-independent context",
                    ));
                }
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
                    let (arg_mode_read, arg_mode_write) =
                        check_expr_handle_mut_arg(ctxt, record, typing, outer_mode, arg)?;
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
                    check_expr_has_mode(ctxt, record, typing, param_mode, arg, param.x.mode)?;
                }
            }
            Ok(function.x.ret.x.mode)
        }
        ExprX::Call(CallTarget::FnSpec(e0), es, None) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot call spec function from exec mode"));
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e0, Mode::Spec)?;
            for arg in es.iter() {
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, arg, Mode::Spec)?;
            }
            Ok(Mode::Spec)
        }
        ExprX::Call(CallTarget::BuiltinSpecFun(_f, _typs, _impl_paths), es, None) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot call spec function from exec mode"));
            }
            for arg in es.iter() {
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, arg, Mode::Spec)?;
            }
            Ok(Mode::Spec)
        }
        ExprX::Call(_, _, Some(_)) => {
            return Err(error(&expr.span, "ExprX::Call should not have post_args at this point"));
        }
        ExprX::ArrayLiteral(es) => {
            let modes = vec_map_result(es, |e| check_expr(ctxt, record, typing, outer_mode, e))?;
            Ok(modes.into_iter().fold(Mode::Exec, mode_join))
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

            if let Some(CtorUpdateTail { place, taken_fields }) = update {
                let place_mode =
                    check_place(ctxt, record, typing, outer_mode, place, PlaceAccess::Read)?;

                for (taken_field, _) in taken_fields.iter() {
                    let field_mode = get_field_mode(taken_field);
                    let arg_mode = mode_join(place_mode, field_mode);
                    if !mode_le(arg_mode, field_mode) {
                        // allow this arg by weakening whole struct's mode
                        mode = mode_join(mode, arg_mode);
                    }
                }
            }
            for arg in binders.iter() {
                let field_mode = get_field_mode(&arg.name);
                let arg_mode =
                    check_expr(ctxt, record, typing, mode_join(outer_mode, field_mode), &arg.a)?;
                if !mode_le(arg_mode, field_mode) {
                    // allow this arg by weakening whole struct's mode
                    mode = mode_join(mode, arg_mode);
                }
            }

            record.type_inv_info.ctor_needs_check.insert(expr.span.id, mode != Mode::Spec);

            // Now that we've computed the final mode of this struct expr, go back through
            // all the 'take_fields' and see which ones require moves.
            // TODO(new_mut_ref) as in the ExprX::ReadPlace case, this is not as aggressive
            // about marking things spec as it should be.
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

            Ok(mode)
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(_)) => Ok(Mode::Exec),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TraitBound(..)) => Ok(Mode::Spec),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(..)) => Ok(Mode::Spec),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(..)) => Ok(Mode::Spec),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter) => Ok(Mode::Spec),
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
            check_expr_has_mode(ctxt, record, typing, param_mode, e1, *from_mode)?;
            if *kind == ModeCoercion::BorrowMut {
                return Ok((*to_mode, Some(*to_mode)));
            } else {
                Ok(*to_mode)
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
            let mode_opt = check_expr(ctxt, record, &mut typing, outer_mode, e1);
            let mode = mode_opt.unwrap_or(Mode::Exec);
            if let Some(infer_spec) = record.infer_spec_for_loop_iter_modes.as_mut() {
                infer_spec.push((expr.span.clone(), mode));
            } else {
                return Err(error(
                    &expr.span,
                    "infer_spec_for_loop_iter is only allowed in function body",
                ));
            }
            Ok(Mode::Spec)
        }
        ExprX::Unary(UnaryOp::MutRefFuture(source_name), e1) => {
            if !typing.allow_prophecy_dependence {
                return Err(error(
                    &expr.span,
                    format!(
                        "cannot use prophecy-dependent function `{:}` in prophecy-independent context",
                        source_name.as_str()
                    ),
                ));
            }
            check_expr(ctxt, record, typing, Mode::Spec, e1)?;
            Ok(Mode::Spec)
        }
        ExprX::Unary(UnaryOp::MutRefCurrent, e1) => {
            check_expr(ctxt, record, typing, Mode::Spec, e1)?;
            Ok(Mode::Spec)
        }
        ExprX::Unary(_, e1) => check_expr(ctxt, record, typing, outer_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::Box(_), _) => panic!("unexpected box"),
        ExprX::UnaryOpr(UnaryOpr::Unbox(_), _) => panic!("unexpected box"),
        ExprX::UnaryOpr(UnaryOpr::HasType(_), _) => panic!("internal error: HasType in modes.rs"),
        ExprX::UnaryOpr(UnaryOpr::IsVariant { .. }, e1) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot test variant in exec mode"));
            }
            check_expr(ctxt, record, typing, outer_mode, e1)
        }
        ExprX::UnaryOpr(
            UnaryOpr::Field(FieldOpr { datatype, variant, field, get_variant, check: _ }),
            e1,
        ) => {
            if *get_variant && ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot get variant in exec mode"));
            }
            let (e1_mode_read, e1_mode_write) =
                check_expr_handle_mut_arg(ctxt, record, typing, outer_mode, e1)?;

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
                return Ok((mode_read, Some(mode_join(e1_mode_write, field_mode))));
            } else {
                Ok(mode_read)
            }
        }
        ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(_kind, min_mode), e1) => {
            let joined_mode = mode_join(outer_mode, *min_mode);
            let mode = check_expr(ctxt, record, typing, joined_mode, e1)?;
            Ok(mode_join(*min_mode, mode))
        }
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), e1) => {
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e1, Mode::Spec)?;
            Ok(Mode::Spec)
        }
        ExprX::Loc(e) => {
            return check_expr_handle_mut_arg(ctxt, record, typing, outer_mode, e);
        }
        ExprX::Binary(op, e1, e2) => {
            let op_mode = match op {
                BinaryOp::Eq(mode) => *mode,
                BinaryOp::HeightCompare { .. } => Mode::Spec,
                _ => Mode::Exec,
            };
            let outer_mode = match op {
                // because Implies isn't compiled, make it spec-only
                BinaryOp::Implies => Mode::Spec,
                BinaryOp::HeightCompare { .. } => Mode::Spec,
                _ => outer_mode,
            };
            let mode1 = check_expr(ctxt, record, typing, outer_mode, e1)?;
            let mode2 = check_expr(ctxt, record, typing, outer_mode, e2)?;
            Ok(mode_join(op_mode, mode_join(mode1, mode2)))
        }
        ExprX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), e1, e2) => {
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e1, Mode::Spec)?;
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e2, Mode::Spec)?;
            Ok(Mode::Spec)
        }
        ExprX::Multi(MultiOp::Chained(_), es) => {
            for e in es.iter() {
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, e, Mode::Spec)?;
            }
            Ok(Mode::Spec)
        }
        ExprX::Quant(_, binders, e1) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use forall/exists in exec mode"));
            }
            let mut typing = typing.push_var_scope();
            for binder in binders.iter() {
                typing.insert(&binder.name, Mode::Spec);
            }
            check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, e1, Mode::Spec)?;
            Ok(Mode::Spec)
        }
        ExprX::Closure(params, body) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use spec_fn closure in 'exec' mode"));
            }
            let mut typing = typing.push_var_scope();
            for binder in params.iter() {
                typing.insert(&binder.name, Mode::Spec);
            }
            let mut typing = typing.push_atomic_insts(None);
            check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, body, Mode::Spec)?;
            Ok(Mode::Spec)
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
                typing.insert(&binder.name, *param_mode);
            }
            let mut typing = typing.push_atomic_insts(None);
            let mut typing = typing.push_ret_mode(Some(ret_mode));

            {
                let mut ghost_typing = typing.push_block_ghostness(Ghost::Ghost);
                let mut ghost_typing = ghost_typing.push_allow_prophecy_dependence(true);
                for req in requires.iter() {
                    check_expr_has_mode(
                        ctxt,
                        record,
                        &mut ghost_typing,
                        Mode::Spec,
                        req,
                        Mode::Spec,
                    )?;
                }

                let mut ens_typing = ghost_typing.push_var_scope();
                ens_typing.insert(&ret.name, ret_mode);
                for ens in ensures.iter() {
                    check_expr_has_mode(
                        ctxt,
                        record,
                        &mut ens_typing,
                        Mode::Spec,
                        ens,
                        Mode::Spec,
                    )?;
                }
            }

            check_expr_has_mode(ctxt, record, &mut typing, outer_mode, body, ret_mode)?;

            Ok(closure_mode)
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

            Ok(outer_mode)
        }
        ExprX::Choose { params, cond, body } => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use choose in exec mode"));
            }
            let mut typing = typing.push_var_scope();
            for binder in params.iter() {
                typing.insert(&binder.name, Mode::Spec);
            }
            check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, cond, Mode::Spec)?;
            check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, body, Mode::Spec)?;
            Ok(Mode::Spec)
        }
        ExprX::WithTriggers { triggers, body } => {
            for trigger in triggers.iter() {
                for term in trigger.iter() {
                    check_expr_has_mode(ctxt, record, typing, Mode::Spec, term, Mode::Spec)?;
                }
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, body, Mode::Spec)?;
            Ok(Mode::Spec)
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
                        let mode = typing.get(xr, &rhs.span)?;
                        typing.infer_as(xl, mode);
                        record.var_modes.insert(xl.clone(), mode);
                        record.erasure_modes.var_modes.push((span, mode));
                    }
                }
            }

            let lhs_mode =
                check_place(ctxt, record, typing, outer_mode, place, PlaceAccess::MutAssign)?;
            check_expr_has_mode(ctxt, record, typing, outer_mode, rhs, lhs_mode)?;
            Ok(lhs_mode)
        }
        ExprX::Assign { init_not_mut, lhs, rhs, op: _ } => {
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
                        let mode = typing.get(xr, &rhs.span)?;
                        typing.infer_as(xl, mode);
                        record.var_modes.insert(xl.clone(), mode);
                        record.erasure_modes.var_modes.push((span, mode));
                    }
                }
            }
            let x_mode =
                get_var_loc_mode(ctxt, record, typing, outer_mode, None, lhs, *init_not_mut)?;
            if !mode_le(outer_mode, x_mode) {
                return Err(error(
                    &expr.span,
                    format!("cannot assign to {x_mode} variable from {outer_mode} mode"),
                ));
            }
            check_expr_has_mode(ctxt, record, typing, outer_mode, rhs, x_mode)?;
            Ok(x_mode)
        }
        ExprX::Fuel(_, _, _) => {
            if typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use reveal/hide in exec mode")
                    .help("wrap the reveal call in a `proof` block"));
            }
            Ok(outer_mode)
        }
        ExprX::RevealString(_) => {
            if typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use reveal_strlit in exec mode")
                    .help("wrap the reveal_strlit call in a `proof` block"));
            }
            Ok(outer_mode)
        }
        ExprX::Header(_) => panic!("internal error: Header shouldn't exist here"),
        ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: true, expr, fun: _ } => {
            check_expr_has_mode(ctxt, record, typing, outer_mode, expr, Mode::Proof)?;
            Ok(outer_mode)
        }
        ExprX::AssertAssumeUserDefinedTypeInvariant { .. } => {
            panic!("internal error: AssertAssumeUserDefinedTypeInvariant shouldn't exist here")
        }
        ExprX::AssertAssume { is_assume: _, expr: e, msg: _ } => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use assert or assume in exec mode"));
            }
            let mut typing = typing.push_allow_prophecy_dependence(true);
            check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, e, Mode::Spec)?;
            Ok(outer_mode)
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
                typing.insert(&var.name, Mode::Spec);
            }
            {
                let mut typing = typing.push_allow_prophecy_dependence(true);
                check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, require, Mode::Spec)?;
                check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, ensure, Mode::Spec)?;
            }
            check_expr_has_mode(ctxt, record, &mut typing, Mode::Proof, proof, Mode::Proof)?;
            Ok(Mode::Proof)
        }
        ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use assert in exec mode"));
            }
            for req in requires.iter() {
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, req, Mode::Spec)?;
            }
            for ens in ensures.iter() {
                check_expr_has_mode(ctxt, record, typing, Mode::Spec, ens, Mode::Spec)?;
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Proof, proof, Mode::Proof)?;
            Ok(Mode::Proof)
        }
        ExprX::AssertCompute(e, _) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use assert in exec mode"));
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e, Mode::Spec)?;
            Ok(Mode::Proof)
        }
        ExprX::If(e1, e2, e3) => {
            let mode1 = check_expr(ctxt, record, typing, outer_mode, e1)?;
            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode1 != Mode::Exec
            {
                return Err(error(&expr.span, "condition must have mode exec"));
            }
            record.erasure_modes.condition_modes.push((expr.span.clone(), mode1));

            let mode_branch = match (outer_mode, mode1) {
                (Mode::Exec, Mode::Spec) => Mode::Proof,
                _ => outer_mode,
            };
            let mode2 = check_expr(ctxt, record, typing, mode_branch, e2)?;
            match e3 {
                None => Ok(mode2),
                Some(e3) => {
                    let mode3 = check_expr(ctxt, record, typing, mode_branch, e3)?;
                    Ok(mode_join(mode2, mode3))
                }
            }
        }
        ExprX::Match(e1, arms) => {
            let mode1 = check_place(ctxt, record, typing, outer_mode, e1, PlaceAccess::Read)?;
            if ctxt.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode1 != Mode::Exec
            {
                return Err(error(&expr.span, "exec code cannot match on non-exec value"));
            }
            record.erasure_modes.condition_modes.push((expr.span.clone(), mode1));

            match (mode1, arms.len()) {
                (Mode::Spec, 0) => {
                    // We treat spec types as inhabited,
                    // so empty matches on spec values would be unsound.
                    return Err(error(&expr.span, "match must have at least one arm"));
                }
                _ => {}
            }
            let mut final_mode = outer_mode;
            for arm in arms.iter() {
                let mut typing = typing.push_var_scope();
                add_pattern(ctxt, record, &mut typing, mode1, &arm.x.pattern)?;
                let arm_outer_mode = match (outer_mode, mode1) {
                    (Mode::Exec, Mode::Spec | Mode::Proof) => Mode::Proof,
                    (m, _) => m,
                };
                let guard_mode =
                    check_expr(ctxt, record, &mut typing, arm_outer_mode, &arm.x.guard)?;
                let arm_outer_mode = match (arm_outer_mode, guard_mode) {
                    (Mode::Exec, Mode::Spec | Mode::Proof) => Mode::Proof,
                    (m, _) => m,
                };
                let arm_mode = check_expr(ctxt, record, &mut typing, arm_outer_mode, &arm.x.body)?;
                final_mode = mode_join(final_mode, arm_mode);
            }
            Ok(final_mode)
        }
        ExprX::Loop { cond, body, invs, decrease, loop_isolation: _, is_for_loop: _, label: _ } => {
            // We could also allow this for proof, if we check it for termination
            if ctxt.check_ghost_blocks && typing.block_ghostness != Ghost::Exec {
                return Err(error(&expr.span, "cannot use while in proof or spec mode"));
            }
            match typing.update_atomic_insts() {
                None => {}
                Some(ai) => ai.add_loop(&expr.span),
            }
            if let Some(cond) = cond {
                check_expr_has_mode(ctxt, record, typing, outer_mode, cond, Mode::Exec)?;
            }
            check_expr_has_mode(ctxt, record, typing, outer_mode, body, Mode::Exec)?;
            for inv in invs.iter() {
                let mut typing = typing.push_block_ghostness(Ghost::Ghost);
                let mut typing = typing.push_allow_prophecy_dependence(true);
                check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, &inv.inv, Mode::Spec)?;
            }
            for dec in decrease.iter() {
                let mut typing = typing.push_block_ghostness(Ghost::Ghost);
                let mut typing = typing.push_allow_prophecy_dependence(false);
                check_expr_has_mode(ctxt, record, &mut typing, Mode::Spec, dec, Mode::Spec)?;
            }
            Ok(Mode::Exec)
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
                    check_expr_has_mode(ctxt, record, typing, outer_mode, e1, ret_mode)?;
                }
            }
            Ok(Mode::Exec)
        }
        ExprX::BreakOrContinue { label: _, is_break: _ } => Ok(Mode::Exec),
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
            let inner_mode = check_expr_handle_mut_arg(ctxt, record, &mut typing, outer_mode, e1)?;
            let mode = if *alloc_wrapper {
                let (inner_read, inner_write) = inner_mode;
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
                (Mode::Exec, outer_write)
            } else {
                inner_mode
            };
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
            check_expr(ctxt, record, &mut typing, Mode::Proof, e1)
        }
        ExprX::Block(ss, Some(e1)) if ss.len() == 0 => {
            return check_expr_handle_mut_arg(ctxt, record, typing, outer_mode, e1);
        }
        ExprX::Block(ss, e1) => {
            let mut typing = typing.push_var_multi_scope();
            for stmt in ss.iter() {
                typing.add_var_multi_scope();
                check_stmt(ctxt, record, &mut typing, outer_mode, stmt)?;
            }
            let mode = match e1 {
                None => outer_mode,
                Some(expr) => check_expr(ctxt, record, &mut typing, outer_mode, expr)?,
            };
            Ok(mode)
        }
        ExprX::OpenInvariant(inv, binder, body, atomicity) => {
            if outer_mode == Mode::Spec {
                return Err(error(&expr.span, "Cannot open invariant in Spec mode."));
            }

            let mut ghost_typing = typing.push_block_ghostness(Ghost::Ghost);
            let mode1 = check_expr(ctxt, record, &mut ghost_typing, outer_mode, inv)?;
            drop(ghost_typing);

            if mode1 != Mode::Proof {
                return Err(error(&inv.span, "Invariant must be Proof mode."));
            }
            let mut typing = typing.push_var_scope();

            typing.insert(&binder.name, Mode::Proof);

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
                let _ = check_expr(ctxt, record, &mut typing, outer_mode, body)?;
            } else {
                let mut typing = typing.push_atomic_insts(Some(AtomicInstCollector::new()));
                let _ = check_expr(ctxt, record, &mut typing, outer_mode, body)?;
                typing
                    .atomic_insts
                    .as_ref()
                    .expect("my_atomic_insts")
                    .validate(&body.span, false)?;
            }

            Ok(Mode::Exec)
        }
        ExprX::AirStmt(_) => Ok(Mode::Exec),
        ExprX::NeverToAny(e) => {
            let mode = check_expr(ctxt, record, typing, outer_mode, e)?;
            if mode == Mode::Spec {
                return Err(error(&expr.span, "never-to-any coercion is not allowed in spec mode"));
            }
            Ok(mode)
        }
        ExprX::Nondeterministic => {
            panic!("Nondeterministic is not created by user code right now");
        }
        ExprX::BorrowMut(place) | ExprX::TwoPhaseBorrowMut(place) => {
            if typing.in_forall_stmt {
                return Err(error(
                    &expr.span,
                    "mutable borrow is not allowed in 'assert ... by' statement",
                ));
            }
            if typing.in_proof_in_spec || outer_mode == Mode::Spec {
                return Err(error(&expr.span, "mutable borrow is not allowed in spec context"));
            }

            let mode =
                check_place(ctxt, record, typing, outer_mode, place, PlaceAccess::MutBorrow)?;
            if mode != Mode::Exec {
                return Err(error(
                    &place.span,
                    format!(
                        "can only take mutable borrow of an exec-mode place; found {:}-mode place",
                        mode
                    ),
                ));
            }
            Ok(Mode::Exec)
        }
        ExprX::UnaryOpr(UnaryOpr::HasResolved(_t), e) => {
            if ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return Err(error(&expr.span, "cannot use `has_resolved` in exec mode"));
            }
            if !typing.allow_prophecy_dependence {
                return Err(error(
                    &expr.span,
                    "cannot use prophecy-dependent predicate `has_resolved` in prophecy-independent context",
                ));
            }
            check_expr_has_mode(ctxt, record, typing, Mode::Spec, e, Mode::Spec)?;
            Ok(outer_mode)
        }
        ExprX::ReadPlace(place, read_kind) => {
            if !typing.allow_prophecy_dependence
                && matches!(read_kind.preliminary_kind, ReadKind::SpecAfterBorrow)
            {
                return Err(error(
                    &expr.span,
                    "cannot use prophecy-dependent function `after_borrow` in prophecy-independent context",
                ));
            }

            let mode = check_place(ctxt, record, typing, outer_mode, place, PlaceAccess::Read)?;

            // TODO(new_mut_ref) this is not aggressive enough about marking stuff as spec;
            // we also need to take the expected mode into account
            let final_read_kind = match mode {
                Mode::Spec => ReadKind::Spec,
                _ => read_kind.preliminary_kind,
            };
            record.read_kind_finals.insert(read_kind.id, final_read_kind);

            // TODO(new_mut_ref) if the ReadKind is spec, we should check that it really is spec

            Ok(mode)
        }
        ExprX::UseLeftWhereRightCanHaveNoAssignments(..) => {
            panic!("UseLeftWhereRightCanHaveNoAssignments shouldn't be created yet");
        }
    };
    Ok((mode?, None))
}

fn check_stmt(
    ctxt: &Ctxt,
    record: &mut Record,
    typing: &mut Typing,
    outer_mode: Mode,
    stmt: &Stmt,
) -> Result<(), VirErr> {
    match &stmt.x {
        StmtX::Expr(e) => {
            let _ = check_expr(ctxt, record, typing, outer_mode, e)?;
            Ok(())
        }
        StmtX::Decl { pattern, mode: None, init, els: _ } => {
            // Special case mode inference just for our encoding of "let tracked pat = ..."
            // in Rust as "let xl; ... { let pat ... xl = xr; }".
            match (&pattern.x, init) {
                (
                    PatternX::Var(PatternBinding {
                        name: x,
                        mutable: _,
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
        StmtX::Decl { pattern, mode: Some(mode), init, els } => {
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
            add_pattern(ctxt, record, typing, mode, pattern)?;
            match init.as_ref() {
                None => {}
                Some(place) => {
                    check_place_has_mode(
                        ctxt,
                        record,
                        typing,
                        outer_mode,
                        place,
                        mode,
                        PlaceAccess::Read,
                    )?;
                }
            }
            match els.as_ref() {
                None => {}
                Some(expr) => {
                    if mode != Mode::Exec {
                        return Err(error(&stmt.span, "let-else only work in exec mode"));
                    }
                    check_expr_has_mode(ctxt, record, typing, outer_mode, expr, mode)?;
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

    let mut fun_typing0 = typing.push_var_scope();

    if function.x.attrs.prophecy_dependent {
        if function.x.mode != Mode::Spec {
            return Err(error(
                &function.span,
                "prophetic attribute can only be applied to 'spec' functions",
            ));
        }
    }
    let mut fun_typing =
        fun_typing0.push_allow_prophecy_dependence(function.x.attrs.prophecy_dependent);

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
        fun_typing.insert(&param.x.name, inner_param_mode);
    }

    for expr in function.x.require.iter() {
        let mut req_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
        let mut req_typing = req_typing.push_allow_prophecy_dependence(true);
        check_expr_has_mode(ctxt, record, &mut req_typing, Mode::Spec, expr, Mode::Spec)?;
    }

    let mut ens_typing = fun_typing.push_var_scope();
    if function.x.ens_has_return {
        ens_typing.insert(&function.x.ret.x.name, function.x.ret.x.mode);
    }
    for expr in function.x.ensure.0.iter().chain(function.x.ensure.1.iter()) {
        let mut ens_typing = ens_typing.push_block_ghostness(Ghost::Ghost);
        let mut ens_typing = ens_typing.push_allow_prophecy_dependence(true);
        check_expr_has_mode(ctxt, record, &mut ens_typing, Mode::Spec, expr, Mode::Spec)?;
    }
    drop(ens_typing);

    if let Some(expr) = &function.x.returns {
        let mut ret_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
        let mut ret_typing = ret_typing.push_allow_prophecy_dependence(true);
        check_expr_has_mode(ctxt, record, &mut ret_typing, Mode::Spec, expr, Mode::Spec)?;
    }

    for expr in function.x.decrease.iter() {
        let mut dec_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
        let mut dec_typing = dec_typing.push_allow_prophecy_dependence(false);
        check_expr_has_mode(ctxt, record, &mut dec_typing, Mode::Spec, expr, Mode::Spec)?;
    }
    if let Some(mask_spec) = &function.x.mask_spec {
        for expr in mask_spec.exprs().iter() {
            let mut dec_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
            check_expr_has_mode(ctxt, record, &mut dec_typing, Mode::Spec, expr, Mode::Spec)?;
        }
    }
    match &function.x.unwind_spec {
        None | Some(UnwindSpec::MayUnwind | UnwindSpec::NoUnwind) => {}
        Some(UnwindSpec::NoUnwindWhen(expr)) => {
            let mut dec_typing = fun_typing.push_block_ghostness(Ghost::Ghost);
            check_expr_has_mode(ctxt, record, &mut dec_typing, Mode::Spec, expr, Mode::Spec)?;
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
        check_expr_has_mode(
            ctxt,
            record,
            &mut body_typing,
            function.x.mode,
            body,
            function.x.ret.x.mode,
        )?;

        // Replace InferSpecForLoopIter None if it fails to have mode spec
        // (if it's mode spec, leave as is to be processed by sst_to_air and loop_inference)
        let infer_spec = record.infer_spec_for_loop_iter_modes.as_ref().expect("infer_spec");
        if infer_spec.len() > 0 {
            let mut functionx = function.x.clone();
            functionx.body = Some(crate::ast_visitor::map_expr_visitor(body, &|expr: &Expr| {
                match &expr.x {
                    ExprX::Unary(op @ UnaryOp::InferSpecForLoopIter { .. }, e) => {
                        let mode_opt = infer_spec.iter().find(|(span, _)| span.id == expr.span.id);
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
                    _ => Ok(expr.clone()),
                }
            })?);
            *function = function.new_x(functionx);
        }
        record.infer_spec_for_loop_iter_modes = None;

        if function.x.mode != Mode::Spec || function.x.ret.x.mode != Mode::Spec {
            let functionx = &mut Arc::make_mut(&mut *function).x;
            crate::user_defined_type_invariants::annotate_user_defined_invariants(
                functionx,
                &record.type_inv_info,
                &ctxt.funs,
                &ctxt.datatypes,
            )?;
            if new_mut_ref {
                if functionx.body.is_some() {
                    functionx.body = Some(crate::resolution_inference::infer_resolution(
                        &functionx.params,
                        functionx.body.as_ref().unwrap(),
                        &record.read_kind_finals,
                        &ctxt.datatypes,
                        &ctxt.funs,
                        &record.var_modes,
                        &record.temporary_modes,
                    ));
                }
            }
        }
    }
    drop(fun_typing);
    drop(fun_typing0);
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
    let erasure_modes = ErasureModes { condition_modes: vec![], var_modes: vec![] };
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
    };
    let mut state = State {
        vars: ScopeMap::new(),
        in_forall_stmt: false,
        in_proof_in_spec: false,
        block_ghostness: Ghost::Exec,
        ret_mode: None,
        atomic_insts: None,
        allow_prophecy_dependence: false,
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
