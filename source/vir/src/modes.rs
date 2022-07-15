use crate::ast::{
    BinaryOp, CallTarget, Datatype, Expr, ExprX, FieldOpr, Fun, Function, FunctionKind, Ident,
    InferMode, InvAtomicity, Krate, Mode, MultiOp, Path, Pattern, PatternX, Stmt, StmtX, UnaryOpr,
    VirErr,
};
use crate::ast_util::{err_str, err_string, get_field};
use crate::util::vec_map_result;
use air::ast::Span;
use air::errors::{error, error_with_label};
use air::scope_map::ScopeMap;
use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::mem::swap;

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
    /// In a ghost block, and lifetime checking is enabled iff tracked == true
    Ghost { tracked: bool },
}

// Placeholder for the erasure expected mode, which is computed after first mode checking pass.
// (See in erase_expr(..., expect: Mode, ...) in erase.rs.)
// We compute the erasure expected mode here so that the AIR/SMT generation can use it.
// For example, if there are arithmetic operations that are exec (and therefore not erased),
// then the AIR/SMT code will insert overflow checks for those arithmetic operations.
// Example:
//   fn test(#[exec] e: u64, #[spec] s: u64) {
//     if e + 1 < s { ... }
//   }
// Here, e + 1 < y is erased because the "<" comparison with s is spec, not exec.
// Therefore, the e + 1 is a spec-mode arithmetic operation, not an exec-mode arithmetic operation.
// However, the mode checker doesn't know this when it first descends into e + 1:
//   - the "if" expression can take a spec or proof or exec condition, so this doesn't constrain
//     the mode of e + 1 < s a priori
//   - the "<" expression can take spec or proof or exec subexpressions, so this doesn't constrain
//     the mode of e + 1 a priori
//   - we check the left side e + 1 before we check the right side s,
//     so when we first reach e + 1, we don't yet know that "<"'s right side is spec
// Therefore, we use Cell to delay the decision about the erasure expected mode of e + 1.
type ErasureMode = std::rc::Rc<ErasureModeX>;
enum ErasureModeX {
    Mode(std::cell::Cell<Option<Mode>>),
    Join(ErasureMode, ErasureMode),
}

impl ErasureModeX {
    fn new(mode: Option<Mode>) -> ErasureMode {
        std::rc::Rc::new(ErasureModeX::Mode(std::cell::Cell::new(mode)))
    }
    fn join(m1: &ErasureMode, m2: &ErasureMode) -> ErasureMode {
        std::rc::Rc::new(ErasureModeX::Join(m1.clone(), m2.clone()))
    }
    fn set(&self, mode: Mode) {
        if let ErasureModeX::Mode(cell) = self {
            cell.set(Some(mode));
        } else {
            panic!("unexpected ErasureMode");
        }
    }
    fn force(&self) -> Mode {
        match self {
            ErasureModeX::Mode(cell) => cell.get().expect("unresolved ErasureMode"),
            ErasureModeX::Join(m1, m2) => mode_join(m1.force(), m2.force()),
        }
    }
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
            Mode::Spec | Mode::Proof => Ghost::Ghost { tracked: false },
            Mode::Exec => Ghost::Exec,
        }
    }

    fn to_mode(self) -> Mode {
        match self {
            Ghost::Ghost { tracked: false } => Mode::Spec,
            Ghost::Ghost { tracked: true } => Mode::Proof,
            Ghost::Exec => Mode::Exec,
        }
    }
}

struct Typing {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) datatypes: HashMap<Path, Datatype>,
    pub(crate) traits: HashSet<Path>,
    // for each variable: (is_mutable, mode)
    pub(crate) vars: ScopeMap<Ident, (bool, Mode)>,
    pub(crate) erasure_modes: ErasureModes,
    inferred_modes: HashMap<InferMode, ErasureMode>,
    pub(crate) in_forall_stmt: bool,
    pub(crate) check_ghost_blocks: bool,
    // Are we in a syntactic ghost block?
    // If not, Ghost::Exec (corresponds to exec mode).
    // If yes (corresponding to proof/spec mode), say whether variables are tracked or not.
    // (note that tracked may be false even in proof mode,
    // and tracked is allowed in spec mode, although that would be needlessly constraining)
    pub(crate) block_ghostness: Ghost,
    pub(crate) fun_mode: Mode,
    pub(crate) ret_mode: Option<Mode>,
    pub(crate) atomic_insts: Option<AtomicInstCollector>,
}

impl Typing {
    fn get(&self, x: &Ident) -> (bool, Mode) {
        *self.vars.get(x).expect("internal error: missing mode")
    }

    fn insert(&mut self, _span: &Span, x: &Ident, mutable: bool, mode: Mode) {
        self.vars.insert(x.clone(), (mutable, mode)).expect("internal error: Typing insert");
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

#[derive(Default)]
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
                format!("{context:} cannot contain an 'exec' loop"),
                inv_block_span,
                "this invariant block contains a loop",
            )
            .secondary_span(&self.loops[0]));
        } else if self.non_atomics.len() > 0 {
            let mut e =
                error(format!("{context:} cannot contain non-atomic operations"), inv_block_span);
            for i in 0..min(self.non_atomics.len(), 3) {
                e = e.secondary_label(&self.non_atomics[i], "non-atomic here");
            }
            return Err(e);
        } else if self.atomics.len() > 1 {
            let mut e = error(
                format!("{context:} cannot contain more than 1 atomic operation"),
                inv_block_span,
            );
            for i in 0..min(self.atomics.len(), 3) {
                e = e.secondary_label(&self.atomics[i], "atomic here");
            }
            return Err(e);
        }
        Ok(())
    }
}

fn check_expr_has_mode(
    typing: &mut Typing,
    outer_mode: Mode,
    expr: &Expr,
    expected: Mode,
) -> Result<(), VirErr> {
    let mode = check_expr(typing, outer_mode, &ErasureModeX::new(Some(expected)), expr)?;
    match &*expr.typ {
        crate::ast::TypX::Tuple(ts) if ts.len() == 0 => return Ok(()),
        _ => {}
    }
    if !mode_le(mode, expected) {
        err_string(&expr.span, format!("expression has mode {}, expected mode {}", mode, expected))
    } else {
        Ok(())
    }
}

fn add_pattern(typing: &mut Typing, mode: Mode, pattern: &Pattern) -> Result<(), VirErr> {
    typing.erasure_modes.var_modes.push((pattern.span.clone(), mode));
    match &pattern.x {
        PatternX::Wildcard => Ok(()),
        PatternX::Var { name: x, mutable } => {
            typing.insert(&pattern.span, x, *mutable, mode);
            Ok(())
        }
        PatternX::Tuple(patterns) => {
            for p in patterns.iter() {
                add_pattern(typing, mode, p)?;
            }
            Ok(())
        }
        PatternX::Constructor(datatype, variant, patterns) => {
            let datatype = typing.datatypes[datatype].clone();
            let variant =
                datatype.x.variants.iter().find(|v| v.name == *variant).expect("missing variant");
            for (binder, field) in patterns.iter().zip(variant.a.iter()) {
                let (_, field_mode, _) = field.a;
                add_pattern(typing, mode_join(field_mode, mode), &binder.a)?;
            }
            Ok(())
        }
    }
}

fn get_var_loc_mode(typing: &mut Typing, expr: &Expr, init_not_mut: bool) -> Result<Mode, VirErr> {
    let x_mode = match &expr.x {
        ExprX::VarLoc(x) => {
            let (_, x_mode) = typing.get(x);
            if typing.block_ghostness != Ghost::Exec && expr.typ.is_ghost_typ() {
                Mode::Spec
            } else if typing.block_ghostness != Ghost::Exec
                && expr.typ.is_tracked_typ()
                && x_mode != Mode::Spec
            {
                Mode::Proof
            } else {
                x_mode
            }
        }
        ExprX::UnaryOpr(UnaryOpr::Field(FieldOpr { datatype, variant: _, field }), rcvr) => {
            let rcvr_mode = get_var_loc_mode(typing, rcvr, init_not_mut)?;
            let datatype = &typing.datatypes[datatype].x;
            if datatype.unforgeable {
                return err_str(&expr.span, "unforgeable datatypes cannot be updated");
            }
            assert!(datatype.variants.len() == 1);
            let (_, field_mode, _) = &datatype.variants[0]
                .a
                .iter()
                .find(|x| x.name == *field)
                .expect("datatype field valid")
                .a;
            mode_join(rcvr_mode, *field_mode)
        }
        _ => {
            panic!("unexpected loc {:?}", expr);
        }
    };
    if x_mode == Mode::Spec && init_not_mut {
        return err_str(
            &expr.span,
            "delayed assignment to non-mut let not allowed for spec variables",
        );
    }
    typing.erasure_modes.var_modes.push((expr.span.clone(), x_mode));
    Ok(x_mode)
}

fn check_expr(
    typing: &mut Typing,
    outer_mode: Mode,
    erasure_mode: &ErasureMode,
    expr: &Expr,
) -> Result<Mode, VirErr> {
    match &expr.x {
        ExprX::Const(_) => Ok(Mode::Exec),
        ExprX::Var(x) | ExprX::VarLoc(x) | ExprX::VarAt(x, _) => {
            let mode = mode_join(outer_mode, typing.get(x).1);
            if typing.in_forall_stmt && mode == Mode::Proof {
                // Proof variables may be used as spec, but not as proof inside forall statements.
                // This protects against effectively consuming a linear proof variable
                // multiple times for different instantiations of the forall variables.
                return err_str(
                    &expr.span,
                    "cannot use proof variable inside forall/assert_by statements",
                );
            }
            let mode = if typing.check_ghost_blocks {
                mode_join(mode, typing.block_ghostness.to_mode())
            } else {
                mode
            };
            typing.erasure_modes.var_modes.push((expr.span.clone(), mode));
            Ok(mode)
        }
        ExprX::ConstVar(x) => {
            let function = match typing.funs.get(x) {
                None => {
                    let name = crate::ast_util::path_as_rust_name(&x.path);
                    return err_string(&expr.span, format!("cannot find constant {}", name));
                }
                Some(f) => f.clone(),
            };
            let mode = function.x.ret.x.mode;
            let mode = if typing.check_ghost_blocks {
                mode_join(mode, typing.block_ghostness.to_mode())
            } else {
                mode
            };
            typing.erasure_modes.var_modes.push((expr.span.clone(), mode));
            Ok(mode)
        }
        ExprX::Call(CallTarget::Static(x, _), es) => {
            let function = match typing.funs.get(x) {
                None => {
                    let name = crate::ast_util::path_as_rust_name(&x.path);
                    return err_string(&expr.span, format!("cannot find function {}", name));
                }
                Some(f) => f.clone(),
            };
            if function.x.mode == Mode::Exec {
                match &mut typing.atomic_insts {
                    None => {}
                    Some(ai) => {
                        if function.x.attrs.atomic {
                            ai.add_atomic(&expr.span);
                        } else {
                            ai.add_non_atomic(&expr.span);
                        }
                    }
                }
            }
            if typing.check_ghost_blocks {
                if (function.x.mode == Mode::Exec) != (typing.block_ghostness == Ghost::Exec) {
                    return err_string(
                        &expr.span,
                        format!("cannot call function with mode {}", function.x.mode),
                    );
                }
            }
            if !mode_le(outer_mode, function.x.mode) {
                return err_string(
                    &expr.span,
                    format!("cannot call function with mode {}", function.x.mode),
                );
            }
            for (param, arg) in function.x.params.iter().zip(es.iter()) {
                let param_mode = mode_join(outer_mode, param.x.mode);
                if param.x.is_mut {
                    if typing.in_forall_stmt {
                        return err_str(
                            &arg.span,
                            "cannot call function with &mut parameter inside forall/assert_by statements",
                        );
                    }
                    let arg_erasure = ErasureModeX::new(Some(param.x.mode));
                    let arg_mode = check_expr(typing, outer_mode, &arg_erasure, arg)?;
                    if arg_mode != param_mode {
                        return err_string(
                            &param.span,
                            format!(
                                "expected mode {}, &mut argument has mode {}",
                                param_mode, arg_mode
                            ),
                        );
                    }
                } else {
                    check_expr_has_mode(typing, param_mode, arg, param.x.mode)?;
                }
            }
            Ok(function.x.ret.x.mode)
        }
        ExprX::Call(CallTarget::FnSpec(e0), es) => {
            // TODO call `add_non_atomic` if this is ever supported for exec-mode functions
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot call spec function from exec mode");
            }
            check_expr_has_mode(typing, Mode::Spec, e0, Mode::Spec)?;
            for arg in es.iter() {
                check_expr_has_mode(typing, Mode::Spec, arg, Mode::Spec)?;
            }
            Ok(Mode::Spec)
        }
        ExprX::Tuple(es) => {
            let modes = vec_map_result(es, |e| check_expr(typing, outer_mode, erasure_mode, e))?;
            Ok(modes.into_iter().fold(outer_mode, mode_join))
        }
        ExprX::Ctor(path, variant, binders, update) => {
            let datatype = &typing.datatypes[path].clone();
            let variant = datatype.x.get_variant(variant);
            let mut mode = mode_join(outer_mode, datatype.x.mode);
            if let Some(update) = update {
                mode = mode_join(mode, check_expr(typing, outer_mode, erasure_mode, update)?);
            }
            for arg in binders.iter() {
                let (_, field_mode, _) = get_field(&variant.a, &arg.name).a;
                let field_erasure_mode =
                    ErasureModeX::join(&erasure_mode, &ErasureModeX::new(Some(field_mode)));
                let mode_arg = check_expr(
                    typing,
                    mode_join(outer_mode, field_mode),
                    &field_erasure_mode,
                    &arg.a,
                )?;
                if !mode_le(mode_arg, field_mode) {
                    // allow this arg by weakening whole struct's mode
                    mode = mode_join(mode, mode_arg);
                }
            }

            if datatype.x.unforgeable && mode == Mode::Proof {
                return err_str(&expr.span, "cannot construct an unforgeable proof object");
            }

            Ok(mode)
        }
        ExprX::Unary(_, e1) => check_expr(typing, outer_mode, erasure_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::Box(_), e1) => check_expr(typing, outer_mode, erasure_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::Unbox(_), e1) => check_expr(typing, outer_mode, erasure_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::HasType(_), _) => panic!("internal error: HasType in modes.rs"),
        ExprX::UnaryOpr(UnaryOpr::IsVariant { .. }, e1) => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot test variant in exec mode");
            }
            check_expr(typing, outer_mode, erasure_mode, e1)
        }
        ExprX::UnaryOpr(UnaryOpr::TupleField { .. }, e1) => {
            check_expr(typing, outer_mode, erasure_mode, e1)
        }
        ExprX::UnaryOpr(UnaryOpr::Field(FieldOpr { datatype, variant, field }), e1) => {
            let e1_mode = check_expr(typing, outer_mode, erasure_mode, e1)?;
            let datatype = &typing.datatypes[datatype];
            let field = get_field(&datatype.x.get_variant(variant).a, field);
            Ok(mode_join(e1_mode, field.a.1))
        }
        ExprX::Loc(e) => check_expr(typing, outer_mode, erasure_mode, e),
        ExprX::Binary(op, e1, e2) => {
            let op_mode = match op {
                BinaryOp::Eq(mode) => *mode,
                _ => Mode::Exec,
            };
            match op {
                BinaryOp::Arith(_, id) => {
                    assert!(!typing.inferred_modes.contains_key(id));
                    typing.inferred_modes.insert(*id, erasure_mode.clone());
                }
                _ => {}
            }
            let outer_mode = match op {
                // because Implies isn't compiled, make it spec-only
                BinaryOp::Implies => mode_join(outer_mode, Mode::Spec),
                _ => outer_mode,
            };
            let mode1 = check_expr(typing, outer_mode, erasure_mode, e1)?;
            let mode2 = check_expr(typing, outer_mode, erasure_mode, e2)?;
            Ok(mode_join(op_mode, mode_join(mode1, mode2)))
        }
        ExprX::Multi(MultiOp::Chained(_), es) => {
            for e in es.iter() {
                check_expr_has_mode(typing, Mode::Spec, e, Mode::Spec)?;
            }
            Ok(Mode::Spec)
        }
        ExprX::Quant(_, binders, e1) => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot use forall/exists in exec mode");
            }
            typing.vars.push_scope(true);
            for binder in binders.iter() {
                typing.insert(&expr.span, &binder.name, false, Mode::Spec);
            }
            check_expr_has_mode(typing, Mode::Spec, e1, Mode::Spec)?;
            typing.vars.pop_scope();
            Ok(Mode::Spec)
        }
        ExprX::Closure(params, body) => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "not supported yet: closures in exec mode");
            }
            typing.vars.push_scope(true);
            for binder in params.iter() {
                typing.insert(&expr.span, &binder.name, false, Mode::Spec);
            }

            let mut inner_atomic_insts = None;
            swap(&mut inner_atomic_insts, &mut typing.atomic_insts);

            check_expr_has_mode(typing, Mode::Spec, body, Mode::Spec)?;

            swap(&mut inner_atomic_insts, &mut typing.atomic_insts);

            typing.vars.pop_scope();
            Ok(Mode::Spec)
        }
        ExprX::Choose { params, cond, body } => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot use choose in exec mode");
            }
            typing.vars.push_scope(true);
            for binder in params.iter() {
                typing.insert(&expr.span, &binder.name, false, Mode::Spec);
            }
            check_expr_has_mode(typing, Mode::Spec, cond, Mode::Spec)?;
            check_expr_has_mode(typing, Mode::Spec, body, Mode::Spec)?;
            typing.vars.pop_scope();
            Ok(Mode::Spec)
        }
        ExprX::WithTriggers { triggers, body } => {
            for trigger in triggers.iter() {
                for term in trigger.iter() {
                    check_expr_has_mode(typing, Mode::Spec, term, Mode::Spec)?;
                }
            }
            check_expr_has_mode(typing, Mode::Spec, body, Mode::Spec)?;
            Ok(Mode::Spec)
        }
        ExprX::Assign { init_not_mut, lhs, rhs } => {
            if typing.in_forall_stmt {
                return err_str(&expr.span, "assignment is not allowed in forall statements");
            }
            let x_mode = get_var_loc_mode(typing, lhs, *init_not_mut)?;
            if !mode_le(outer_mode, x_mode) {
                return err_string(
                    &expr.span,
                    format!("cannot assign to {x_mode} variable from {outer_mode} mode"),
                );
            }
            check_expr_has_mode(typing, outer_mode, rhs, x_mode)?;
            Ok(x_mode)
        }
        ExprX::Fuel(_, _) => Ok(outer_mode),
        ExprX::Header(_) => panic!("internal error: Header shouldn't exist here"),
        ExprX::Admit => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot use admit in exec mode");
            }
            Ok(outer_mode)
        }
        ExprX::Forall { vars, require, ensure, proof } => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot use assert_forall in exec mode");
            }
            let in_forall_stmt = typing.in_forall_stmt;
            // REVIEW: we could allow proof vars when vars.len() == 0,
            // but we'd have to implement the proper lifetime checking in erase.rs
            typing.in_forall_stmt = true;
            typing.vars.push_scope(true);
            for var in vars.iter() {
                typing.insert(&expr.span, &var.name, false, Mode::Spec);
            }
            check_expr_has_mode(typing, Mode::Spec, require, Mode::Spec)?;
            check_expr_has_mode(typing, Mode::Spec, ensure, Mode::Spec)?;
            check_expr_has_mode(typing, Mode::Proof, proof, Mode::Proof)?;
            typing.vars.pop_scope();
            typing.in_forall_stmt = in_forall_stmt;
            Ok(Mode::Proof)
        }
        ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot use assert in exec mode");
            }
            for req in requires.iter() {
                check_expr_has_mode(typing, Mode::Spec, req, Mode::Spec)?;
            }
            for ens in ensures.iter() {
                check_expr_has_mode(typing, Mode::Spec, ens, Mode::Spec)?;
            }
            check_expr_has_mode(typing, Mode::Proof, proof, Mode::Proof)?;
            Ok(Mode::Proof)
        }
        ExprX::AssertBV(e) => {
            if typing.check_ghost_blocks && typing.block_ghostness == Ghost::Exec {
                return err_str(&expr.span, "cannot use assert in exec mode");
            }
            check_expr_has_mode(typing, Mode::Spec, e, Mode::Spec)?;
            Ok(Mode::Proof)
        }
        ExprX::If(e1, e2, e3) => {
            let erasure_mode1 = ErasureModeX::new(None);
            let mode1 = check_expr(typing, outer_mode, &erasure_mode1, e1)?;
            if typing.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode1 != Mode::Exec
            {
                return err_str(&expr.span, "condition must have mode exec");
            }
            erasure_mode1.set(mode1);
            typing.erasure_modes.condition_modes.push((expr.span.clone(), mode1));

            let mode_branch = match (outer_mode, mode1) {
                (Mode::Exec, Mode::Spec) => Mode::Proof,
                _ => outer_mode,
            };
            let mode2 = check_expr(typing, mode_branch, erasure_mode, e2)?;
            match e3 {
                None => Ok(mode2),
                Some(e3) => {
                    let mode3 = check_expr(typing, mode_branch, erasure_mode, e3)?;
                    Ok(mode_join(mode2, mode3))
                }
            }
        }
        ExprX::Match(e1, arms) => {
            let erasure_mode1 = ErasureModeX::new(None);
            let mode1 = check_expr(typing, outer_mode, &erasure_mode1, e1)?;
            if typing.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode1 != Mode::Exec
            {
                return err_str(&expr.span, "exec code cannot match on non-exec value");
            }
            erasure_mode1.set(mode1);
            typing.erasure_modes.condition_modes.push((expr.span.clone(), mode1));

            match (mode1, arms.len()) {
                (Mode::Spec, 0) => {
                    // We treat spec types as inhabited,
                    // so empty matches on spec values would be unsound.
                    return err_str(&expr.span, "match must have at least one arm");
                }
                _ => {}
            }
            let mut final_mode = outer_mode;
            for arm in arms.iter() {
                typing.vars.push_scope(true);
                add_pattern(typing, mode1, &arm.x.pattern)?;
                let arm_outer_mode = match (outer_mode, mode1) {
                    (Mode::Exec, Mode::Spec | Mode::Proof) => Mode::Proof,
                    (m, _) => m,
                };
                let guard_mode = check_expr(typing, arm_outer_mode, erasure_mode, &arm.x.guard)?;
                let arm_outer_mode = match (arm_outer_mode, guard_mode) {
                    (Mode::Exec, Mode::Spec | Mode::Proof) => Mode::Proof,
                    (m, _) => m,
                };
                let arm_mode = check_expr(typing, arm_outer_mode, erasure_mode, &arm.x.body)?;
                final_mode = mode_join(final_mode, arm_mode);
                typing.vars.pop_scope();
            }
            Ok(final_mode)
        }
        ExprX::While { cond, body, invs } => {
            // We could also allow this for proof, if we check it for termination
            if typing.check_ghost_blocks && typing.block_ghostness != Ghost::Exec {
                return err_str(&expr.span, "cannot use while in proof or spec mode");
            }
            match &mut typing.atomic_insts {
                None => {}
                Some(ai) => ai.add_loop(&expr.span),
            }
            check_expr_has_mode(typing, outer_mode, cond, Mode::Exec)?;
            check_expr_has_mode(typing, outer_mode, body, Mode::Exec)?;
            for inv in invs.iter() {
                let prev = typing.block_ghostness;
                typing.block_ghostness = Ghost::Ghost { tracked: false };
                check_expr_has_mode(typing, Mode::Spec, inv, Mode::Spec)?;
                typing.block_ghostness = prev;
            }
            Ok(Mode::Exec)
        }
        ExprX::Return(e1) => {
            if typing.check_ghost_blocks {
                match (typing.fun_mode, typing.block_ghostness) {
                    (Mode::Exec, Ghost::Exec) => {}
                    (Mode::Proof, _) => {}
                    (Mode::Spec, _) => {}
                    (Mode::Exec, _) => {
                        return err_str(
                            &expr.span,
                            "cannot return from non-exec code in exec function",
                        );
                    }
                }
            } else {
                match (typing.fun_mode, outer_mode) {
                    (Mode::Exec, Mode::Exec) => {}
                    (Mode::Proof, _) => {}
                    (Mode::Spec, _) => {}
                    (Mode::Exec, _) => {
                        return err_str(
                            &expr.span,
                            "cannot return from non-exec code in exec function",
                        );
                    }
                }
            }
            if typing.in_forall_stmt {
                return err_str(&expr.span, "return is not allowed in forall statements");
            }
            match (e1, typing.ret_mode) {
                (None, _) => {}
                (_, None) => panic!("internal error: missing return type"),
                (Some(e1), Some(ret_mode)) => {
                    check_expr_has_mode(typing, outer_mode, e1, ret_mode)?;
                }
            }
            Ok(Mode::Exec)
        }
        ExprX::Ghost { alloc_wrapper, tracked, expr: e1 } => {
            let prev = typing.block_ghostness;
            let block_ghostness = match (prev, alloc_wrapper, tracked) {
                (Ghost::Exec, None, false) => match &*e1.typ {
                    crate::ast::TypX::Tuple(ts) if ts.len() == 0 => Ghost::Ghost { tracked: false },
                    _ => {
                        return err_str(&expr.span, "proof block must have type ()");
                    }
                },
                (_, None, false) => {
                    return err_str(&expr.span, "already in proof mode");
                }
                (Ghost::Exec, None, true) => {
                    return err_str(&expr.span, "cannot mark expression as tracked in exec mode");
                }
                (Ghost::Ghost { .. }, None, true) => Ghost::Ghost { tracked: true },
                (Ghost::Exec, Some(_), _) => Ghost::Ghost { tracked: *tracked },
                (Ghost::Ghost { .. }, Some(_), _) => {
                    return err_str(
                        &expr.span,
                        "ghost(...) or tracked(...) can only be used in exec mode",
                    );
                }
            };
            typing.block_ghostness = block_ghostness;
            let outer_mode = match (outer_mode, block_ghostness) {
                (Mode::Exec, Ghost::Ghost { .. }) => Mode::Proof,
                _ => outer_mode,
            };
            let mode = if alloc_wrapper.is_none() {
                check_expr(typing, outer_mode, erasure_mode, e1)?
            } else {
                let target_mode = if *tracked { Mode::Proof } else { Mode::Spec };
                check_expr_has_mode(typing, outer_mode, e1, target_mode)?;
                Mode::Exec
            };
            typing.block_ghostness = prev;
            Ok(mode)
        }
        ExprX::Block(ss, e1) => {
            for stmt in ss.iter() {
                typing.vars.push_scope(true);
                check_stmt(typing, outer_mode, erasure_mode, stmt)?;
            }
            let mode = match e1 {
                None => outer_mode,
                Some(expr) => check_expr(typing, outer_mode, erasure_mode, expr)?,
            };
            for _ in ss.iter() {
                typing.vars.pop_scope();
            }
            Ok(mode)
        }
        ExprX::OpenInvariant(inv, binder, body, atomicity) => {
            if outer_mode == Mode::Spec {
                return err_string(&expr.span, format!("Cannot open invariant in Spec mode."));
            }
            let mode1 = check_expr(typing, outer_mode, erasure_mode, inv)?;
            if mode1 != Mode::Proof {
                return err_string(&inv.span, format!("Invariant must be Proof mode."));
            }
            typing.vars.push_scope(true);
            typing.insert(&expr.span, &binder.name, /* mutable */ true, Mode::Proof);

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
                let _ = check_expr(typing, outer_mode, erasure_mode, body)?;
            } else {
                let mut my_atomic_insts = Some(AtomicInstCollector::new());
                swap(&mut my_atomic_insts, &mut typing.atomic_insts);
                let _ = check_expr(typing, outer_mode, erasure_mode, body)?;
                swap(&mut my_atomic_insts, &mut typing.atomic_insts);
                my_atomic_insts.expect("my_atomic_insts").validate(&body.span, false)?;
            }

            typing.vars.pop_scope();
            Ok(Mode::Exec)
        }
    }
}

fn check_stmt(
    typing: &mut Typing,
    outer_mode: Mode,
    erasure_mode: &ErasureMode,
    stmt: &Stmt,
) -> Result<(), VirErr> {
    match &stmt.x {
        StmtX::Expr(e) => {
            let _ = check_expr(typing, outer_mode, erasure_mode, e)?;
            Ok(())
        }
        StmtX::Decl { pattern, mode, init } => {
            let mode = if typing.check_ghost_blocks
                && typing.block_ghostness != Ghost::Exec
                && *mode == Mode::Exec
            {
                Mode::Spec
            } else {
                *mode
            };
            if typing.check_ghost_blocks
                && typing.block_ghostness == Ghost::Exec
                && mode != Mode::Exec
            {
                return err_str(&stmt.span, "exec code cannot declare non-exec variables");
            }
            if !mode_le(outer_mode, mode) {
                return err_string(&stmt.span, format!("pattern cannot have mode {}", mode));
            }
            add_pattern(typing, mode, pattern)?;
            match init.as_ref() {
                None => {}
                Some(expr) => {
                    check_expr_has_mode(typing, outer_mode, expr, mode)?;
                }
            }
            Ok(())
        }
    }
}

fn check_function(typing: &mut Typing, function: &Function) -> Result<(), VirErr> {
    typing.vars.push_scope(true);

    if let FunctionKind::TraitMethodImpl { method, trait_path, datatype, .. } = &function.x.kind {
        let datatype_mode = typing.datatypes[datatype].x.mode;
        let self_mode = function.x.params[0].x.mode;
        let our_trait = typing.traits.contains(trait_path);
        if self_mode != function.x.mode {
            // It's hard for erase.rs to support mode != param_mode (we'd have to erase self),
            // so we currently disallow it:
            return err_string(
                &function.x.params[0].span,
                format!(
                    "self has mode {}, function has mode {} -- these cannot be different",
                    self_mode, function.x.mode
                ),
            );
        }
        let (expected_params, expected_ret_mode): (Vec<Mode>, Mode) = if our_trait {
            let trait_method = &typing.funs[method];
            let expect_mode = mode_join(trait_method.x.mode, datatype_mode);
            if function.x.mode != expect_mode {
                return err_string(
                    &function.span,
                    format!("function must have mode {}", expect_mode),
                );
            }
            (trait_method.x.params.iter().map(|f| f.x.mode).collect(), trait_method.x.ret.x.mode)
        } else {
            (function.x.params.iter().map(|_| Mode::Exec).collect(), Mode::Exec)
        };
        assert!(expected_params.len() == function.x.params.len());
        for (param, expect) in function.x.params.iter().zip(expected_params.iter()) {
            let expect_mode = mode_join(*expect, datatype_mode);
            if param.x.mode != expect_mode {
                return err_string(
                    &param.span,
                    format!("parameter must have mode {}", expect_mode),
                );
            }
        }
        if function.x.ret.x.mode != mode_join(expected_ret_mode, datatype_mode) {
            return err_string(
                &function.span,
                format!("function return value must have mode {}", expected_ret_mode),
            );
        }
    }

    for param in function.x.params.iter() {
        if !mode_le(function.x.mode, param.x.mode) {
            return err_string(
                &function.span,
                format!("parameter {} cannot have mode {}", param.x.name, param.x.mode),
            );
        }
        typing.insert(&function.span, &param.x.name, param.x.is_mut, param.x.mode);
    }

    for expr in function.x.require.iter() {
        typing.block_ghostness = Ghost::Ghost { tracked: false };
        check_expr_has_mode(typing, Mode::Spec, expr, Mode::Spec)?;
    }

    typing.vars.push_scope(true);
    if function.x.has_return() {
        typing.insert(&function.span, &function.x.ret.x.name, false, function.x.ret.x.mode);
    }
    for expr in function.x.ensure.iter() {
        typing.block_ghostness = Ghost::Ghost { tracked: false };
        check_expr_has_mode(typing, Mode::Spec, expr, Mode::Spec)?;
    }
    typing.vars.pop_scope();

    for expr in function.x.decrease.iter() {
        typing.block_ghostness = Ghost::Ghost { tracked: false };
        check_expr_has_mode(typing, Mode::Spec, expr, Mode::Spec)?;
    }

    if function.x.has_return() {
        let ret_mode = function.x.ret.x.mode;
        if !function.x.is_const && !mode_le(function.x.mode, ret_mode) {
            return err_string(
                &function.span,
                format!("return type cannot have mode {}", ret_mode),
            );
        }
        if function.x.body.is_none()
            && !matches!(&function.x.kind, FunctionKind::TraitMethodDecl { .. })
        {
            // can't erase return values in external_body functions, so:
            if function.x.mode != ret_mode {
                return err_string(
                    &function.span,
                    format!(
                        "because function has no body, return type cannot have mode {}",
                        ret_mode
                    ),
                );
            }
        }
        typing.ret_mode = Some(ret_mode);
    }
    if let Some(body) = &function.x.body {
        typing.block_ghostness = Ghost::of_mode(function.x.mode);
        check_expr_has_mode(typing, function.x.mode, body, function.x.ret.x.mode)?;
    }
    typing.ret_mode = None;
    typing.vars.pop_scope();
    assert_eq!(typing.vars.num_scopes(), 0);
    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<(ErasureModes, HashMap<InferMode, Mode>), VirErr> {
    let mut funs: HashMap<Fun, Function> = HashMap::new();
    let mut datatypes: HashMap<Path, Datatype> = HashMap::new();
    for function in krate.functions.iter() {
        funs.insert(function.x.name.clone(), function.clone());
    }
    for datatype in krate.datatypes.iter() {
        datatypes.insert(datatype.x.path.clone(), datatype.clone());
    }
    let erasure_modes = ErasureModes { condition_modes: vec![], var_modes: vec![] };
    let mut typing = Typing {
        funs,
        datatypes,
        traits: krate.traits.iter().map(|t| t.x.name.clone()).collect(),
        vars: ScopeMap::new(),
        erasure_modes,
        inferred_modes: HashMap::new(),
        in_forall_stmt: false,
        check_ghost_blocks: false,
        block_ghostness: Ghost::Exec,
        fun_mode: Mode::Exec,
        ret_mode: None,
        atomic_insts: None,
    };
    for function in krate.functions.iter() {
        typing.check_ghost_blocks = function.x.attrs.uses_ghost_blocks;
        typing.fun_mode = function.x.mode;
        if function.x.attrs.atomic {
            let mut my_atomic_insts = Some(AtomicInstCollector::new());
            swap(&mut my_atomic_insts, &mut typing.atomic_insts);

            check_function(&mut typing, function)?;

            swap(&mut my_atomic_insts, &mut typing.atomic_insts);
            my_atomic_insts.expect("my_atomic_insts").validate(&function.span, true)?;
        } else {
            check_function(&mut typing, function)?;
        }
    }
    let inferred_modes = typing.inferred_modes.into_iter().map(|(k, m)| (k, m.force())).collect();
    Ok((typing.erasure_modes, inferred_modes))
}
