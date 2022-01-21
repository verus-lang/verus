use crate::ast::{
    BinaryOp, CallTarget, Datatype, Expr, ExprX, Fun, Function, Ident, Krate, Mode, Path, Pattern,
    PatternX, Stmt, StmtX, UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string, get_field};
use crate::util::vec_map_result;
use air::ast::Span;
use air::errors::{error, error_with_label};
use air::scope_map::ScopeMap;
use std::cmp::min;
use std::collections::HashMap;
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

#[derive(Clone)]
pub struct ErasureModes {
    // Modes of conditions in If
    pub condition_modes: Vec<(Span, Mode)>,
    // Modes of variables in Var, Assign, Decl
    pub var_modes: Vec<(Span, Mode)>,
}

struct Typing {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) datatypes: HashMap<Path, Datatype>,
    // for each variable: (is_mutable, mode)
    pub(crate) vars: ScopeMap<Ident, (bool, Mode)>,
    pub(crate) erasure_modes: ErasureModes,
    pub(crate) in_forall_stmt: bool,
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

// One tricky thing in mode-checking is that an invariant blocks needs to have
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
    pub fn validate(&self, inv_block_span: &Span) -> Result<(), VirErr> {
        if self.loops.len() > 0 {
            return Err(error_with_label(
                "open_invariant cannot contain an 'exec' loop",
                inv_block_span,
                "this invariant block contains a loop",
            )
            .secondary_span(&self.loops[0]));
        } else if self.non_atomics.len() > 0 {
            let mut e =
                error("open_invariant cannot contain non-atomic operations", inv_block_span);
            for i in 0..min(self.non_atomics.len(), 3) {
                e = e.secondary_label(&self.non_atomics[i], "non-atomic here");
            }
            return Err(e);
        } else if self.atomics.len() > 1 {
            let mut e =
                error("open_invariant cannot contain more than 1 atomic operation", inv_block_span);
            for i in 0..min(self.atomics.len(), 3) {
                e = e.secondary_label(&self.atomics[i], "atomic here");
            }
            return Err(e);
        }
        return Ok(());
    }
}

fn check_expr_has_mode(
    typing: &mut Typing,
    outer_mode: Mode,
    expr: &Expr,
    expected: Mode,
) -> Result<(), VirErr> {
    let mode = check_expr(typing, outer_mode, expr)?;
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
                let (_, field_mode) = field.a;
                add_pattern(typing, mode_join(field_mode, mode), &binder.a)?;
            }
            Ok(())
        }
    }
}

fn check_expr(typing: &mut Typing, outer_mode: Mode, expr: &Expr) -> Result<Mode, VirErr> {
    match &expr.x {
        ExprX::Const(_) => Ok(outer_mode),
        ExprX::Var(x) | ExprX::VarAt(x, _) => {
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
                    let arg_mode = check_expr(typing, outer_mode, arg)?;
                    if arg_mode != param_mode {
                        return err_string(
                            &param.span,
                            format!(
                                "expected mode {}, &mut argument has mode {}",
                                param_mode, arg_mode
                            ),
                        );
                    }
                }
                check_expr_has_mode(typing, param_mode, arg, param.x.mode)?;
            }
            Ok(function.x.ret.x.mode)
        }
        ExprX::Call(CallTarget::FnSpec(e0), es) => {
            // TODO call `add_non_atomic` if this is ever supported for exec-mode functions
            check_expr_has_mode(typing, Mode::Spec, e0, Mode::Spec)?;
            for arg in es.iter() {
                check_expr_has_mode(typing, Mode::Spec, arg, Mode::Spec)?;
            }
            Ok(Mode::Spec)
        }
        ExprX::Tuple(es) => {
            let modes = vec_map_result(es, |e| check_expr(typing, outer_mode, e))?;
            Ok(modes.into_iter().fold(outer_mode, mode_join))
        }
        ExprX::Ctor(path, variant, binders, update) => {
            let datatype = &typing.datatypes[path].clone();
            let variant = datatype.x.get_variant(variant);
            let mut mode = mode_join(outer_mode, datatype.x.mode);
            if let Some(update) = update {
                mode = mode_join(mode, check_expr(typing, outer_mode, update)?);
            }
            for arg in binders.iter() {
                let (_, field_mode) = get_field(&variant.a, &arg.name).a;
                let mode_arg = check_expr(typing, mode_join(outer_mode, field_mode), &arg.a)?;
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
        ExprX::Unary(_, e1) => check_expr(typing, outer_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::Box(_), e1) => check_expr(typing, outer_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::Unbox(_), e1) => check_expr(typing, outer_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::HasType(_), _) => panic!("internal error: HasType in modes.rs"),
        ExprX::UnaryOpr(UnaryOpr::IsVariant { .. }, e1) => check_expr(typing, outer_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::TupleField { .. }, e1) => check_expr(typing, outer_mode, e1),
        ExprX::UnaryOpr(UnaryOpr::Field { datatype, variant, field }, e1) => {
            let e1_mode = check_expr(typing, outer_mode, e1)?;
            let datatype = &typing.datatypes[datatype];
            let field = get_field(&datatype.x.get_variant(variant).a, field);
            Ok(mode_join(e1_mode, field.a.1))
        }
        ExprX::Binary(op, e1, e2) => {
            let op_mode = match op {
                BinaryOp::Eq(mode) => *mode,
                _ => Mode::Exec,
            };
            let outer_mode = match op {
                // because Implies isn't compiled, make it spec-only
                BinaryOp::Implies => mode_join(outer_mode, Mode::Spec),
                _ => outer_mode,
            };
            let mode1 = check_expr(typing, outer_mode, e1)?;
            let mode2 = check_expr(typing, outer_mode, e2)?;
            Ok(mode_join(op_mode, mode_join(mode1, mode2)))
        }
        ExprX::Quant(_, binders, e1) => {
            typing.vars.push_scope(true);
            for binder in binders.iter() {
                typing.insert(&expr.span, &binder.name, false, Mode::Spec);
            }
            check_expr_has_mode(typing, Mode::Spec, e1, Mode::Spec)?;
            typing.vars.pop_scope();
            Ok(Mode::Spec)
        }
        ExprX::Closure(params, body) => {
            // Note: captures and call are not filled in at this point (ast_simplify sets them),
            // so there's no need to check them here.
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
        ExprX::Choose(binder, e1) => {
            typing.vars.push_scope(true);
            typing.insert(&expr.span, &binder.name, false, Mode::Spec);
            check_expr_has_mode(typing, Mode::Spec, e1, Mode::Spec)?;
            typing.vars.pop_scope();
            Ok(Mode::Spec)
        }
        ExprX::Assign(lhs, rhs) => {
            if typing.in_forall_stmt {
                return err_str(&expr.span, "assignment is not allowed in forall statements");
            }
            match &lhs.x {
                // TODO when we support field updates, make sure we handle 'unforgeable' types
                // correctly.
                ExprX::Var(x) => {
                    let (x_mut, x_mode) = typing.get(x);
                    if !x_mut {
                        return err_str(
                            &expr.span,
                            "variable must be declared 'mut' to allow assignment",
                        );
                    }
                    typing.erasure_modes.var_modes.push((lhs.span.clone(), x_mode));

                    check_expr_has_mode(typing, outer_mode, rhs, x_mode)?;
                    Ok(x_mode)
                }
                _ => panic!("expected var, found {:?}", &lhs),
            }
        }
        ExprX::Fuel(_, _) => Ok(outer_mode),
        ExprX::Header(_) => panic!("internal error: Header shouldn't exist here"),
        ExprX::Admit => Ok(outer_mode),
        ExprX::Forall { vars, require, ensure, proof } => {
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
        ExprX::AssertBV(e) => {
            check_expr_has_mode(typing, Mode::Spec, e, Mode::Spec)?;
            Ok(Mode::Proof)
        }
        ExprX::If(e1, e2, e3) => {
            let mode1 = check_expr(typing, outer_mode, e1)?;
            typing.erasure_modes.condition_modes.push((expr.span.clone(), mode1));
            let mode_branch = match (outer_mode, mode1) {
                (Mode::Exec, Mode::Spec) => Mode::Proof,
                _ => outer_mode,
            };
            let mode2 = check_expr(typing, mode_branch, e2)?;
            match e3 {
                None => Ok(mode2),
                Some(e3) => {
                    let mode3 = check_expr(typing, mode_branch, e3)?;
                    Ok(mode_join(mode2, mode3))
                }
            }
        }
        ExprX::Match(e1, arms) => {
            let mode1 = check_expr(typing, outer_mode, e1)?;
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
                let guard_mode = check_expr(typing, arm_outer_mode, &arm.x.guard)?;
                let arm_outer_mode = match (arm_outer_mode, guard_mode) {
                    (Mode::Exec, Mode::Spec | Mode::Proof) => Mode::Proof,
                    (m, _) => m,
                };
                let arm_mode = check_expr(typing, arm_outer_mode, &arm.x.body)?;
                final_mode = mode_join(final_mode, arm_mode);
                typing.vars.pop_scope();
            }
            Ok(final_mode)
        }
        ExprX::While { cond, body, invs } => {
            // We could also allow this for proof, if we check it for termination
            match &mut typing.atomic_insts {
                None => {}
                Some(ai) => ai.add_loop(&expr.span),
            }
            check_expr_has_mode(typing, outer_mode, cond, Mode::Exec)?;
            check_expr_has_mode(typing, outer_mode, body, Mode::Exec)?;
            for inv in invs.iter() {
                check_expr_has_mode(typing, Mode::Spec, inv, Mode::Spec)?;
            }
            Ok(Mode::Exec)
        }
        ExprX::Return(e1) => {
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
        ExprX::Block(ss, e1) => {
            for stmt in ss.iter() {
                typing.vars.push_scope(true);
                check_stmt(typing, outer_mode, stmt)?;
            }
            let mode = match e1 {
                None => outer_mode,
                Some(expr) => check_expr(typing, outer_mode, expr)?,
            };
            for _ in ss.iter() {
                typing.vars.pop_scope();
            }
            Ok(mode)
        }
        ExprX::OpenInvariant(inv, binder, body) => {
            if outer_mode == Mode::Spec {
                return err_string(&expr.span, format!("Cannot open invariant in Spec mode."));
            }
            let mode1 = check_expr(typing, outer_mode, inv)?;
            if mode1 != Mode::Proof {
                return err_string(&inv.span, format!("Invariant must be Proof mode."));
            }
            typing.vars.push_scope(true);
            typing.insert(&expr.span, &binder.name, /* mutable */ true, Mode::Proof);

            if typing.atomic_insts.is_some() || outer_mode != Mode::Exec {
                // If we're a nested atomic block, we don't need to create a new
                // AtomicInstCollector. We just rely on the outer one.
                // Also, if we're already in Proof mode, then we just recurse in Proof
                // mode, and we don't need to do the atomicity check at all.
                let _ = check_expr(typing, outer_mode, body)?;
            } else {
                let mut my_atomic_insts = Some(AtomicInstCollector::new());
                swap(&mut my_atomic_insts, &mut typing.atomic_insts);
                let _ = check_expr(typing, outer_mode, body)?;
                swap(&mut my_atomic_insts, &mut typing.atomic_insts);
                my_atomic_insts.expect("my_atomic_insts").validate(&body.span)?;
            }

            typing.vars.pop_scope();
            Ok(Mode::Exec)
        }
    }
}

fn check_stmt(typing: &mut Typing, outer_mode: Mode, stmt: &Stmt) -> Result<(), VirErr> {
    match &stmt.x {
        StmtX::Expr(e) => {
            let _ = check_expr(typing, outer_mode, e)?;
            Ok(())
        }
        StmtX::Decl { pattern, mode, init } => {
            if !mode_le(outer_mode, *mode) {
                return err_string(&stmt.span, format!("pattern cannot have mode {}", *mode));
            }
            add_pattern(typing, *mode, pattern)?;
            match init.as_ref() {
                None => {}
                Some(expr) => {
                    check_expr_has_mode(typing, outer_mode, expr, *mode)?;
                }
            }
            Ok(())
        }
    }
}

fn check_function(typing: &mut Typing, function: &Function) -> Result<(), VirErr> {
    typing.vars.push_scope(true);
    for param in function.x.params.iter() {
        if !mode_le(function.x.mode, param.x.mode) {
            return err_string(
                &function.span,
                format!("parameter {} cannot have mode {}", param.x.name, param.x.mode),
            );
        }
        typing.insert(&function.span, &param.x.name, param.x.is_mut, param.x.mode);
    }
    if function.x.has_return() {
        let ret_mode = function.x.ret.x.mode;
        if !mode_le(function.x.mode, ret_mode) {
            return err_string(
                &function.span,
                format!("return type cannot have mode {}", ret_mode),
            );
        }
        if function.x.body.is_none() {
            // can't erase return values in external_body functions, so:
            if function.x.mode != ret_mode {
                return err_string(
                    &function.span,
                    format!("because of external_body, return type cannot have mode {}", ret_mode),
                );
            }
        }
        typing.ret_mode = Some(ret_mode);
    }
    if let Some(body) = &function.x.body {
        check_expr_has_mode(typing, function.x.mode, body, function.x.ret.x.mode)?;
    }
    typing.ret_mode = None;
    typing.vars.pop_scope();
    assert_eq!(typing.vars.num_scopes(), 0);
    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<ErasureModes, VirErr> {
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
        vars: ScopeMap::new(),
        erasure_modes,
        in_forall_stmt: false,
        ret_mode: None,
        atomic_insts: None,
    };
    for function in krate.functions.iter() {
        check_function(&mut typing, function)?;
    }
    Ok(typing.erasure_modes)
}
