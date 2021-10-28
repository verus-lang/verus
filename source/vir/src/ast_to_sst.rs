use crate::ast::{
    BinaryOp, Constant, Expr, ExprX, Function, Ident, Mode, ParamX, Path, Pattern, PatternX,
    SpannedTyped, Stmt, StmtX, Typ, TypX, Typs, UnaryOp, UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Dest, Exp, ExpX, LocalDecl, LocalDeclX, Stm, StmX};
use crate::util::{vec_map, vec_map_result};
use air::ast::{Binder, BinderX, Span};
use std::sync::Arc;

type Arg = (Exp, Typ);
type Args = Arc<Vec<Arg>>;

pub(crate) struct State {
    next_var: u64,
    pub(crate) local_decls: Vec<LocalDecl>,
}

impl State {
    pub fn new() -> Self {
        State { next_var: 0, local_decls: Vec::new() }
    }

    fn next_temp(&mut self) -> Ident {
        self.next_var += 1;
        crate::def::prefix_temp_var(self.next_var)
    }

    fn declare_var(&mut self, ident: &Ident, typ: &Typ, mutable: bool) {
        let decl = LocalDeclX { ident: ident.clone(), typ: typ.clone(), mutable };
        self.local_decls.push(Arc::new(decl));
    }
}

fn init_var(span: &Span, x: &Ident, exp: &Exp) -> Stm {
    Spanned::new(span.clone(), StmX::Assign { lhs: x.clone(), rhs: exp.clone(), is_init: true })
}

fn get_function(ctx: &Ctx, expr: &Expr, name: &Path) -> Result<Function, VirErr> {
    match ctx.func_map.get(name) {
        None => err_string(&expr.span, format!("could not find function {:?}", &name)),
        Some(func) => Ok(func.clone()),
    }
}

fn function_can_be_exp(ctx: &Ctx, expr: &Expr, path: &Path) -> Result<bool, VirErr> {
    match get_function(ctx, expr, path)?.x.mode {
        Mode::Spec => Ok(true),
        Mode::Proof | Mode::Exec => Ok(false),
    }
}

fn expr_get_call(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, Path, Typs, bool, Args)>, VirErr> {
    match &expr.x {
        ExprX::Call(x, typs, args) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut exps: Vec<Arg> = Vec::new();
            for arg in args.iter() {
                let (mut stms0, e0) = expr_to_stm(ctx, state, arg)?;
                stms.append(&mut stms0);
                exps.push((e0, arg.typ.clone()));
            }
            let has_ret = !get_function(ctx, expr, x)?.x.ret.is_none();
            Ok(Some((stms, x.clone(), typs.clone(), has_ret, Arc::new(exps))))
        }
        _ => Ok(None),
    }
}

// If the Expr is a call that must be a Stm (not an Exp), return it
fn expr_must_be_call_stm(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, Path, Typs, bool, Args)>, VirErr> {
    match &expr.x {
        ExprX::Call(x, _, _) if !function_can_be_exp(ctx, expr, x)? => {
            expr_get_call(ctx, state, expr)
        }
        _ => Ok(None),
    }
}

pub(crate) fn expr_to_exp_state(ctx: &Ctx, state: &mut State, expr: &Expr) -> Result<Exp, VirErr> {
    let (stms, exp) = expr_to_stm(ctx, state, expr)?;
    if stms.len() == 0 {
        Ok(exp)
    } else {
        err_str(&expr.span, "expected pure mathematical expression")
    }
}

pub(crate) fn expr_to_exp(ctx: &Ctx, expr: &Expr) -> Result<Exp, VirErr> {
    let mut state = State::new();
    expr_to_exp_state(ctx, &mut state, expr)
}

pub(crate) fn expr_to_stm(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Exp), VirErr> {
    let (stms, exp_opt) = expr_to_stm_opt(ctx, state, expr)?;
    Ok((stms, exp_opt.expect("expr_to_stm")))
}

pub(crate) fn stms_to_one_stm(span: &Span, stms: Vec<Stm>) -> Stm {
    if stms.len() == 1 {
        stms[0].clone()
    } else {
        Spanned::new(span.clone(), StmX::Block(Arc::new(stms)))
    }
}

fn check_no_exp(exp: &Option<Exp>) -> Result<(), VirErr> {
    match exp {
        None => Ok(()),
        Some(exp) => match &exp.x {
            ExpX::Var(x) if crate::def::is_temp_var(x) => Ok(()),
            // REVIEW: we could lift this restriction by putting exp into a dummy VIR node:
            // (we can't just drop it; the erasure depends on information from VIR)
            _ => err_str(&exp.span, "expressions with no effect are not supported"),
        },
    }
}

pub(crate) fn expr_to_one_stm(ctx: &Ctx, state: &mut State, expr: &Expr) -> Result<Stm, VirErr> {
    let (stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
    check_no_exp(&exp)?;
    Ok(stms_to_one_stm(&expr.span, stms))
}

pub(crate) fn expr_to_one_stm_dest(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
    dest: &Option<Ident>,
) -> Result<Stm, VirErr> {
    let (mut stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
    match (dest, exp) {
        (None, _) => {}
        (Some(_), None) => {
            panic!("internal error: missing return value")
        }
        (Some(dest), Some(exp)) => {
            stms.push(init_var(&expr.span, dest, &exp));
        }
    }
    Ok(stms_to_one_stm(&expr.span, stms))
}

fn is_small_expr(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Const(_) => true,
        ExprX::Var(_) => true,
        ExprX::Unary(UnaryOp::Not | UnaryOp::Clip(_), e) => is_small_expr(e),
        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_expr(e),
        _ => false,
    }
}

fn is_small_exp(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Const(_) => true,
        ExpX::Var(_) => true,
        ExpX::Old(_, _) => true,
        ExpX::Unary(UnaryOp::Not | UnaryOp::Clip(_), e) => is_small_exp(e),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_exp(e),
        _ => false,
    }
}

fn stm_call(
    state: &mut State,
    span: &Span,
    path: Path,
    typs: Typs,
    args: Args,
    dest: Option<Dest>,
) -> Stm {
    let mut small_args: Vec<Exp> = Vec::new();
    let mut stms: Vec<Stm> = Vec::new();
    for arg in args.iter() {
        if is_small_exp(&arg.0) {
            small_args.push(arg.0.clone());
        } else {
            // To avoid copying arg in preconditions and postconditions,
            // put arg into a temporary variable
            let temp = state.next_temp();
            small_args.push(Spanned::new(arg.0.span.clone(), ExpX::Var(temp.clone())));
            state.declare_var(&temp, &arg.1, false);
            stms.push(init_var(&arg.0.span, &temp, &arg.0));
        }
    }
    let call = StmX::Call(path, typs, Arc::new(small_args), dest);
    stms.push(Spanned::new(span.clone(), call));
    stms_to_one_stm(span, stms)
}

fn datatype_field_typ(ctx: &Ctx, path: &Path, variant: &Ident, field: &Ident) -> Typ {
    let fields =
        &ctx.datatypes[path].iter().find(|v| v.name == *variant).expect("couldn't find variant").a;
    let (typ, _) = &fields.iter().find(|f| f.name == *field).expect("couldn't find field").a;
    typ.clone()
}

// Compute:
// - expression that tests whether exp matches pattern
// - bindings of pattern variables to fields of exp
fn pattern_to_exprs(ctx: &Ctx, expr: &Expr, pattern: &Pattern, decls: &mut Vec<Stmt>) -> Expr {
    let t_bool = Arc::new(TypX::Bool);
    match &pattern.x {
        PatternX::Wildcard => {
            SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true)))
        }
        PatternX::Var(x) => {
            let paramx = ParamX { name: x.clone(), typ: expr.typ.clone(), mode: Mode::Exec };
            let param = Spanned::new(expr.span.clone(), paramx);
            let decl = StmtX::Decl { param, mutable: false, init: Some(expr.clone()) };
            decls.push(Spanned::new(expr.span.clone(), decl));
            SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true)))
        }
        PatternX::Constructor(path, variant, patterns) => {
            let is_variant_opr =
                UnaryOpr::IsVariant { datatype: path.clone(), variant: variant.clone() };
            let test_variant = ExprX::UnaryOpr(is_variant_opr, expr.clone());
            let mut test = SpannedTyped::new(&pattern.span, &t_bool, test_variant);
            for binder in patterns.iter() {
                let field_op = UnaryOpr::Field {
                    datatype: path.clone(),
                    variant: variant.clone(),
                    field: binder.name.clone(),
                };
                let field = ExprX::UnaryOpr(field_op, expr.clone());
                let field_typ = datatype_field_typ(ctx, path, variant, &binder.name);
                let field_exp = SpannedTyped::new(&pattern.span, &field_typ, field);
                let field_exp = match (&*field_typ, &*binder.a.typ) {
                    (TypX::TypParam(_), TypX::TypParam(_)) => field_exp,
                    (TypX::TypParam(_), TypX::Boxed(_)) => field_exp,
                    (TypX::TypParam(_), _) => {
                        let op = UnaryOpr::Unbox(binder.a.typ.clone());
                        let unbox = ExprX::UnaryOpr(op, field_exp);
                        SpannedTyped::new(&pattern.span, &binder.a.typ, unbox)
                    }
                    _ => field_exp,
                };
                let pattern_test = pattern_to_exprs(ctx, &field_exp, &binder.a, decls);
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }
            test
        }
    }
}

fn if_to_stm(
    state: &mut State,
    expr: &Expr,
    stms0: &mut Vec<Stm>,
    e0: Exp,
    mut stms1: Vec<Stm>,
    e1: &Exp,
    mut stms2: Vec<Stm>,
    e2: &Exp,
) -> Exp {
    // If statement, put results from e1/e2 in a temp variable, return temp variable
    let temp = state.next_temp();
    state.declare_var(&temp, &expr.typ, false);
    // if e0 { stms1; temp = e1; } else { stms2; temp = e2; }
    stms1.push(init_var(&expr.span, &temp, &e1));
    stms2.push(init_var(&expr.span, &temp, &e2));
    let stm1 = stms_to_one_stm(&expr.span, stms1);
    let stm2 = stms_to_one_stm(&expr.span, stms2);
    let if_stmt = StmX::If(e0, stm1, Some(stm2));
    stms0.push(Spanned::new(expr.span.clone(), if_stmt));
    // temp
    Spanned::new(expr.span.clone(), ExpX::Var(temp))
}

pub(crate) fn expr_to_stm_opt(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Option<Exp>), VirErr> {
    match &expr.x {
        ExprX::Const(c) => {
            Ok((vec![], Some(Spanned::new(expr.span.clone(), ExpX::Const(c.clone())))))
        }
        ExprX::Var(x) => Ok((vec![], Some(Spanned::new(expr.span.clone(), ExpX::Var(x.clone()))))),
        ExprX::Assign(expr1, expr2) => {
            let dest_x = match &expr1.x {
                ExprX::Var(x) => Ok(x.clone()),
                _ => err_str(&expr1.span, "complex assignments not yet supported"),
            };
            match expr_must_be_call_stm(ctx, state, expr2)? {
                Some((mut stms2, func_path, typs, _, args)) => {
                    // make a Call
                    let dest = Dest { var: dest_x?.clone(), is_init: false };
                    stms2.push(stm_call(state, &expr.span, func_path, typs, args, Some(dest)));
                    Ok((stms2, None))
                }
                None => {
                    // make an Assign
                    let (mut stms2, e2) = expr_to_stm(ctx, state, expr2)?;
                    let assign = StmX::Assign { lhs: dest_x?, rhs: e2, is_init: false };
                    stms2.push(Spanned::new(expr.span.clone(), assign));
                    Ok((stms2, None))
                }
            }
        }
        ExprX::Call(_, _, _) => {
            let (mut stms, x, typs, ret, args) = expr_get_call(ctx, state, expr)?.expect("Call");
            if function_can_be_exp(ctx, expr, &x)? {
                // ExpX::Call
                let args = Arc::new(vec_map(&args, |(a, _)| a.clone()));
                let call = ExpX::Call(false, x.clone(), typs.clone(), args);
                Ok((stms, Some(Spanned::new(expr.span.clone(), call))))
            } else if ret {
                let temp = state.next_temp();
                state.declare_var(&temp, &expr.typ, false);
                // tmp = StmX::Call;
                let dest = Dest { var: temp.clone(), is_init: true };
                stms.push(stm_call(state, &expr.span, x.clone(), typs.clone(), args, Some(dest)));
                // tmp
                Ok((stms, Some(Spanned::new(expr.span.clone(), ExpX::Var(temp)))))
            } else {
                // StmX::Call
                stms.push(stm_call(state, &expr.span, x.clone(), typs.clone(), args, None));
                Ok((stms, None))
            }
        }
        ExprX::Ctor(p, i, binders) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut args: Vec<Binder<Exp>> = Vec::new();
            for binder in binders.iter() {
                let (mut stms1, e1) = expr_to_stm(ctx, state, &binder.a)?;
                stms.append(&mut stms1);
                let arg = BinderX { name: binder.name.clone(), a: e1 };
                args.push(Arc::new(arg));
            }
            let ctor = ExpX::Ctor(p.clone(), i.clone(), Arc::new(args));
            Ok((stms, Some(Spanned::new(expr.span.clone(), ctor))))
        }
        ExprX::Unary(op, expr) => {
            let (stms, exp) = expr_to_stm(ctx, state, expr)?;
            Ok((stms, Some(Spanned::new(expr.span.clone(), ExpX::Unary(*op, exp)))))
        }
        ExprX::UnaryOpr(op, expr) => {
            let (stms, exp) = expr_to_stm(ctx, state, expr)?;
            Ok((stms, Some(Spanned::new(expr.span.clone(), ExpX::UnaryOpr(op.clone(), exp)))))
        }
        ExprX::Binary(op, e1, e2) => {
            let short_circuit = match op {
                BinaryOp::And => Some((true, false)),
                BinaryOp::Implies => Some((true, true)),
                BinaryOp::Or => Some((false, true)),
                _ => None,
            };
            let (mut stms1, e1) = expr_to_stm(ctx, state, e1)?;
            let (mut stms2, e2) = expr_to_stm(ctx, state, e2)?;
            let bin = match (short_circuit, stms2.len()) {
                (Some((proceed_on, other)), n) if n > 0 => {
                    // and:
                    //   if e1 { stmts2; e2 } else { false }
                    // implies:
                    //   if e1 { stmts2; e2 } else { true }
                    // or:
                    //   if e1 { true } else { stmts2; e2 }
                    let bx = ExpX::Const(Constant::Bool(other));
                    let b = Spanned::new(expr.span.clone(), bx);
                    if proceed_on {
                        let temp_var =
                            if_to_stm(state, expr, &mut stms1, e1, stms2, &e2, vec![], &b);
                        temp_var
                    } else {
                        let temp_var =
                            if_to_stm(state, expr, &mut stms1, e1, vec![], &b, stms2, &e2);
                        temp_var
                    }
                }
                _ => {
                    stms1.append(&mut stms2);
                    Spanned::new(expr.span.clone(), ExpX::Binary(*op, e1, e2))
                }
            };
            Ok((stms1, Some(bin)))
        }
        ExprX::Quant(quant, binders, body) => {
            let exp = expr_to_exp_state(ctx, state, body)?;
            let vars: Vec<Ident> = binders.iter().map(|b| b.name.clone()).collect();
            let trigs = crate::triggers::build_triggers(ctx, &expr.span, &vars, &exp)?;
            let bnd = Spanned::new(body.span.clone(), BndX::Quant(*quant, binders.clone(), trigs));
            Ok((vec![], Some(Spanned::new(expr.span.clone(), ExpX::Bind(bnd, exp)))))
        }
        ExprX::If(e0, e1, None) => {
            let (mut stms0, e0) = expr_to_stm(ctx, state, e0)?;
            let stms1 = expr_to_one_stm(ctx, state, e1)?;
            stms0.push(Spanned::new(expr.span.clone(), StmX::If(e0, stms1, None)));
            Ok((stms0, None))
        }
        ExprX::If(expr0, expr1, Some(expr2)) => {
            let (mut stms0, e0) = expr_to_stm(ctx, state, expr0)?;
            let (stms1, e1) = expr_to_stm_opt(ctx, state, expr1)?;
            let (stms2, e2) = expr_to_stm_opt(ctx, state, expr2)?;
            match (e1, e2) {
                (Some(e1), Some(e2)) if stms1.len() == 0 && stms2.len() == 0 => {
                    // If expression
                    Ok((stms0, Some(Spanned::new(expr.span.clone(), ExpX::If(e0, e1, e2)))))
                }
                (Some(e1), Some(e2)) => {
                    // If statement, put results from e1/e2 in a temp variable, return temp variable
                    let temp_var = if_to_stm(state, expr, &mut stms0, e0, stms1, &e1, stms2, &e2);
                    Ok((stms0, Some(temp_var)))
                }
                _ => {
                    // If statement, let expression be None
                    let stm1 = stms_to_one_stm(&expr1.span, stms1);
                    let stm2 = stms_to_one_stm(&expr2.span, stms2);
                    stms0.push(Spanned::new(expr.span.clone(), StmX::If(e0, stm1, Some(stm2))));
                    Ok((stms0, None))
                }
            }
        }
        ExprX::Match(expr0, arms1) => {
            let mut temp_decl: Option<Stmt> = None;
            let expr0 = if is_small_expr(&expr0) {
                expr0.clone()
            } else {
                // put expr0 into a temp variable to avoid duplicating it
                let temp = state.next_temp();
                let name = temp.clone();
                let paramx = ParamX { name, typ: expr0.typ.clone(), mode: Mode::Exec };
                let param = Spanned::new(expr0.span.clone(), paramx);
                let decl = StmtX::Decl { param, mutable: false, init: Some(expr0.clone()) };
                temp_decl = Some(Spanned::new(expr0.span.clone(), decl));
                SpannedTyped::new(&expr0.span, &expr0.typ, ExprX::Var(temp))
            };
            // Translate into If expression
            let t_bool = Arc::new(TypX::Bool);
            let mut if_expr: Option<Expr> = None;
            for arm in arms1.iter().rev() {
                let mut decls: Vec<Stmt> = Vec::new();
                let test_pattern = pattern_to_exprs(ctx, &expr0, &arm.x.pattern, &mut decls);
                let test = match &arm.x.guard.x {
                    ExprX::Const(Constant::Bool(true)) => test_pattern,
                    _ => {
                        let guard = arm.x.guard.clone();
                        let test_exp = ExprX::Binary(BinaryOp::And, test_pattern, guard);
                        let test = SpannedTyped::new(&arm.x.pattern.span, &t_bool, test_exp);
                        let block = ExprX::Block(Arc::new(decls.clone()), Some(test));
                        SpannedTyped::new(&arm.x.pattern.span, &t_bool, block)
                    }
                };
                let block = ExprX::Block(Arc::new(decls), Some(arm.x.body.clone()));
                let body = SpannedTyped::new(&arm.x.pattern.span, &t_bool, block);
                if let Some(prev) = if_expr {
                    // if pattern && guard then body else prev
                    let ifx = ExprX::If(test.clone(), body, Some(prev));
                    if_expr = Some(SpannedTyped::new(&test.span, &expr.typ.clone(), ifx));
                } else {
                    // last arm is unconditional
                    if_expr = Some(body);
                }
            }
            if let Some(if_expr) = if_expr {
                let if_expr = if let Some(decl) = temp_decl {
                    let block = ExprX::Block(Arc::new(vec![decl]), Some(if_expr));
                    SpannedTyped::new(&expr.span, &expr.typ, block)
                } else {
                    if_expr
                };
                expr_to_stm_opt(ctx, state, &if_expr)
            } else {
                err_str(&expr.span, "not yet implemented: zero-arm match expressions")
            }
        }
        ExprX::While { cond, body, invs } => {
            let (stms0, e0) = expr_to_stm(ctx, state, cond)?;
            if stms0.len() != 0 {
                // TODO:
                return err_str(&cond.span, "not yet implemented: complex while loop conditions");
            }
            let (stms1, e1) = expr_to_stm_opt(ctx, state, body)?;
            check_no_exp(&e1)?;
            let invs = Arc::new(vec_map_result(invs, |e| expr_to_exp_state(ctx, state, e))?);
            let while_stm = Spanned::new(
                expr.span.clone(),
                StmX::While {
                    cond: e0,
                    body: stms_to_one_stm(&body.span, stms1),
                    invs,
                    typ_inv_vars: Arc::new(vec![]),
                    modified_vars: Arc::new(vec![]),
                },
            );
            Ok((vec![while_stm], None))
        }
        ExprX::Block(stmts, body_opt) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut local_decls: Vec<LocalDecl> = Vec::new();
            let mut binds: Vec<Bnd> = Vec::new();
            let mut is_pure_exp = true;
            for stmt in stmts.iter() {
                let (mut stms0, e0, decl_bnd_opt) = stmt_to_stm(ctx, state, stmt)?;
                match decl_bnd_opt {
                    Some((decl, Some(bnd))) => {
                        local_decls.push(decl);
                        binds.push(bnd);
                    }
                    Some((decl, None)) => {
                        local_decls.push(decl);
                        is_pure_exp = false;
                    }
                    _ => {
                        is_pure_exp = false;
                    }
                }
                check_no_exp(&e0)?;
                stms.append(&mut stms0);
            }
            let exp = if let Some(expr) = body_opt {
                let (mut stms1, exp) = expr_to_stm_opt(ctx, state, expr)?;
                if stms1.len() > 0 {
                    is_pure_exp = false;
                }
                stms.append(&mut stms1);
                exp
            } else {
                None
            };
            match exp {
                Some(mut exp) if is_pure_exp => {
                    // Pure expression: fold decls into Let bindings and return a single expression
                    for bnd in binds.iter().rev() {
                        exp = Spanned::new(expr.span.clone(), ExpX::Bind(bnd.clone(), exp));
                    }
                    return Ok((vec![], Some(exp)));
                }
                _ => {
                    // Not pure: return statements
                    state.local_decls.append(&mut local_decls);
                    let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(stms)));
                    Ok((vec![block], exp))
                }
            }
        }
        ExprX::Fuel(x, fuel) => {
            let stm = Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel));
            Ok((vec![stm], None))
        }
        ExprX::Admit => {
            let exp = Spanned::new(expr.span.clone(), ExpX::Const(Constant::Bool(false)));
            let stm = Spanned::new(expr.span.clone(), StmX::Assume(exp));
            Ok((vec![stm], None))
        }
        _ => {
            todo!("{}", expr.span.as_string)
        }
    }
}

pub(crate) fn stmt_to_stm(
    ctx: &Ctx,
    state: &mut State,
    stmt: &Stmt,
) -> Result<(Vec<Stm>, Option<Exp>, Option<(LocalDecl, Option<Bnd>)>), VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => {
            let (stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
            Ok((stms, exp, None))
        }
        StmtX::Decl { param, mutable, init } => {
            let ident = param.x.name.clone();
            let typ = param.x.typ.clone();
            let decl = Arc::new(LocalDeclX { ident, typ, mutable: *mutable });

            if let Some(init) = init {
                match expr_must_be_call_stm(ctx, state, init)? {
                    Some((mut stms, func_name, typs, _, args)) => {
                        // Special case: convert to a Call
                        let dest = Dest { var: param.x.name.clone(), is_init: true };
                        stms.push(stm_call(state, &init.span, func_name, typs, args, Some(dest)));
                        return Ok((stms, None, Some((decl, None))));
                    }
                    None => {}
                }
            }

            let (mut stms, exp) = match init {
                None => (vec![], None),
                Some(init) => expr_to_stm_opt(ctx, state, init)?,
            };

            // For a pure expression, return a binder
            let bnd = match &exp {
                Some(exp) if stms.len() == 0 => {
                    let binder = BinderX { name: param.x.name.clone(), a: exp.clone() };
                    let bnd = BndX::Let(Arc::new(vec![Arc::new(binder)]));
                    Some(Spanned::new(stmt.span.clone(), bnd))
                }
                _ => None,
            };

            match (*mutable, &exp) {
                (false, None) => {
                    // We don't yet support Assign to non-mutable
                    return err_str(&stmt.span, "non-mut variable must have an initializer");
                }
                (true, None) => {}
                (_, Some(exp)) => {
                    stms.push(init_var(&stmt.span, &param.x.name, exp));
                }
            }

            Ok((stms, None, Some((decl, bnd))))
        }
    }
}
