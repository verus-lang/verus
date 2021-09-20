use crate::ast::{
    BinaryOp, Constant, Expr, ExprX, Function, Ident, Mode, Path, Stmt, StmtX, Typs, VirErr,
};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Dest, Exp, ExpX, Exps, Stm, StmX};
use crate::util::vec_map_result;
use air::ast::{Binder, BinderX, Span};
use std::sync::Arc;

pub struct State {
    next_var: u64,
}

impl State {
    pub fn new() -> Self {
        State { next_var: 0 }
    }

    fn next_temp(&mut self) -> Ident {
        self.next_var += 1;
        crate::def::prefix_temp_var(self.next_var)
    }
}

fn assume_var(span: &Span, x: &Ident, exp: &Exp) -> Stm {
    let x_var = Spanned::new(span.clone(), ExpX::Var(x.clone()));
    let eq = Spanned::new(span.clone(), ExpX::Binary(BinaryOp::Eq, x_var, exp.clone()));
    Spanned::new(span.clone(), StmX::Assume(eq))
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
) -> Result<Option<(Vec<Stm>, Path, Typs, bool, Exps)>, VirErr> {
    match &expr.x {
        ExprX::Call(x, typs, args) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut exps: Vec<Exp> = Vec::new();
            for arg in args.iter() {
                let (mut stms0, e0) = expr_to_stm(ctx, state, arg)?;
                stms.append(&mut stms0);
                exps.push(e0);
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
) -> Result<Option<(Vec<Stm>, Path, Typs, bool, Exps)>, VirErr> {
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
            ExpX::Var(x) if x.starts_with(crate::def::PREFIX_TEMP_VAR) => Ok(()),
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
            stms.push(assume_var(&expr.span, dest, &exp));
        }
    }
    Ok(stms_to_one_stm(&expr.span, stms))
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
                    let dest = Dest { var: dest_x?.clone(), mutable: true };
                    let call = StmX::Call(func_path, typs, args, Some(dest));
                    stms2.push(Spanned::new(expr.span.clone(), call));
                    Ok((stms2, None))
                }
                None => {
                    // make an Assign
                    let (mut stms2, e2) = expr_to_stm(ctx, state, expr2)?;
                    let dest = Spanned::new(expr1.span.clone(), ExpX::Var(dest_x?));
                    let assign = StmX::Assign(dest, e2);
                    stms2.push(Spanned::new(expr.span.clone(), assign));
                    Ok((stms2, None))
                }
            }
        }
        ExprX::Call(_, _, _) => {
            let (mut stms, x, typs, ret, args) = expr_get_call(ctx, state, expr)?.expect("Call");
            if function_can_be_exp(ctx, expr, &x)? {
                // ExpX::Call
                let call = ExpX::Call(false, x.clone(), typs.clone(), args);
                Ok((stms, Some(Spanned::new(expr.span.clone(), call))))
            } else if ret {
                let temp = state.next_temp();
                // let tmp;
                let typ = expr.typ.clone();
                let ident = temp.clone();
                let temp_decl = StmX::Decl { ident, typ, mutable: false, init: false };
                stms.push(Spanned::new(expr.span.clone(), temp_decl));
                // tmp = StmX::Call;
                let dest = Dest { var: temp.clone(), mutable: false };
                let call = StmX::Call(x.clone(), typs.clone(), args, Some(dest));
                stms.push(Spanned::new(expr.span.clone(), call));
                // tmp
                Ok((stms, Some(Spanned::new(expr.span.clone(), ExpX::Var(temp)))))
            } else {
                // StmX::Call
                let call = StmX::Call(x.clone(), typs.clone(), args, None);
                stms.push(Spanned::new(expr.span.clone(), call));
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
            let (mut stms1, e1) = expr_to_stm(ctx, state, e1)?;
            let (mut stms2, e2) = expr_to_stm(ctx, state, e2)?;
            stms1.append(&mut stms2);
            let bin = ExpX::Binary(*op, e1, e2);
            Ok((stms1, Some(Spanned::new(expr.span.clone(), bin))))
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
            let (mut stms1, e1) = expr_to_stm_opt(ctx, state, expr1)?;
            let (mut stms2, e2) = expr_to_stm_opt(ctx, state, expr2)?;
            match (e1, e2) {
                (Some(e1), Some(e2)) if stms1.len() == 0 && stms2.len() == 0 => {
                    // If expression
                    Ok((stms0, Some(Spanned::new(expr.span.clone(), ExpX::If(e0, e1, e2)))))
                }
                (Some(e1), Some(e2)) => {
                    // If statement, put results from e1/e2 in a temp variable, return temp variable
                    let temp = state.next_temp();
                    // let temp;
                    let typ = expr.typ.clone();
                    let ident = temp.clone();
                    let temp_decl = StmX::Decl { ident, typ, mutable: false, init: false };
                    stms0.push(Spanned::new(expr.span.clone(), temp_decl));
                    // if e0 { stms1; temp = e1; } else { stms2; temp = e2; }
                    stms1.push(assume_var(&expr.span, &temp, &e1));
                    stms2.push(assume_var(&expr.span, &temp, &e2));
                    let stm1 = stms_to_one_stm(&expr.span, stms1);
                    let stm2 = stms_to_one_stm(&expr.span, stms2);
                    let if_stmt = StmX::If(e0, stm1, Some(stm2));
                    stms0.push(Spanned::new(expr.span.clone(), if_stmt));
                    // temp
                    let temp_var = Spanned::new(expr.span.clone(), ExpX::Var(temp));
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
            let mut decls: Vec<Bnd> = Vec::new();
            let mut is_pure_exp = true;
            for stmt in stmts.iter() {
                let (mut stms0, e0, bnd_opt) = stmt_to_stm(ctx, state, stmt)?;
                match bnd_opt {
                    Some(bnd) => {
                        decls.push(bnd);
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
                stms.append(&mut stms1);
                exp
            } else {
                None
            };
            match exp {
                Some(mut exp) if is_pure_exp => {
                    // Pure expression: fold decls into Let bindings and return a single expression
                    for bnd in decls.iter().rev() {
                        exp = Spanned::new(expr.span.clone(), ExpX::Bind(bnd.clone(), exp));
                    }
                    return Ok((vec![], Some(exp)));
                }
                _ => {
                    // Not pure: return statements
                    let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(stms)));
                    Ok((vec![block], exp))
                }
            }
        }
        ExprX::Field { lhs, datatype, field_name } => {
            let (stms, lhs) = expr_to_stm(ctx, state, lhs)?;
            let field =
                ExpX::Field { lhs, datatype: datatype.clone(), field_name: field_name.clone() };
            Ok((stms, Some(Spanned::new(expr.span.clone(), field))))
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

pub fn stmt_to_stm(
    ctx: &Ctx,
    state: &mut State,
    stmt: &Stmt,
) -> Result<(Vec<Stm>, Option<Exp>, Option<Bnd>), VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => {
            let (stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
            Ok((stms, exp, None))
        }
        StmtX::Decl { param, mutable, init } => {
            let ident = param.x.name.clone();
            let typ = param.x.typ.clone();
            let decl = StmX::Decl { ident, typ, mutable: *mutable, init: !init.is_none() };

            if let Some(init) = init {
                match expr_must_be_call_stm(ctx, state, init)? {
                    Some((mut stms, func_name, typs, _, args)) => {
                        // Special case: convert to a Call
                        let dest = Dest { var: param.x.name.clone(), mutable: *mutable };
                        let call = StmX::Call(func_name, typs, args, Some(dest));
                        stms.push(Spanned::new(stmt.span.clone(), decl));
                        stms.push(Spanned::new(init.span.clone(), call));
                        return Ok((stms, None, None));
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

            stms.push(Spanned::new(stmt.span.clone(), decl));

            match (*mutable, &exp) {
                (false, None) => {
                    // We don't yet support Assign to non-mutable
                    return err_str(&stmt.span, "non-mut variable must have an initializer");
                }
                (true, None) => {}
                (_, Some(exp)) => {
                    stms.push(assume_var(&stmt.span, &param.x.name, exp));
                }
            }

            Ok((stms, None, bnd))
        }
    }
}
