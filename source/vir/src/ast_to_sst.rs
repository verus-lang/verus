use crate::ast::{BinaryOp, Constant, Expr, ExprX, Ident, Mode, Stmt, StmtX, Typs, VirErr};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{BndX, Dest, Exp, ExpX, Exps, Stm, StmX};
use crate::util::vec_map_result;
use air::ast::BinderX;
use std::rc::Rc;

fn function_can_be_exp(ctx: &Ctx, name: &Ident) -> bool {
    let func = &ctx.func_map[name];
    match func.x.mode {
        Mode::Spec => true,
        Mode::Exec | Mode::Proof => false,
    }
}

// If the Expr is a call that must be a Stm (not an Exp), return it
fn expr_must_be_call_stm(ctx: &Ctx, expr: &Expr) -> Result<Option<(Ident, Typs, Exps)>, VirErr> {
    match &expr.x {
        ExprX::Call(x, typs, args) if !function_can_be_exp(ctx, x) => {
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Some((x.clone(), typs.clone(), Rc::new(exps))))
        }
        _ => Ok(None),
    }
}

pub(crate) fn constant_to_sst_constant(
    _ctx: &Ctx,
    constant: &Constant,
) -> Result<crate::sst::Constant, VirErr> {
    Ok(match constant {
        Constant::Bool(b) => crate::sst::Constant::Bool(*b),
        Constant::Nat(n) => crate::sst::Constant::Nat(n.clone()),
    })
}

pub(crate) fn expr_to_exp(ctx: &Ctx, expr: &Expr) -> Result<Exp, VirErr> {
    match &expr.x {
        ExprX::Const(c) => {
            Ok(Spanned::new(expr.span.clone(), ExpX::Const(constant_to_sst_constant(ctx, c)?)))
        }
        ExprX::Var(x) => Ok(Spanned::new(expr.span.clone(), ExpX::Var(x.clone()))),
        ExprX::Call(x, typs, args) => {
            match ctx.func_map.get(x) {
                None => {
                    return err_string(&expr.span, format!("could not find function {}", &x));
                }
                Some(fun) => match fun.x.mode {
                    Mode::Spec => {}
                    _ => {
                        unimplemented!("call to non-spec function {} {:?}", &x, expr.span)
                    }
                },
            }
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Spanned::new(expr.span.clone(), ExpX::Call(x.clone(), typs.clone(), Rc::new(exps))))
        }
        ExprX::Ctor(p, i, binders) => Ok(Spanned::new(
            expr.span.clone(),
            ExpX::Ctor(
                p.clone(),
                i.clone(),
                Rc::new(
                    binders
                        .iter()
                        .map(|b| b.map_result(|a| expr_to_exp(ctx, a)))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
            ),
        )),
        ExprX::Unary(op, expr) => {
            Ok(Spanned::new(expr.span.clone(), ExpX::Unary(*op, expr_to_exp(ctx, expr)?)))
        }
        ExprX::UnaryOpr(op, expr) => {
            Ok(Spanned::new(expr.span.clone(), ExpX::UnaryOpr(op.clone(), expr_to_exp(ctx, expr)?)))
        }
        ExprX::Binary(op, lhs, rhs) => {
            let bin = ExpX::Binary(*op, expr_to_exp(ctx, lhs)?, expr_to_exp(ctx, rhs)?);
            Ok(Spanned::new(expr.span.clone(), bin))
        }
        ExprX::Quant(quant, binders, body) => {
            let exp = expr_to_exp(ctx, body)?;
            let vars: Vec<Ident> = binders.iter().map(|b| b.name.clone()).collect();
            let trigs = crate::triggers::build_triggers(ctx, &expr.span, &vars, &exp)?;
            let bnd = Spanned::new(body.span.clone(), BndX::Quant(*quant, binders.clone(), trigs));
            Ok(Spanned::new(expr.span.clone(), ExpX::Bind(bnd, exp)))
        }
        ExprX::If(cond, lhs, Some(rhs)) => Ok(Spanned::new(
            expr.span.clone(),
            ExpX::If(expr_to_exp(ctx, cond)?, expr_to_exp(ctx, lhs)?, expr_to_exp(ctx, rhs)?),
        )),
        ExprX::Block(stmts, Some(body)) => {
            let mut exp = expr_to_exp(ctx, body)?;
            for stmt in stmts.iter().rev() {
                match &stmt.x {
                    StmtX::Decl { param, mutable: false, init: Some(init) } => {
                        let name = param.x.name.clone();
                        let binder = Rc::new(BinderX { name, a: expr_to_exp(ctx, init)? });
                        let binders = Rc::new(vec![binder]);
                        let bnd = Spanned::new(param.span.clone(), BndX::Let(binders));
                        exp = Spanned::new(expr.span.clone(), ExpX::Bind(bnd, exp));
                    }
                    _ => todo!("{:#?}", expr),
                }
            }
            Ok(exp)
        }
        ExprX::Field { lhs, datatype_name, field_name } => Ok(Spanned::new(
            expr.span.clone(),
            ExpX::Field {
                lhs: expr_to_exp(ctx, lhs)?,
                datatype_name: datatype_name.clone(),
                field_name: field_name.clone(),
            },
        )),
        _ => {
            todo!("{:#?}", expr)
        }
    }
}

pub fn expr_to_stm(ctx: &Ctx, expr: &Expr, dest: &Option<Ident>) -> Result<Stm, VirErr> {
    match &expr.x {
        ExprX::Call(x, typs, args) => {
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Spanned::new(
                expr.span.clone(),
                StmX::Call(x.clone(), typs.clone(), Rc::new(exps), None),
            ))
        }
        ExprX::Assign(lhs, rhs) => {
            let dest = expr_to_exp(ctx, lhs)?;
            match (expr_must_be_call_stm(ctx, rhs)?, &dest.x) {
                (Some((func_name, typs, args)), ExpX::Var(var)) => Ok(Spanned::new(
                    expr.span.clone(),
                    StmX::Call(
                        func_name,
                        typs,
                        args,
                        Some(Dest { var: var.clone(), mutable: true }),
                    ),
                )),
                _ => {
                    Ok(Spanned::new(expr.span.clone(), StmX::Assign(dest, expr_to_exp(ctx, rhs)?)))
                }
            }
        }
        ExprX::Fuel(x, fuel) => Ok(Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel))),
        ExprX::Admit => {
            let f = Spanned::new(expr.span.clone(), ExpX::Const(crate::sst::Constant::Bool(false)));
            Ok(Spanned::new(expr.span.clone(), StmX::Assume(f)))
        }
        ExprX::If(cond, lhs, rhs) => {
            let scond = expr_to_exp(ctx, cond)?;
            let slhs = expr_to_stm(ctx, lhs, dest)?;
            let srhs = rhs.as_ref().map(|e| expr_to_stm(ctx, e, dest)).transpose()?;
            Ok(Spanned::new(expr.span.clone(), StmX::If(scond, slhs, srhs)))
        }
        ExprX::While { cond, body, invs } => {
            assert_eq!(*dest, None);
            let cond = expr_to_exp(ctx, cond)?;
            let body = expr_to_stm(ctx, body, &None)?;
            let invs = Rc::new(vec_map_result(invs, |e| expr_to_exp(ctx, e))?);
            Ok(Spanned::new(
                expr.span.clone(),
                StmX::While {
                    cond,
                    body,
                    invs,
                    typ_inv_vars: Rc::new(vec![]),
                    modified_vars: Rc::new(vec![]),
                },
            ))
        }
        ExprX::Block(stmts, expr_opt) => {
            let stms_vec = vec_map_result(stmts, |s| stmt_to_stm(ctx, s))?;
            let mut stms: Vec<Stm> = stms_vec.into_iter().flatten().collect();
            match (dest, expr_opt) {
                (None, None) => {}
                (None, Some(expr)) => {
                    stms.push(expr_to_stm(ctx, expr, &None)?);
                }
                (Some(dest), Some(expr)) => {
                    let _ = expr_to_exp(ctx, expr);
                    let x_dest = Spanned::new(expr.span.clone(), ExpX::Var(dest.clone()));
                    let eq = ExpX::Binary(BinaryOp::Eq, x_dest, expr_to_exp(ctx, expr)?);
                    let assign = StmX::Assume(Spanned::new(expr.span.clone(), eq));
                    stms.push(Spanned::new(expr.span.clone(), assign));
                }
                _ => panic!("internal error: ExprX::Block {:?} {}", dest, expr.span.as_string),
            }
            Ok(Spanned::new(expr.span.clone(), StmX::Block(Rc::new(stms))))
        }
        _ => {
            todo!("{}", expr.span.as_string)
        }
    }
}

pub fn stmt_to_stm(ctx: &Ctx, stmt: &Stmt) -> Result<Vec<Stm>, VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => Ok(vec![expr_to_stm(ctx, &expr, &None)?]),
        StmtX::Decl { param, mutable, init } => {
            let decl = Spanned::new(
                stmt.span.clone(),
                StmX::Decl {
                    ident: param.x.name.clone(),
                    typ: param.x.typ.clone(),
                    mutable: *mutable,
                    init: matches!(init, Some(_)),
                },
            );
            let mut stms = vec![decl];
            match (*mutable, init) {
                (false, None) => {
                    // We don't yet support Assign to non-mutable
                    return err_str(&stmt.span, "non-mut variable must have an initializer");
                }
                (true, None) => {}
                (_, Some(init)) => {
                    let span = &init.span;
                    let var = Spanned::new(span.clone(), ExpX::Var(param.x.name.clone()));
                    match &expr_must_be_call_stm(ctx, init)? {
                        None => {
                            let rhs = expr_to_exp(ctx, init)?;
                            let eq =
                                Spanned::new(span.clone(), ExpX::Binary(BinaryOp::Eq, var, rhs));
                            stms.push(Spanned::new(span.clone(), StmX::Assume(eq)));
                        }
                        Some((func_name, typs, args)) => {
                            let dest = Some(Dest { var: param.x.name.clone(), mutable: *mutable });
                            let call =
                                StmX::Call(func_name.clone(), typs.clone(), args.clone(), dest);
                            stms.push(Spanned::new(span.clone(), call));
                        }
                    }
                }
            }
            Ok(stms)
        }
    }
}
