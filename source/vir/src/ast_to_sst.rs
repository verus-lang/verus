use crate::ast::{BinaryOp, Expr, ExprX, Ident, Mode, Stmt, StmtX, VirErr};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Dest, Exp, ExpX, Exps, Stm, StmX};
use crate::util::vec_map_result;
use std::rc::Rc;

fn function_can_be_exp(ctx: &Ctx, name: &Ident) -> bool {
    let func = &ctx.func_map[name];
    match func.x.mode {
        Mode::Spec => true,
        Mode::Exec | Mode::Proof => false,
    }
}

// If the Expr is a call that must be a Stm (not an Exp), return it
fn expr_must_be_call_stm(ctx: &Ctx, expr: &Expr) -> Result<Option<(Ident, Exps)>, VirErr> {
    match &expr.x {
        ExprX::Call(x, args) if !function_can_be_exp(ctx, x) => {
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Some((x.clone(), Rc::new(exps))))
        }
        _ => Ok(None),
    }
}

pub(crate) fn expr_to_exp(ctx: &Ctx, expr: &Expr) -> Result<Exp, VirErr> {
    match &expr.x {
        ExprX::Const(c) => Ok(Spanned::new(expr.span.clone(), ExpX::Const(c.clone()))),
        ExprX::Var(x) => Ok(Spanned::new(expr.span.clone(), ExpX::Var(x.clone()))),
        ExprX::Call(x, args) => {
            match ctx.func_map.get(x) {
                None => {
                    return Err(Spanned::new(
                        expr.span.clone(),
                        format!("could not find function {}", &x),
                    ));
                }
                Some(fun) => match fun.x.mode {
                    Mode::Spec => {}
                    _ => {
                        unimplemented!("call to non-spec function {} {:?}", &x, expr.span)
                    }
                },
            }
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Spanned::new(expr.span.clone(), ExpX::Call(x.clone(), Rc::new(exps))))
        }
        ExprX::Unary(op, expr) => {
            Ok(Spanned::new(expr.span.clone(), ExpX::Unary(*op, expr_to_exp(ctx, expr)?)))
        }
        ExprX::Binary(op, lhs, rhs) => {
            let bin = ExpX::Binary(*op, expr_to_exp(ctx, lhs)?, expr_to_exp(ctx, rhs)?);
            Ok(Spanned::new(expr.span.clone(), bin))
        }
        ExprX::Block(stmts, Some(expr)) if stmts.len() == 0 => expr_to_exp(ctx, expr),
        ExprX::Field(lhs, name) => {
            Ok(Spanned::new(expr.span.clone(), ExpX::Field(expr_to_exp(ctx, lhs)?, name.clone())))
        }
        _ => {
            todo!("{:?}", expr)
        }
    }
}

pub fn expr_to_stm(ctx: &Ctx, expr: &Expr, dest: &Option<Ident>) -> Result<Stm, VirErr> {
    match &expr.x {
        ExprX::Call(x, args) => {
            let exps = vec_map_result(args, |e| expr_to_exp(ctx, e))?;
            Ok(Spanned::new(expr.span.clone(), StmX::Call(x.clone(), Rc::new(exps), None)))
        }
        ExprX::Assume(expr) => {
            Ok(Spanned::new(expr.span.clone(), StmX::Assume(expr_to_exp(ctx, expr)?)))
        }
        ExprX::Assert(expr) => {
            Ok(Spanned::new(expr.span.clone(), StmX::Assert(expr_to_exp(ctx, expr)?)))
        }
        ExprX::Assign(lhs, rhs) => {
            let dest = expr_to_exp(ctx, lhs)?;
            match (expr_must_be_call_stm(ctx, rhs)?, &dest.x) {
                (Some((func_name, args)), ExpX::Var(var)) => Ok(Spanned::new(
                    expr.span.clone(),
                    StmX::Call(func_name, args, Some(Dest { var: var.clone(), mutable: true })),
                )),
                _ => {
                    Ok(Spanned::new(expr.span.clone(), StmX::Assign(dest, expr_to_exp(ctx, rhs)?)))
                }
            }
        }
        ExprX::Fuel(x, fuel) => Ok(Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel))),
        ExprX::Block(stmts, expr_opt) => {
            let stms_vec = vec_map_result(stmts, |s| stmt_to_stm(ctx, s))?;
            let mut stms: Vec<Stm> = stms_vec.into_iter().flatten().collect();
            match (dest, expr_opt) {
                (None, None) => {}
                (Some(dest), Some(expr)) => {
                    let _ = expr_to_exp(ctx, expr);
                    let x_dest = Spanned::new(expr.span.clone(), ExpX::Var(dest.clone()));
                    let eq = ExpX::Binary(BinaryOp::Eq, x_dest, expr_to_exp(ctx, expr)?);
                    let assign = StmX::Assume(Spanned::new(expr.span.clone(), eq));
                    stms.push(Spanned::new(expr.span.clone(), assign));
                }
                _ => panic!("internal error: ExprX::Block {}", expr.span.as_string),
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
                StmX::Decl { ident: param.name.clone(), typ: param.typ.clone(), mutable: *mutable },
            );
            let mut stms = vec![decl];
            match init {
                None => {}
                Some(init) => {
                    let span = &init.span;
                    let var = Spanned::new(span.clone(), ExpX::Var(param.name.clone()));
                    match &expr_must_be_call_stm(ctx, init)? {
                        None => {
                            let rhs = expr_to_exp(ctx, init)?;
                            let eq =
                                Spanned::new(span.clone(), ExpX::Binary(BinaryOp::Eq, var, rhs));
                            stms.push(Spanned::new(span.clone(), StmX::Assume(eq)));
                        }
                        Some((func_name, args)) => {
                            let dest = Some(Dest { var: param.name.clone(), mutable: *mutable });
                            let call = StmX::Call(func_name.clone(), args.clone(), dest);
                            stms.push(Spanned::new(span.clone(), call));
                        }
                    }
                }
            }
            Ok(stms)
        }
    }
}
