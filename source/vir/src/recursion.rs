use crate::ast::{
    BinaryOp, Constant, Function, Ident, IntRange, Params, Path, Typ, TypX, UnaryOp, UnaryOpr,
    VirErr,
};
use crate::ast_util::err_str;
use crate::ast_visitor::map_expr_visitor;
use crate::context::Ctx;
use crate::def::{
    check_decrease_int, height, prefix_recursive, suffix_rename, Spanned, DECREASE_AT_ENTRY,
    FUEL_PARAM,
};
use crate::scc::Graph;
use crate::sst::{BndX, Exp, ExpX, Exps, LocalDecl, LocalDeclX, Stm, StmX, UniqueIdent};
use crate::sst_visitor::{exp_rename_vars, map_exp_visitor, map_stm_visitor};
use air::ast::{Binder, Commands, Quant, Span};
use air::ast_util::{ident_binder, str_ident};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone)]
struct Ctxt<'a> {
    recursive_function_path: Path,
    params: Params,
    decreases_at_entry: Ident,
    decreases_exp: Exp,
    decreases_typ: Typ,
    scc_rep: Path,
    ctx: &'a Ctx,
}

fn height_of_exp(ctxt: &Ctxt, exp: &Exp) -> Exp {
    match &*ctxt.decreases_typ {
        TypX::Int(_) => exp.clone(),
        TypX::Datatype(..) => {
            let op = UnaryOpr::Box(ctxt.decreases_typ.clone());
            let arg = Spanned::new(exp.span.clone(), ExpX::UnaryOpr(op, exp.clone()));
            let call = ExpX::Call(height(), Arc::new(vec![]), Arc::new(vec![arg]));
            Spanned::new(exp.span.clone(), call)
        }
        // TODO: non-panic error message
        _ => panic!("internal error: unsupported type for decreases {:?}", ctxt.decreases_typ),
    }
}

fn check_decrease(ctxt: &Ctxt, exp: &Exp) -> Exp {
    let decreases_at_entry =
        Spanned::new(exp.span.clone(), ExpX::Var((ctxt.decreases_at_entry.clone(), Some(0))));
    // 0 <= decreases_exp < decreases_at_entry
    let args = vec![height_of_exp(ctxt, exp), decreases_at_entry];
    let call = ExpX::Call(check_decrease_int(), Arc::new(vec![]), Arc::new(args));
    Spanned::new(exp.span.clone(), call)
}

fn check_decrease_rename(ctxt: &Ctxt, span: &Span, args: &Exps) -> Exp {
    // check_decrease(let params = args in decreases_exp, decreases_at_entry)
    let binders: Vec<Binder<Exp>> = ctxt
        .params
        .iter()
        .zip(args.iter())
        .map(|(param, arg)| ident_binder(&suffix_rename(&param.x.name), &arg.clone()))
        .collect();
    let renames: HashMap<UniqueIdent, UniqueIdent> = ctxt
        .params
        .iter()
        .map(|param| ((param.x.name.clone(), Some(0)), (suffix_rename(&param.x.name), None)))
        .collect();
    let dec_exp = exp_rename_vars(&ctxt.decreases_exp, &renames);
    let e_dec = Spanned::new(
        span.clone(),
        ExpX::Bind(Spanned::new(span.clone(), BndX::Let(Arc::new(binders))), dec_exp),
    );
    check_decrease(ctxt, &e_dec)
}

fn update_decreases_exp<'a>(ctxt: &'a Ctxt, name: &Path) -> Result<Ctxt<'a>, VirErr> {
    let function = ctxt.ctx.func_map.get(name).expect("func_map should hold all functions");
    let new_decreases_expr = function
        .x
        .decrease
        .as_ref()
        .expect("shouldn't call update_decreases_exp on a function without a decreases clause")
        .clone();
    let new_decreases_exp =
        crate::ast_to_sst::expr_to_exp(ctxt.ctx, &function.x.params, &new_decreases_expr)?;
    Ok(Ctxt { decreases_exp: new_decreases_exp, ..ctxt.clone() })
}

// Check that exp terminates
fn terminates(ctxt: &Ctxt, exp: &Exp) -> Result<Exp, VirErr> {
    match &exp.x {
        ExpX::Const(_) | ExpX::Var(..) | ExpX::Old(..) => {
            Ok(Spanned::new(exp.span.clone(), ExpX::Const(Constant::Bool(true))))
        }
        ExpX::Call(x, _, args) => {
            let mut e = if *x == ctxt.recursive_function_path
                || ctxt.ctx.func_call_graph.get_scc_rep(x) == ctxt.scc_rep
            {
                let new_ctxt = update_decreases_exp(&ctxt, x)?;
                check_decrease_rename(&new_ctxt, &exp.span, args)
            } else {
                Spanned::new(exp.span.clone(), ExpX::Const(Constant::Bool(true)))
            };
            for arg in args.iter().rev() {
                let e_arg = terminates(ctxt, arg)?;
                e = Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::And, e_arg, e));
            }
            Ok(e)
        }
        ExpX::Ctor(_path, _ident, binders) => {
            let mut e = Spanned::new(exp.span.clone(), ExpX::Const(Constant::Bool(true)));
            for binder in binders.iter().rev() {
                let e_binder = terminates(ctxt, &binder.a)?;
                e = Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::And, e_binder, e));
            }
            Ok(e)
        }
        ExpX::Unary(_, e1) => terminates(ctxt, e1),
        ExpX::UnaryOpr(_, e1) => terminates(ctxt, e1),
        ExpX::Binary(BinaryOp::And, e1, e2) | ExpX::Binary(BinaryOp::Implies, e1, e2) => {
            let t_e1 = terminates(ctxt, e1)?;
            let t_e2 = terminates(ctxt, e2)?;
            let imply =
                Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::Implies, e1.clone(), t_e2));
            Ok(Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::And, t_e1, imply)))
        }
        ExpX::Binary(BinaryOp::Or, e1, e2) => {
            let t_e1 = terminates(ctxt, e1)?;
            let t_e2 = terminates(ctxt, e2)?;
            let not = Spanned::new(exp.span.clone(), ExpX::Unary(UnaryOp::Not, e1.clone()));
            let imply = Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::Implies, not, t_e2));
            Ok(Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::And, t_e1, imply)))
        }
        ExpX::Binary(_, e1, e2) => {
            let e1 = terminates(ctxt, e1)?;
            let e2 = terminates(ctxt, e2)?;
            Ok(Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::And, e1, e2)))
        }
        ExpX::If(e1, e2, e3) => {
            let t_e1 = terminates(ctxt, e1)?;
            let t_e2 = terminates(ctxt, e2)?;
            let t_e3 = terminates(ctxt, e3)?;
            let e_if = Spanned::new(exp.span.clone(), ExpX::If(e1.clone(), t_e2, t_e3));
            Ok(Spanned::new(exp.span.clone(), ExpX::Binary(BinaryOp::And, t_e1, e_if)))
        }
        ExpX::Bind(bnd, e1) => {
            let t_e1 = terminates(ctxt, e1)?;
            match &bnd.x {
                BndX::Let(binders) => {
                    let mut e_bind = Spanned::new(
                        exp.span.clone(),
                        ExpX::Bind(
                            Spanned::new(bnd.span.clone(), BndX::Let(binders.clone())),
                            t_e1,
                        ),
                    );
                    for binder in binders.iter().rev() {
                        let e_binder = terminates(ctxt, &binder.a)?;
                        e_bind = Spanned::new(
                            exp.span.clone(),
                            ExpX::Binary(BinaryOp::And, e_binder, e_bind),
                        );
                    }
                    Ok(e_bind)
                }
                BndX::Quant(_, binders, triggers) => Ok(Spanned::new(
                    exp.span.clone(),
                    ExpX::Bind(
                        Spanned::new(
                            bnd.span.clone(),
                            BndX::Quant(Quant::Forall, binders.clone(), triggers.clone()),
                        ),
                        t_e1,
                    ),
                )),
            }
        }
    }
}

pub(crate) fn is_recursive_exp(ctx: &Ctx, name: &Path, body: &Exp) -> bool {
    if ctx.func_call_graph.get_scc_size(name) > 1 {
        // This function is part of a mutually recursive component
        true
    } else {
        // Check for self-recursion, which SCC computation does not account for
        let mut recurse = false;
        map_exp_visitor(body, &mut |exp| match &exp.x {
            ExpX::Call(x, _, _) if x == name => {
                recurse = true;
                exp.clone()
            }
            _ => exp.clone(),
        });
        recurse
    }
}

pub(crate) fn is_recursive_stm(ctx: &Ctx, name: &Path, body: &Stm) -> bool {
    if ctx.func_call_graph.get_scc_size(name) > 1 {
        // This function is part of a mutually recursive component
        true
    } else {
        // Check for self-recursion, which SCC computation does not account for
        let mut recurse = false;
        map_stm_visitor(body, &mut |stm| match &stm.x {
            StmX::Call(x, _, _, _) if x == name => {
                recurse = true;
                Ok(stm.clone())
            }
            _ => Ok(stm.clone()),
        })
        .unwrap();
        recurse
    }
}

fn mk_decreases_at_entry(ctxt: &Ctxt, span: &Span) -> (LocalDecl, Stm) {
    let decl = Arc::new(LocalDeclX {
        ident: (ctxt.decreases_at_entry.clone(), Some(0)),
        typ: Arc::new(TypX::Int(IntRange::Int)),
        mutable: false,
    });
    let stm_assign = Spanned::new(
        span.clone(),
        StmX::Assign {
            lhs: (ctxt.decreases_at_entry.clone(), Some(0)),
            rhs: height_of_exp(ctxt, &ctxt.decreases_exp),
            is_init: true,
        },
    );
    (decl, stm_assign)
}

pub(crate) fn check_termination_exp(
    ctx: &Ctx,
    function: &Function,
    mut local_decls: Vec<LocalDecl>,
    body: &Exp,
) -> Result<(bool, Commands, Exp), VirErr> {
    if !is_recursive_exp(ctx, &function.x.path, body) {
        return Ok((false, Arc::new(vec![]), body.clone()));
    }

    let decreases_expr = match &function.x.decrease {
        None => {
            return err_str(&function.span, "recursive function must call decreases(...)");
        }
        Some(dec) => dec.clone(),
    };
    let decreases_typ = decreases_expr.typ.clone();
    let decreases_exp = crate::ast_to_sst::expr_to_exp(ctx, &function.x.params, &decreases_expr)?;
    let decreases_at_entry = str_ident(DECREASE_AT_ENTRY);
    let scc_rep = ctx.func_call_graph.get_scc_rep(&function.x.path);
    let scc_rep_clone = scc_rep.clone();
    let ctxt = Ctxt {
        recursive_function_path: function.x.path.clone(),
        params: function.x.params.clone(),
        decreases_at_entry,
        decreases_exp,
        decreases_typ,
        scc_rep,
        ctx,
    };
    let check = terminates(&ctxt, &body)?;
    let (decl, stm_assign) = mk_decreases_at_entry(&ctxt, &body.span);
    let span =
        Span { description: Some("could not prove termination".to_string()), ..body.span.clone() };
    let stm_assert = Spanned::new(span, StmX::Assert(check));
    let stm_block =
        Spanned::new(body.span.clone(), StmX::Block(Arc::new(vec![stm_assign, stm_assert])));

    // TODO: If we decide to support debugging decreases failures, we should plumb _snap_map
    // up to the VIR model
    local_decls.push(decl);
    let (commands, _assign_set, _snap_map) = crate::sst_to_air::body_stm_to_air(
        ctx,
        &function.x.typ_params,
        &function.x.params,
        &Arc::new(local_decls),
        &Arc::new(vec![]),
        &Arc::new(vec![]),
        &Arc::new(vec![]),
        &stm_block,
    );

    // New body: substitute rec%f(args, fuel) for f(args)
    let body = map_exp_visitor(&body, &mut |exp| match &exp.x {
        ExpX::Call(x, typs, args)
            if *x == function.x.path || ctx.func_call_graph.get_scc_rep(x) == scc_rep_clone =>
        {
            let mut args = (**args).clone();
            args.push(Spanned::new(exp.span.clone(), ExpX::Var((str_ident(FUEL_PARAM), Some(0)))));
            let rec_name = prefix_recursive(&x);
            Spanned::new(exp.span.clone(), ExpX::Call(rec_name, typs.clone(), Arc::new(args)))
        }
        _ => exp.clone(),
    });

    Ok((true, commands, body))
}

pub(crate) fn check_termination_stm(
    ctx: &Ctx,
    function: &Function,
    body: &Stm,
) -> Result<(Vec<LocalDecl>, Stm), VirErr> {
    if !is_recursive_stm(ctx, &function.x.path, body) {
        return Ok((vec![], body.clone()));
    }

    let decreases_expr = match &function.x.decrease {
        None => {
            return err_str(&function.span, "recursive function must call decreases(...)");
        }
        Some(dec) => dec.clone(),
    };
    let decreases_typ = decreases_expr.typ.clone();
    let decreases_exp = crate::ast_to_sst::expr_to_exp(ctx, &function.x.params, &decreases_expr)?;
    let decreases_at_entry = str_ident(DECREASE_AT_ENTRY);
    let scc_rep = ctx.func_call_graph.get_scc_rep(&function.x.path);
    let ctxt = Ctxt {
        recursive_function_path: function.x.path.clone(),
        params: function.x.params.clone(),
        decreases_at_entry,
        decreases_exp,
        decreases_typ,
        scc_rep,
        ctx,
    };
    let stm = map_stm_visitor(body, &mut |s| match &s.x {
        StmX::Call(x, _, args, _)
            if *x == function.x.path || ctx.func_call_graph.get_scc_rep(x) == ctxt.scc_rep =>
        {
            let new_ctxt = update_decreases_exp(&ctxt, x)?;
            let check = check_decrease_rename(&new_ctxt, &s.span, &args);
            let span = Span {
                description: Some("could not prove termination".to_string()),
                ..s.span.clone()
            };
            let stm_assert = Spanned::new(span, StmX::Assert(check));
            let stm_block =
                Spanned::new(s.span.clone(), StmX::Block(Arc::new(vec![stm_assert, s.clone()])));
            Ok(stm_block)
        }
        _ => Ok(s.clone()),
    })?;
    let (decl, stm_assign) = mk_decreases_at_entry(&ctxt, &stm.span);
    let stm_block =
        Spanned::new(stm.span.clone(), StmX::Block(Arc::new(vec![stm_assign, stm.clone()])));
    Ok((vec![decl], stm_block))
}

fn add_call_graph_edges(
    call_graph: &mut Graph<Path>,
    src: &Path,
    expr: &crate::ast::Expr,
) -> Result<crate::ast::Expr, VirErr> {
    use crate::ast::ExprX;

    match &expr.x {
        ExprX::Call(x, _, _) | ExprX::Fuel(x, _) => call_graph.add_edge(src.clone(), x.clone()),
        _ => {}
    }
    Ok(expr.clone())
}

pub(crate) fn expand_call_graph(
    call_graph: &mut Graph<Path>,
    function: &Function,
) -> Result<(), VirErr> {
    // We only traverse expressions (not statements), since calls only appear in the former (see ast.rs)
    if let Some(body) = &function.x.body {
        map_expr_visitor(body, &mut |expr| {
            add_call_graph_edges(call_graph, &function.x.path, expr)
        })?;
    }
    Ok(())
}
