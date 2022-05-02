use crate::ast::{
    BinaryOp, CallTarget, Constant, ExprX, Fun, Function, FunctionKind, GenericBoundX, IntRange,
    MaskSpec, Path, SpannedTyped, TypX, Typs, UnaryOp, UnaryOpr, VirErr,
};
use crate::ast_to_sst::expr_to_exp;
use crate::ast_util::err_str;
use crate::context::Ctx;
use crate::def::{
    check_decrease_int, decrease_at_entry, height, prefix_recursive_fun, suffix_rename, Spanned,
    FUEL_PARAM, FUEL_TYPE,
};
use crate::func_to_air::params_to_pars;
use crate::scc::Graph;
use crate::sst::{BndX, Dest, Exp, ExpX, Exps, LocalDecl, LocalDeclX, Stm, StmX, UniqueIdent};
use crate::sst_visitor::{
    exp_rename_vars, exp_visitor_check, exp_visitor_dfs, map_exp_visitor, map_stm_visitor,
    stm_visitor_dfs, VisitorControlFlow,
};
use crate::util::vec_map_result;
use air::ast::{Binder, Commands, Quant, Span};
use air::ast_util::{ident_binder, str_ident, str_typ};
use air::errors::error;
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node {
    Fun(Fun),
    Trait(Path),
    DatatypeTraitBound { datatype: Path, trait_path: Path },
}

#[derive(Clone)]
struct Ctxt<'a> {
    recursive_function_name: Fun,
    num_decreases: usize,
    scc_rep: Node,
    ctx: &'a Ctx,
}

fn get_callee(ctx: &Ctx, target: &Fun, targs: &Typs) -> Option<Fun> {
    let fun = &ctx.func_map[target];
    if let FunctionKind::TraitMethodDecl { .. } = &fun.x.kind {
        match &*targs[0] {
            TypX::TypParam(_) => None,
            TypX::Datatype(datatype, _) => {
                Some(ctx.global.method_map[&(target.clone(), datatype.clone())].clone())
            }
            _ => panic!("unexpected Self type instantiation"),
        }
    } else {
        Some(target.clone())
    }
}

fn is_self_call(ctx: &Ctx, target: &Fun, targs: &Typs, name: &Fun) -> bool {
    get_callee(ctx, target, targs) == Some(name.clone())
}

fn is_recursive_call(ctxt: &Ctxt, target: &Fun, targs: &Typs) -> bool {
    if let Some(callee) = get_callee(ctxt.ctx, target, targs) {
        callee == ctxt.recursive_function_name
            || ctxt.ctx.global.func_call_graph.get_scc_rep(&Node::Fun(callee.clone()))
                == ctxt.scc_rep
    } else {
        false
    }
}

fn height_of_exp(ctxt: &Ctxt, exp: &Exp) -> Exp {
    match &*exp.typ {
        TypX::Int(_) => exp.clone(),
        TypX::Datatype(..) => {
            let arg = if crate::poly::typ_is_poly(ctxt.ctx, &exp.typ) {
                exp.clone()
            } else {
                let op = UnaryOpr::Box(exp.typ.clone());
                let argx = ExpX::UnaryOpr(op, exp.clone());
                SpannedTyped::new(&exp.span, &exp.typ, argx)
            };
            let call = ExpX::Call(height(), Arc::new(vec![]), Arc::new(vec![arg]));
            SpannedTyped::new(&exp.span, &Arc::new(TypX::Int(IntRange::Int)), call)
        }
        // TODO: non-panic error message
        _ => panic!("internal error: unsupported type for decreases {:?}", exp.typ),
    }
}

fn check_decrease(ctxt: &Ctxt, span: &Span, exps: &Vec<Exp>) -> Exp {
    // When calling a function with more decreases clauses,
    // it's good enough to be equal on the shared decreases clauses
    // and to ignore the extra decreases clauses.
    let tbool = Arc::new(TypX::Bool);
    let when_equalx = ExpX::Const(Constant::Bool(ctxt.num_decreases < exps.len()));
    let when_equal = SpannedTyped::new(span, &tbool, when_equalx);

    let mut dec_exp: Exp = when_equal;
    for (i, exp) in (0..ctxt.num_decreases).zip(exps.iter()).rev() {
        let decreases_at_entryx = ExpX::Var((decrease_at_entry(i), Some(0)));
        let decreases_at_entry =
            SpannedTyped::new(&exp.span, &Arc::new(TypX::Int(IntRange::Int)), decreases_at_entryx);
        // 0 <= decreases_exp < decreases_at_entry
        let args = vec![height_of_exp(ctxt, exp), decreases_at_entry, dec_exp];
        let call = ExpX::Call(check_decrease_int(), Arc::new(vec![]), Arc::new(args));
        dec_exp = SpannedTyped::new(&exp.span, &Arc::new(TypX::Bool), call);
    }
    dec_exp
}

fn check_decrease_call(
    ctxt: &Ctxt,
    span: &Span,
    target: &Fun,
    targs: &Typs,
    args: &Exps,
) -> Result<Exp, VirErr> {
    let name = if let Some(callee) = get_callee(ctxt.ctx, target, targs) {
        callee
    } else {
        return Ok(SpannedTyped::new(
            span,
            &Arc::new(TypX::Bool),
            ExpX::Const(Constant::Bool(true)),
        ));
    };
    let function = &ctxt.ctx.func_map[&name];
    // check_decrease(let params = args in decreases_exp, decreases_at_entry)
    let params = &function.x.params;
    assert!(params.len() == args.len());
    let binders: Vec<Binder<Exp>> = params
        .iter()
        .zip(args.iter())
        .map(|(param, arg)| ident_binder(&suffix_rename(&param.x.name), &arg.clone()))
        .collect();
    let renames: HashMap<UniqueIdent, UniqueIdent> = params
        .iter()
        .map(|param| ((param.x.name.clone(), Some(0)), (suffix_rename(&param.x.name), None)))
        .collect();
    let mut decreases_exps: Vec<Exp> = Vec::new();
    for expr in function.x.decrease.iter() {
        let decreases_exp =
            expr_to_exp(ctxt.ctx, &params_to_pars(&function.x.params, false), expr)?;
        let dec_exp = exp_rename_vars(&decreases_exp, &renames);
        let e_decx = ExpX::Bind(
            Spanned::new(span.clone(), BndX::Let(Arc::new(binders.clone()))),
            dec_exp.clone(),
        );
        decreases_exps.push(SpannedTyped::new(&span, &dec_exp.typ, e_decx));
    }
    Ok(check_decrease(ctxt, span, &decreases_exps))
}

// Check that exp terminates
fn terminates(ctxt: &Ctxt, exp: &Exp) -> Result<Exp, VirErr> {
    let bool_exp = |expx: ExpX| SpannedTyped::new(&exp.span, &Arc::new(TypX::Bool), expx);
    match &exp.x {
        ExpX::Const(_) | ExpX::Var(..) | ExpX::VarAt(..) | ExpX::VarLoc(..) | ExpX::Old(..) => {
            Ok(bool_exp(ExpX::Const(Constant::Bool(true))))
        }
        ExpX::Loc(e) => terminates(ctxt, e),
        ExpX::Call(x, targs, args) => {
            let mut e = if is_recursive_call(ctxt, x, targs) {
                check_decrease_call(ctxt, &exp.span, x, targs, args)?
            } else {
                bool_exp(ExpX::Const(Constant::Bool(true)))
            };
            for arg in args.iter().rev() {
                let e_arg = terminates(ctxt, arg)?;
                e = bool_exp(ExpX::Binary(BinaryOp::And, e_arg, e));
            }
            Ok(e)
        }
        ExpX::CallLambda(_, f, args) => {
            let mut e = terminates(ctxt, f)?;
            for arg in args.iter().rev() {
                let e_arg = terminates(ctxt, arg)?;
                e = bool_exp(ExpX::Binary(BinaryOp::And, e_arg, e));
            }
            Ok(e)
        }
        ExpX::Ctor(_path, _ident, binders) => {
            let mut e = bool_exp(ExpX::Const(Constant::Bool(true)));
            for binder in binders.iter().rev() {
                let e_binder = terminates(ctxt, &binder.a)?;
                e = bool_exp(ExpX::Binary(BinaryOp::And, e_binder, e));
            }
            Ok(e)
        }
        ExpX::Unary(_, e1) => terminates(ctxt, e1),
        ExpX::UnaryOpr(_, e1) => terminates(ctxt, e1),
        ExpX::Binary(BinaryOp::And, e1, e2) | ExpX::Binary(BinaryOp::Implies, e1, e2) => {
            let t_e1 = terminates(ctxt, e1)?;
            let t_e2 = terminates(ctxt, e2)?;
            let imply = bool_exp(ExpX::Binary(BinaryOp::Implies, e1.clone(), t_e2));
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, t_e1, imply)))
        }
        ExpX::Binary(BinaryOp::Or, e1, e2) => {
            let t_e1 = terminates(ctxt, e1)?;
            let t_e2 = terminates(ctxt, e2)?;
            let not = bool_exp(ExpX::Unary(UnaryOp::Not, e1.clone()));
            let imply = bool_exp(ExpX::Binary(BinaryOp::Implies, not, t_e2));
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, t_e1, imply)))
        }
        ExpX::Binary(_, e1, e2) => {
            let e1 = terminates(ctxt, e1)?;
            let e2 = terminates(ctxt, e2)?;
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, e1, e2)))
        }
        ExpX::If(e1, e2, e3) => {
            let t_e1 = terminates(ctxt, e1)?;
            let t_e2 = terminates(ctxt, e2)?;
            let t_e3 = terminates(ctxt, e3)?;
            let e_if = bool_exp(ExpX::If(e1.clone(), t_e2, t_e3));
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, t_e1, e_if)))
        }
        ExpX::WithTriggers(_triggers, body) => terminates(ctxt, body),
        ExpX::Bind(bnd, e1) => {
            let t_e1 = terminates(ctxt, e1)?;
            match &bnd.x {
                BndX::Let(binders) => {
                    let mut e_bind = bool_exp(ExpX::Bind(
                        Spanned::new(bnd.span.clone(), BndX::Let(binders.clone())),
                        t_e1,
                    ));
                    for binder in binders.iter().rev() {
                        let e_binder = terminates(ctxt, &binder.a)?;
                        e_bind = bool_exp(ExpX::Binary(BinaryOp::And, e_binder, e_bind));
                    }
                    Ok(e_bind)
                }
                BndX::Quant(_, binders, triggers) => Ok(bool_exp(ExpX::Bind(
                    Spanned::new(
                        bnd.span.clone(),
                        BndX::Quant(Quant::Forall, binders.clone(), triggers.clone()),
                    ),
                    t_e1,
                ))),
                BndX::Lambda(_) => {
                    disallow_recursion_exp(ctxt, e1)?;
                    Ok(bool_exp(ExpX::Const(Constant::Bool(true))))
                }
                BndX::Choose(..) => {
                    disallow_recursion_exp(ctxt, e1)?;
                    Ok(bool_exp(ExpX::Const(Constant::Bool(true))))
                }
            }
        }
    }
}

pub(crate) fn is_recursive_exp(ctx: &Ctx, name: &Fun, body: &Exp) -> bool {
    if ctx.global.func_call_graph.get_scc_size(&Node::Fun(name.clone())) > 1 {
        // This function is part of a mutually recursive component
        true
    } else {
        let mut scope_map = ScopeMap::new();
        // Check for self-recursion, which SCC computation does not account for
        match exp_visitor_dfs(body, &mut scope_map, &mut |exp, _scope_map| match &exp.x {
            ExpX::Call(x, targs, _) if is_self_call(ctx, x, targs, name) => {
                VisitorControlFlow::Stop(())
            }
            _ => VisitorControlFlow::Recurse,
        }) {
            VisitorControlFlow::Stop(()) => true,
            _ => false,
        }
    }
}

pub(crate) fn is_recursive_stm(ctx: &Ctx, name: &Fun, body: &Stm) -> bool {
    if ctx.global.func_call_graph.get_scc_size(&Node::Fun(name.clone())) > 1 {
        // This function is part of a mutually recursive component
        true
    } else {
        // Check for self-recursion, which SCC computation does not account for
        match stm_visitor_dfs(body, &mut |stm| match &stm.x {
            StmX::Call(x, _, targs, _, _) if is_self_call(ctx, x, targs, name) => {
                VisitorControlFlow::Stop(())
            }
            _ => VisitorControlFlow::Recurse,
        }) {
            VisitorControlFlow::Stop(()) => true,
            _ => false,
        }
    }
}

fn mk_decreases_at_entry(ctxt: &Ctxt, span: &Span, exps: &Vec<Exp>) -> (Vec<LocalDecl>, Vec<Stm>) {
    let mut decls: Vec<LocalDecl> = Vec::new();
    let mut stm_assigns: Vec<Stm> = Vec::new();
    for (i, exp) in exps.iter().enumerate() {
        let typ = Arc::new(TypX::Int(IntRange::Int));
        let decl = Arc::new(LocalDeclX {
            ident: (decrease_at_entry(i), Some(0)),
            typ: typ.clone(),
            mutable: false,
        });
        let uniq_ident = (decrease_at_entry(i), Some(0));
        let stm_assign = Spanned::new(
            span.clone(),
            StmX::Assign {
                lhs: Dest {
                    dest: crate::ast_to_sst::var_loc_exp(&span, &typ, uniq_ident),
                    is_init: true,
                },
                rhs: height_of_exp(ctxt, exp),
            },
        );
        decls.push(decl);
        stm_assigns.push(stm_assign);
    }
    (decls, stm_assigns)
}

// REVIEW: for simplicity, we completely disallow recursive calls from inside closures.
// It's possible that we could be allow some recursion.
fn disallow_recursion_exp(ctxt: &Ctxt, exp: &Exp) -> Result<(), VirErr> {
    let mut scope_map = ScopeMap::new();
    exp_visitor_check(exp, &mut scope_map, &mut |exp, _scope_map| match &exp.x {
        ExpX::Call(x, targs, _) if is_recursive_call(ctxt, x, targs) => {
            err_str(&exp.span, "recursion not allowed here")
        }
        _ => Ok(()),
    })
}

pub(crate) fn check_termination_exp(
    ctx: &Ctx,
    function: &Function,
    mut local_decls: Vec<LocalDecl>,
    body: &Exp,
    proof_body: Vec<Stm>,
) -> Result<(bool, Commands, Exp), VirErr> {
    if !is_recursive_exp(ctx, &function.x.name, body) {
        return Ok((false, Arc::new(vec![]), body.clone()));
    }
    let num_decreases = function.x.decrease.len();
    if num_decreases == 0 {
        return err_str(&function.span, "recursive function must call decreases(...)");
    }

    let decreases_exps = vec_map_result(&function.x.decrease, |e| {
        expr_to_exp(ctx, &params_to_pars(&function.x.params, false), e)
    })?;
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&Node::Fun(function.x.name.clone()));
    let ctxt =
        Ctxt { recursive_function_name: function.x.name.clone(), num_decreases, scc_rep, ctx };
    let check = terminates(&ctxt, &body)?;
    let (mut decls, mut stm_assigns) = mk_decreases_at_entry(&ctxt, &body.span, &decreases_exps);
    stm_assigns.extend(proof_body.clone());
    let error = error("could not prove termination", &body.span);
    let stm_assert = Spanned::new(body.span.clone(), StmX::Assert(Some(error), check));
    stm_assigns.push(stm_assert);
    let stm_block = Spanned::new(body.span.clone(), StmX::Block(Arc::new(stm_assigns)));

    // TODO: If we decide to support debugging decreases failures, we should plumb _snap_map
    // up to the VIR model
    local_decls.append(&mut decls);
    let (commands, _snap_map) = crate::sst_to_air::body_stm_to_air(
        ctx,
        &function.span,
        &vec![],
        &function.x.typ_params(),
        &function.x.params,
        &Arc::new(local_decls),
        &Arc::new(vec![]),
        &Arc::new(vec![]),
        &Arc::new(vec![]),
        &MaskSpec::NoSpec,
        function.x.mode,
        &stm_block,
        false,
        false,
        false,
    );

    assert_eq!(commands.len(), 1);
    let commands = commands.into_iter().next().unwrap().commands.clone();

    // New body: substitute rec%f(args, fuel) for f(args)
    let body = map_exp_visitor(&body, &mut |exp| match &exp.x {
        ExpX::Call(x, typs, args)
            if is_recursive_call(&ctxt, x, typs) && ctx.func_map[x].x.body.is_some() =>
        {
            let mut args = (**args).clone();
            let varx = ExpX::Var((str_ident(FUEL_PARAM), Some(0)));
            let var_typ = Arc::new(TypX::Air(str_typ(FUEL_TYPE)));
            args.push(SpannedTyped::new(&exp.span, &var_typ, varx));
            let rec_name = prefix_recursive_fun(&x);
            let callx = ExpX::Call(rec_name, typs.clone(), Arc::new(args));
            SpannedTyped::new(&exp.span, &exp.typ, callx)
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
    if !is_recursive_stm(ctx, &function.x.name, body) {
        return Ok((vec![], body.clone()));
    }
    let num_decreases = function.x.decrease.len();
    if num_decreases == 0 {
        return err_str(&function.span, "recursive function must call decreases(...)");
    }

    let decreases_exps = vec_map_result(&function.x.decrease, |e| {
        expr_to_exp(ctx, &params_to_pars(&function.x.params, false), e)
    })?;
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&Node::Fun(function.x.name.clone()));
    let ctxt =
        Ctxt { recursive_function_name: function.x.name.clone(), num_decreases, scc_rep, ctx };
    let stm = map_stm_visitor(body, &mut |s| match &s.x {
        StmX::Call(x, _, targs, args, _) if is_recursive_call(&ctxt, x, targs) => {
            let check = check_decrease_call(&ctxt, &s.span, x, targs, args)?;
            let error = error("could not prove termination", &s.span);
            let stm_assert = Spanned::new(s.span.clone(), StmX::Assert(Some(error), check));
            let stm_block =
                Spanned::new(s.span.clone(), StmX::Block(Arc::new(vec![stm_assert, s.clone()])));
            Ok(stm_block)
        }
        _ => Ok(s.clone()),
    })?;
    let (decls, mut stm_assigns) = mk_decreases_at_entry(&ctxt, &stm.span, &decreases_exps);
    stm_assigns.push(stm.clone());
    let stm_block = Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stm_assigns)));
    Ok((decls, stm_block))
}

pub(crate) fn expand_call_graph(
    func_map: &HashMap<Fun, Function>,
    method_map: &HashMap<(Fun, Path), Fun>,
    call_graph: &mut Graph<Node>,
    function: &Function,
) -> Result<(), VirErr> {
    // See recursive_types::check_traits for more documentation
    let f_node = Node::Fun(function.x.name.clone());

    // Add D: T --> f and D: T --> T where f is one of D's methods that implements T
    if let FunctionKind::TraitMethodImpl { trait_path, datatype, .. } = function.x.kind.clone() {
        let t_node = Node::Trait(trait_path.clone());
        let dt_node = Node::DatatypeTraitBound { datatype, trait_path };
        call_graph.add_edge(t_node, dt_node.clone());
        call_graph.add_edge(dt_node, f_node.clone());
    }

    // Add f --> T for any function f<A: T> with type parameter A: T
    for (_, tbound) in function.x.typ_bounds.iter() {
        if let GenericBoundX::Traits(traits) = &**tbound {
            for tr in traits {
                call_graph.add_edge(Node::Trait(tr.clone()), f_node.clone());
            }
        }
    }

    // Add f --> fd if fd is the decreases proof for f's definition
    if let Some(decrease_by) = &function.x.decrease_by {
        call_graph.add_edge(f_node.clone(), Node::Fun(decrease_by.clone()))
    }

    // Add f1 --> f2 edges where f1 calls f2
    // Add f1 --> D: T where one of f1's expressions instantiates A: T with D: T
    // Add T --> f2 if the requires/ensures of T's method declarations call f2
    crate::ast_visitor::function_visitor_check::<VirErr, _>(function, &mut |expr| {
        match &expr.x {
            ExprX::Call(CallTarget::Static(x, ts), _) => {
                let f2 = &func_map[x];
                assert!(f2.x.typ_bounds.len() == ts.len());
                let mut t_param_args = f2.x.typ_bounds.iter().zip(ts.iter());

                let callee =
                    if let FunctionKind::TraitMethodDecl { trait_path: trait_path2 } = &f2.x.kind {
                        let (tparam, targ) = t_param_args.next().expect("method Self type");
                        assert!(tparam.0 == crate::def::trait_self_type_param());
                        match &**targ {
                            TypX::TypParam(p) if p == &crate::def::trait_self_type_param() => {
                                match &function.x.kind {
                                    FunctionKind::TraitMethodDecl { trait_path: trait_path1 }
                                        if trait_path1 == trait_path2 =>
                                    {
                                        // Call to self within trait, T.f1 --> T.f2
                                        Some(x)
                                    }
                                    _ => {
                                        return err_str(&expr.span, "unsupported use of Self type");
                                    }
                                }
                            }
                            TypX::TypParam(p) => {
                                // no f1 --> f2 edge for calls via a type parameter A: T,
                                // because we (conceptually) get f2 from the dictionary passed for A: T.
                                let bound = function.x.typ_bounds.iter().find(|(q, _)| q == p);
                                let bound = bound.expect("missing type parameter");
                                if let GenericBoundX::Traits(ts) = &*bound.1 {
                                    assert!(ts.iter().any(|t| t == trait_path2));
                                } else {
                                    panic!("wrong type bound on type parameter");
                                }
                                None
                            }
                            TypX::Datatype(datatype, _) => {
                                // f1 --> D.f2
                                Some(&method_map[&(x.clone(), datatype.clone())])
                            }
                            _ => panic!("unexpected Self type instantiation"),
                        }
                    } else {
                        Some(x)
                    };

                for ((_, tbound), targ) in t_param_args {
                    match &**tbound {
                        GenericBoundX::Traits(traits) => {
                            for tr in traits {
                                match &**targ {
                                    TypX::Datatype(datatype, _) => {
                                        // f1 --> D: T
                                        call_graph.add_edge(
                                            f_node.clone(),
                                            Node::DatatypeTraitBound {
                                                datatype: datatype.clone(),
                                                trait_path: tr.clone(),
                                            },
                                        );
                                    }
                                    TypX::TypParam(..) => match &function.x.kind {
                                        FunctionKind::Static => {}
                                        FunctionKind::TraitMethodDecl { .. } => {
                                            return err_str(
                                                &expr.span,
                                                "not yet supported: trait type bounds",
                                            );
                                        }
                                        FunctionKind::TraitMethodImpl { .. } => {}
                                    },
                                    _ => {
                                        return err_str(
                                            &expr.span,
                                            "not yet supported: type bounds on non-datatypes",
                                        );
                                    }
                                }
                            }
                        }
                        GenericBoundX::FnSpec(..) => {}
                    }
                }

                if let FunctionKind::TraitMethodDecl { trait_path } = &function.x.kind {
                    // T --> f2
                    call_graph.add_edge(Node::Trait(trait_path.clone()), Node::Fun(x.clone()))
                }

                // f1 --> f2
                if let Some(callee) = callee {
                    call_graph.add_edge(f_node.clone(), Node::Fun(callee.clone()))
                }
            }
            _ => {}
        }
        Ok(())
    })?;

    for fun in &function.x.extra_dependencies {
        call_graph.add_edge(f_node.clone(), Node::Fun(fun.clone()));
    }

    Ok(())
}
