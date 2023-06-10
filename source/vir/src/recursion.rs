use crate::ast::{
    AutospecUsage, BinaryOp, CallTarget, Constant, ExprX, Fun, Function, FunctionKind,
    GenericBoundX, IntRange, MaskSpec, Path, SpannedTyped, Typ, TypX, Typs, UnaryOp, UnaryOpr,
    VirErr,
};
use crate::ast_to_sst::expr_to_exp;
use crate::ast_util::{error, msg_error, QUANT_FORALL};
use crate::context::Ctx;
use crate::def::{
    decrease_at_entry, suffix_rename, unique_bound, unique_local, Spanned, FUEL_PARAM, FUEL_TYPE,
};
use crate::func_to_air::{params_to_pars, SstMap};
use crate::scc::Graph;
use crate::sst::{
    BndX, CallFun, Dest, Exp, ExpX, Exps, InternalFun, LocalDecl, LocalDeclX, Stm, StmX,
    UniqueIdent,
};
use crate::sst_to_air::PostConditionKind;
use crate::sst_visitor::{
    exp_rename_vars, exp_visitor_check, exp_visitor_dfs, map_exp_visitor, map_stm_visitor,
    stm_visitor_dfs, VisitorControlFlow,
};
use crate::util::vec_map_result;
use air::ast::{Binder, Commands, Span};
use air::ast_util::{ident_binder, str_ident, str_typ};
use air::messages::Diagnostics;
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node {
    Fun(Fun),
    Trait(Path),
    Datatype(Path),
    DatatypeTraitBound { self_typ: Typ, trait_path: Path },
}

#[derive(Clone)]
struct Ctxt<'a> {
    recursive_function_name: Fun,
    num_decreases: usize,
    scc_rep: Node,
    ctx: &'a Ctx,
}

fn get_callee(ctx: &Ctx, target: &Fun, resolved_method: &Option<(Fun, Typs)>) -> Option<Fun> {
    let fun = &ctx.func_map[target];
    if let FunctionKind::TraitMethodDecl { .. } = &fun.x.kind {
        resolved_method.clone().map(|(x, _)| x)
    } else {
        Some(target.clone())
    }
}

fn is_self_call(
    ctx: &Ctx,
    target: &Fun,
    resolved_method: &Option<(Fun, Typs)>,
    name: &Fun,
) -> bool {
    get_callee(ctx, target, resolved_method) == Some(name.clone())
}

fn is_recursive_call(ctxt: &Ctxt, target: &Fun, resolved_method: &Option<(Fun, Typs)>) -> bool {
    if let Some(callee) = get_callee(ctxt.ctx, target, resolved_method) {
        callee == ctxt.recursive_function_name
            || ctxt.ctx.global.func_call_graph.get_scc_rep(&Node::Fun(callee.clone()))
                == ctxt.scc_rep
    } else {
        false
    }
}

fn height_of_exp(ctxt: &Ctxt, exp: &Exp) -> Exp {
    match &*crate::ast_util::undecorate_typ(&exp.typ) {
        TypX::Int(_) => exp.clone(),
        TypX::Datatype(..) => {
            let arg = if crate::poly::typ_is_poly(ctxt.ctx, &exp.typ) {
                exp.clone()
            } else {
                let op = UnaryOpr::Box(exp.typ.clone());
                let argx = ExpX::UnaryOpr(op, exp.clone());
                SpannedTyped::new(&exp.span, &exp.typ, argx)
            };
            let call = ExpX::UnaryOpr(UnaryOpr::Height, arg);
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
        let decreases_at_entryx = ExpX::Var(unique_local(&decrease_at_entry(i)));
        let decreases_at_entry =
            SpannedTyped::new(&exp.span, &Arc::new(TypX::Int(IntRange::Int)), decreases_at_entryx);
        // 0 <= decreases_exp < decreases_at_entry
        let args = vec![height_of_exp(ctxt, exp), decreases_at_entry, dec_exp];
        let call = ExpX::Call(
            CallFun::InternalFun(InternalFun::CheckDecreaseInt),
            Arc::new(vec![]),
            Arc::new(args),
        );
        dec_exp = SpannedTyped::new(&exp.span, &Arc::new(TypX::Bool), call);
    }
    dec_exp
}

fn check_decrease_call(
    ctxt: &Ctxt,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    span: &Span,
    target: &Fun,
    resolved_method: &Option<(Fun, Typs)>,
    args: &Exps,
) -> Result<Exp, VirErr> {
    let name = if let Some(callee) = get_callee(ctxt.ctx, target, resolved_method) {
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
        .map(|param| (unique_local(&param.x.name), unique_bound(&suffix_rename(&param.x.name))))
        .collect();
    let mut decreases_exps: Vec<Exp> = Vec::new();
    for expr in function.x.decrease.iter() {
        let decreases_exp = expr_to_exp(
            ctxt.ctx,
            diagnostics,
            fun_ssts,
            &params_to_pars(&function.x.params, true),
            expr,
        )?;
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
fn terminates(
    ctxt: &Ctxt,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    exp: &Exp,
) -> Result<Exp, VirErr> {
    let bool_exp = |expx: ExpX| SpannedTyped::new(&exp.span, &Arc::new(TypX::Bool), expx);
    let r = |e: &Exp| terminates(ctxt, diagnostics, fun_ssts, e);
    match &exp.x {
        ExpX::Const(_)
        | ExpX::Var(..)
        | ExpX::VarAt(..)
        | ExpX::VarLoc(..)
        | ExpX::Old(..)
        | ExpX::NullaryOpr(..) => Ok(bool_exp(ExpX::Const(Constant::Bool(true)))),
        ExpX::Loc(e) => r(e),
        ExpX::Call(CallFun::Fun(x, resolved_method), _targs, args) => {
            let mut e = if is_recursive_call(ctxt, x, resolved_method) {
                check_decrease_call(
                    ctxt,
                    diagnostics,
                    fun_ssts,
                    &exp.span,
                    x,
                    resolved_method,
                    args,
                )?
            } else {
                bool_exp(ExpX::Const(Constant::Bool(true)))
            };
            for arg in args.iter().rev() {
                let e_arg = r(arg)?;
                e = bool_exp(ExpX::Binary(BinaryOp::And, e_arg, e));
            }
            Ok(e)
        }
        ExpX::Call(CallFun::CheckTermination(_), _, _) => {
            panic!("internal error: CheckTermination")
        }
        ExpX::Call(CallFun::InternalFun(_func), _tys, args) => {
            let mut e = bool_exp(ExpX::Const(Constant::Bool(true)));
            for arg in args.iter().rev() {
                let e_arg = r(arg)?;
                e = bool_exp(ExpX::Binary(BinaryOp::And, e_arg, e));
            }
            Ok(e)
        }
        ExpX::CallLambda(_, f, args) => {
            let mut e = r(f)?;
            for arg in args.iter().rev() {
                let e_arg = r(arg)?;
                e = bool_exp(ExpX::Binary(BinaryOp::And, e_arg, e));
            }
            Ok(e)
        }
        ExpX::Ctor(_path, _ident, binders) => {
            let mut e = bool_exp(ExpX::Const(Constant::Bool(true)));
            for binder in binders.iter().rev() {
                let e_binder = r(&binder.a)?;
                e = bool_exp(ExpX::Binary(BinaryOp::And, e_binder, e));
            }
            Ok(e)
        }
        ExpX::Unary(_, e1) => r(e1),
        ExpX::UnaryOpr(_, e1) => r(e1),
        ExpX::Binary(BinaryOp::And, e1, e2) | ExpX::Binary(BinaryOp::Implies, e1, e2) => {
            let t_e1 = r(e1)?;
            let t_e2 = r(e2)?;
            let imply = bool_exp(ExpX::Binary(BinaryOp::Implies, e1.clone(), t_e2));
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, t_e1, imply)))
        }
        ExpX::Binary(BinaryOp::Or, e1, e2) => {
            let t_e1 = r(e1)?;
            let t_e2 = r(e2)?;
            let not = bool_exp(ExpX::Unary(UnaryOp::Not, e1.clone()));
            let imply = bool_exp(ExpX::Binary(BinaryOp::Implies, not, t_e2));
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, t_e1, imply)))
        }
        ExpX::Binary(_, e1, e2) | ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), e1, e2) => {
            let e1 = r(e1)?;
            let e2 = r(e2)?;
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, e1, e2)))
        }
        ExpX::If(e1, e2, e3) => {
            let t_e1 = r(e1)?;
            let t_e2 = r(e2)?;
            let t_e3 = r(e3)?;
            let e_if = bool_exp(ExpX::If(e1.clone(), t_e2, t_e3));
            Ok(bool_exp(ExpX::Binary(BinaryOp::And, t_e1, e_if)))
        }
        ExpX::WithTriggers(_triggers, body) => r(body),
        ExpX::Bind(bnd, e1) => {
            let t_e1 = r(e1)?;
            match &bnd.x {
                BndX::Let(binders) => {
                    let mut e_bind = bool_exp(ExpX::Bind(
                        Spanned::new(bnd.span.clone(), BndX::Let(binders.clone())),
                        t_e1,
                    ));
                    for binder in binders.iter().rev() {
                        let e_binder = r(&binder.a)?;
                        e_bind = bool_exp(ExpX::Binary(BinaryOp::And, e_binder, e_bind));
                    }
                    Ok(e_bind)
                }
                BndX::Quant(_, binders, triggers) => Ok(bool_exp(ExpX::Bind(
                    Spanned::new(
                        bnd.span.clone(),
                        BndX::Quant(QUANT_FORALL, binders.clone(), triggers.clone()),
                    ),
                    t_e1,
                ))),
                BndX::Lambda(_, _) => {
                    disallow_recursion_exp(ctxt, e1)?;
                    Ok(bool_exp(ExpX::Const(Constant::Bool(true))))
                }
                BndX::Choose(..) => {
                    disallow_recursion_exp(ctxt, e1)?;
                    Ok(bool_exp(ExpX::Const(Constant::Bool(true))))
                }
            }
        }
        ExpX::Interp(_) => {
            panic!("Found an interpreter expression {:?} outside the interpreter", exp)
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
            ExpX::Call(CallFun::Fun(x, resolved_method), _, _)
                if is_self_call(ctx, x, resolved_method, name) =>
            {
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
            StmX::Call { fun, resolved_method, .. }
                if is_self_call(ctx, fun, resolved_method, name) =>
            {
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
            ident: unique_local(&decrease_at_entry(i)),
            typ: typ.clone(),
            mutable: false,
        });
        let uniq_ident = unique_local(&decrease_at_entry(i));
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
        ExpX::Call(CallFun::Fun(x, resolved_method), _targs, _)
            if is_recursive_call(ctxt, x, resolved_method) =>
        {
            error(&exp.span, "recursion not allowed here")
        }
        _ => Ok(()),
    })
}

pub(crate) fn check_termination_exp(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
    mut local_decls: Vec<LocalDecl>,
    body: &Exp,
    proof_body: Vec<Stm>,
    uses_decreases_by: bool,
) -> Result<(bool, Commands, Exp), VirErr> {
    if !is_recursive_exp(ctx, &function.x.name, body) {
        return Ok((false, Arc::new(vec![]), body.clone()));
    }
    let num_decreases = function.x.decrease.len();
    if num_decreases == 0 {
        return error(&function.span, "recursive function must have a decreases clause");
    }

    let decreases_exps = vec_map_result(&function.x.decrease, |e| {
        expr_to_exp(ctx, diagnostics, fun_ssts, &params_to_pars(&function.x.params, true), e)
    })?;
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&Node::Fun(function.x.name.clone()));
    let ctxt =
        Ctxt { recursive_function_name: function.x.name.clone(), num_decreases, scc_rep, ctx };
    let check = terminates(&ctxt, diagnostics, fun_ssts, &body)?;
    let (mut decls, mut stm_assigns) = mk_decreases_at_entry(&ctxt, &body.span, &decreases_exps);
    stm_assigns.extend(proof_body.clone());
    let stm_block = Spanned::new(body.span.clone(), StmX::Block(Arc::new(stm_assigns)));

    // TODO: If we decide to support debugging decreases failures, we should plumb _snap_map
    // up to the VIR model
    local_decls.append(&mut decls);
    let (commands, _snap_map) = crate::sst_to_air::body_stm_to_air(
        ctx,
        &function.span,
        &HashMap::new(),
        &function.x.typ_params(),
        &function.x.params,
        &Arc::new(local_decls),
        &Arc::new(vec![]),
        &Arc::new(vec![]),
        &Arc::new(vec![check]),
        &Arc::new(vec![]),
        &MaskSpec::NoSpec,
        function.x.mode,
        &stm_block,
        false,
        false,
        false,
        false,
        None,
        if uses_decreases_by {
            PostConditionKind::DecreasesBy
        } else {
            PostConditionKind::DecreasesImplicitLemma
        },
    )?;

    assert_eq!(commands.len(), 1);
    let commands = commands.into_iter().next().unwrap().commands.clone();

    // New body: substitute rec%f(args, fuel) for f(args)
    let body = map_exp_visitor(&body, &mut |exp| match &exp.x {
        ExpX::Call(CallFun::Fun(x, resolved_method), typs, args)
            if is_recursive_call(&ctxt, x, resolved_method) && ctx.func_map[x].x.body.is_some() =>
        {
            let mut args = (**args).clone();
            let varx = ExpX::Var(unique_local(&str_ident(FUEL_PARAM)));
            let var_typ = Arc::new(TypX::Air(str_typ(FUEL_TYPE)));
            args.push(SpannedTyped::new(&exp.span, &var_typ, varx));
            let callx =
                ExpX::Call(CallFun::CheckTermination(x.clone()), typs.clone(), Arc::new(args));
            SpannedTyped::new(&exp.span, &exp.typ, callx)
        }
        _ => exp.clone(),
    });

    Ok((true, commands, body))
}

pub(crate) fn check_termination_stm(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
    body: &Stm,
) -> Result<(Vec<LocalDecl>, Stm), VirErr> {
    if !is_recursive_stm(ctx, &function.x.name, body) {
        return Ok((vec![], body.clone()));
    }
    let num_decreases = function.x.decrease.len();
    if num_decreases == 0 {
        return error(&function.span, "recursive function must have a decreases clause");
    }

    let decreases_exps = vec_map_result(&function.x.decrease, |e| {
        expr_to_exp(ctx, diagnostics, fun_ssts, &params_to_pars(&function.x.params, true), e)
    })?;
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&Node::Fun(function.x.name.clone()));
    let ctxt =
        Ctxt { recursive_function_name: function.x.name.clone(), num_decreases, scc_rep, ctx };
    let stm = map_stm_visitor(body, &mut |s| match &s.x {
        StmX::Call { fun, resolved_method, args, .. }
            if is_recursive_call(&ctxt, fun, resolved_method) =>
        {
            let check = check_decrease_call(
                &ctxt,
                diagnostics,
                fun_ssts,
                &s.span,
                fun,
                resolved_method,
                args,
            )?;
            let error = msg_error("could not prove termination", &s.span);
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
    call_graph: &mut Graph<Node>,
    function: &Function,
) -> Result<(), VirErr> {
    // See recursive_types::check_traits for more documentation
    let f_node = Node::Fun(function.x.name.clone());

    // Add D: T --> f and D: T --> T where f is one of D's methods that implements T
    if let FunctionKind::TraitMethodImpl { trait_path, self_typ, .. } = function.x.kind.clone() {
        let t_node = Node::Trait(trait_path.clone());
        let dt_node = Node::DatatypeTraitBound { self_typ, trait_path };
        call_graph.add_edge(dt_node.clone(), t_node);
        call_graph.add_edge(dt_node, f_node.clone());
    }

    // Add f --> T for any function f<A: T> with type parameter A: T
    for (_, tbound) in function.x.typ_bounds.iter() {
        let GenericBoundX::Traits(traits) = &**tbound;
        for tr in traits {
            call_graph.add_edge(f_node.clone(), Node::Trait(tr.clone()));
        }
    }

    // Add f --> fd if fd is the decreases proof for f's definition
    if let Some(decrease_by) = &function.x.decrease_by {
        call_graph.add_edge(f_node.clone(), Node::Fun(decrease_by.clone()))
    }

    // Add f --> f2 edges where f calls f2
    // Add f --> D: T where one of f's expressions instantiates A: T with D: T
    // Add T --> f2 if the requires/ensures of T's method declarations call f2
    crate::ast_visitor::function_visitor_check::<VirErr, _>(function, &mut |expr| {
        match &expr.x {
            ExprX::Call(CallTarget::Fun(kind, x, ts, autospec), _) => {
                assert!(*autospec == AutospecUsage::Final);

                use crate::ast::CallTargetKind;
                let f2 = &func_map[x];
                assert!(f2.x.typ_bounds.len() == ts.len());
                let mut t_param_args = f2.x.typ_bounds.iter().zip(ts.iter());
                let callee =
                    if let FunctionKind::TraitMethodDecl { trait_path: trait_path2 } = &f2.x.kind {
                        let (tparam, t_self_arg) = t_param_args.next().expect("method Self type");
                        assert!(tparam.0 == crate::def::trait_self_type_param());
                        match (kind, &**t_self_arg) {
                            (CallTargetKind::Static, _) => panic!("expected Method"),
                            // If the Self type argument is a concrete type,
                            // then we should know concretely which function we're calling.
                            // We rely on rustc to resolve this case to Method(Some(x)):
                            (CallTargetKind::Method(Some((x, _))), _) => Some(x),
                            // By contrast, if the Self type argument is a type parameter,
                            // then we don't know concretely which function we're calling;
                            // conceptually, we're looking up the function dynamically in
                            // a dictionary.
                            // (Note that the dictionary is passed in with the type parameter;
                            // if there's no type parameter, there's no dictionary,
                            // so we can only use the dictionary in the type parameter case.)
                            (_, TypX::TypParam(p)) if p == &crate::def::trait_self_type_param() => {
                                match &function.x.kind {
                                    FunctionKind::TraitMethodDecl { trait_path: trait_path1 }
                                        if trait_path1 == trait_path2 =>
                                    {
                                        // Call to self within trait, T.f --> T.f2
                                        // (We can't use the dictionary in case, because the
                                        // dictionary is still under construction.)
                                        Some(x)
                                    }
                                    _ => {
                                        return error(&expr.span, "unsupported use of Self type");
                                    }
                                }
                            }
                            (_, TypX::TypParam(p)) => {
                                // no f --> f2 edge for calls via a type parameter A: T,
                                // because we (conceptually) get f2 from the dictionary passed for A: T.
                                let bound = function.x.typ_bounds.iter().find(|(q, _)| q == p);
                                let bound = bound.expect("missing type parameter");
                                let GenericBoundX::Traits(ts) = &*bound.1;
                                assert!(ts.iter().any(|t| t == trait_path2));
                                None
                            }
                            _ => panic!("unexpected Self type instantiation"),
                        }
                    } else {
                        assert!(matches!(kind, CallTargetKind::Static));
                        Some(x)
                    };

                for ((_, tbound), targ) in t_param_args {
                    // For each instantiation of a callee type parameter,
                    // if the type parameter has a bound,
                    // we need to pass in the right dictionary.
                    // (Note: we don't need to consider the Self instantiation here,
                    // because if the Self argument is a type parameter X,
                    // there's nothing to do (see TypParam case below),
                    // and if Self is concrete, we conceptually make a direct call with no
                    // need for a Self argument (see the callee selection code above).)
                    match &**tbound {
                        GenericBoundX::Traits(traits) => {
                            for tr in traits {
                                match &**targ {
                                    TypX::TypParam(..) => {
                                        // We already have the dictionaries for type parameters,
                                        // so nothing else needs to happen here.
                                    }
                                    _ => {
                                        // f --> D: T
                                        call_graph.add_edge(
                                            f_node.clone(),
                                            Node::DatatypeTraitBound {
                                                self_typ: targ.clone(),
                                                trait_path: tr.clone(),
                                            },
                                        );
                                    }
                                }
                            }
                        }
                    }
                }

                if let FunctionKind::TraitMethodDecl { trait_path } = &function.x.kind {
                    // T --> f2
                    call_graph.add_edge(Node::Trait(trait_path.clone()), Node::Fun(x.clone()));
                    if let Some(callee) = callee {
                        call_graph
                            .add_edge(Node::Trait(trait_path.clone()), Node::Fun(callee.clone()));
                    }
                }

                // f --> f2
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
