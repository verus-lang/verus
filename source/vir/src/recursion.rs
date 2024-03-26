use crate::ast::{
    AutospecUsage, CallTarget, CallTargetKind, Constant, ExprX, Fun, Function, FunctionKind,
    GenericBoundX, ImplPath, IntRange, Path, SpannedTyped, Typ, TypX, Typs, UnaryOpr, VarBinder,
    VirErr,
};
use crate::ast_to_sst::expr_to_exp_skip_checks;
use crate::ast_util::{air_unique_var, ident_var_binder, typ_to_diagnostic_str};
use crate::context::Ctx;
use crate::def::{
    decrease_at_entry, rename_rec_param, unique_bound, unique_local, CommandsWithContext, Spanned,
    FUEL_PARAM, FUEL_TYPE,
};
use crate::func_to_air::{params_to_pars, SstMap};
use crate::inv_masks::MaskSet;
use crate::messages::{error, Span};
use crate::scc::Graph;
use crate::sst::PostConditionKind;
use crate::sst::PostConditionSst;
use crate::sst::{
    BndX, CallFun, Dest, Exp, ExpX, Exps, FunctionSst, InternalFun, LocalDecl, LocalDeclX, Stm,
    StmX, UniqueIdent,
};
use crate::sst_visitor::{exp_rename_vars, map_exp_visitor, map_stm_visitor};
use crate::util::vec_map_result;
use air::ast_util::str_typ;
use air::messages::Diagnostics;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node {
    Fun(Fun),
    Datatype(Path),
    Trait(Path),
    TraitImpl(ImplPath),
    // This is used to replace an X --> Y edge with X --> SpanInfo --> Y edges
    // to give more precise span information than X or Y alone provide
    SpanInfo { span_infos_index: usize, text: String },
}

#[derive(Clone)]
struct Ctxt<'a> {
    recursive_function_name: Fun,
    num_decreases: usize,
    scc_rep: Node,
    ctx: &'a Ctx,
}

pub(crate) fn get_callee(
    ctx: &Ctx,
    target: &Fun,
    resolved_method: &Option<(Fun, Typs)>,
) -> Option<Fun> {
    let fun = &ctx.func_map[target];
    if let FunctionKind::TraitMethodDecl { .. } = &fun.x.kind {
        resolved_method.clone().map(|(x, _)| x)
    } else {
        Some(target.clone())
    }
}

fn is_recursive_call(ctxt: &Ctxt, target: &Fun, resolved_method: &Option<(Fun, Typs)>) -> bool {
    if let Some(callee) = get_callee(ctxt.ctx, target, resolved_method) {
        let callee_node = Node::Fun(callee.clone());
        callee == ctxt.recursive_function_name
            || ctxt.ctx.global.func_call_graph.get_scc_rep(&callee_node) == ctxt.scc_rep
    } else {
        false
    }
}

pub fn height_is_int(typ: &Typ) -> bool {
    match &*crate::ast_util::undecorate_typ(typ) {
        TypX::Int(_) => true,
        _ => false,
    }
}

fn height_typ(ctxt: &Ctxt, exp: &Exp) -> Typ {
    if height_is_int(&exp.typ) {
        Arc::new(TypX::Int(IntRange::Int))
    } else {
        if crate::poly::typ_is_poly(ctxt.ctx, &exp.typ) {
            exp.typ.clone()
        } else {
            Arc::new(TypX::Boxed(exp.typ.clone()))
        }
    }
}

fn exp_for_decrease(ctxt: &Ctxt, exp: &Exp) -> Result<Exp, VirErr> {
    match &*crate::ast_util::undecorate_typ(&exp.typ) {
        TypX::Int(_) => Ok(exp.clone()),
        TypX::Datatype(..) => Ok(if crate::poly::typ_is_poly(ctxt.ctx, &exp.typ) {
            exp.clone()
        } else {
            let op = UnaryOpr::Box(exp.typ.clone());
            let argx = ExpX::UnaryOpr(op, exp.clone());
            let typ = Arc::new(TypX::Boxed(exp.typ.clone()));
            SpannedTyped::new(&exp.span, &typ, argx)
        }),
        _ => Err(error(
            &exp.span,
            format!(
                "internal error: unsupported type for decreases {}",
                typ_to_diagnostic_str(&exp.typ)
            ),
        )),
    }
}

fn check_decrease(ctxt: &Ctxt, span: &Span, exps: &Vec<Exp>) -> Result<Exp, VirErr> {
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
            SpannedTyped::new(&exp.span, &height_typ(ctxt, exp), decreases_at_entryx);
        // 0 <= decreases_exp < decreases_at_entry
        let args = vec![exp_for_decrease(ctxt, exp)?, decreases_at_entry, dec_exp];
        let call = ExpX::Call(
            if height_is_int(&exp.typ) {
                CallFun::InternalFun(InternalFun::CheckDecreaseInt)
            } else {
                CallFun::InternalFun(InternalFun::CheckDecreaseHeight)
            },
            Arc::new(vec![]),
            Arc::new(args),
        );
        dec_exp = SpannedTyped::new(&exp.span, &Arc::new(TypX::Bool), call);
    }
    Ok(dec_exp)
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
    let binders: Vec<VarBinder<Exp>> = params
        .iter()
        .zip(args.iter())
        .enumerate()
        .map(|(n, (param, arg))| {
            ident_var_binder(&rename_rec_param(&param.x.name, n), &arg.clone())
        })
        .collect();
    let renames: HashMap<UniqueIdent, UniqueIdent> = params
        .iter()
        .enumerate()
        .map(|(n, param)| {
            (unique_local(&param.x.name), unique_bound(&rename_rec_param(&param.x.name, n)))
        })
        .collect();
    let mut decreases_exps: Vec<Exp> = Vec::new();
    for expr in function.x.decrease.iter() {
        // use expr_to_exp_skip_checks here because checks in decreases done by func_def_to_air
        let decreases_exp = expr_to_exp_skip_checks(
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
    check_decrease(ctxt, span, &decreases_exps)
}

pub(crate) fn fun_is_recursive(ctx: &Ctx, function: &Function) -> bool {
    let name = &function.x.name;
    let node = Node::Fun(name.clone());
    ctx.global.func_call_graph.node_is_in_cycle(&node)
}

fn mk_decreases_at_entry(
    ctxt: &Ctxt,
    span: &Span,
    exps: &Vec<Exp>,
) -> Result<(Vec<LocalDecl>, Vec<Stm>), VirErr> {
    let mut decls: Vec<LocalDecl> = Vec::new();
    let mut stm_assigns: Vec<Stm> = Vec::new();
    for (i, exp) in exps.iter().enumerate() {
        let typ = height_typ(ctxt, exp);
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
                rhs: exp_for_decrease(ctxt, exp)?,
            },
        );
        decls.push(decl);
        stm_assigns.push(stm_assign);
    }
    Ok((decls, stm_assigns))
}

/// fuel param:
/// `None` for normal case (the usual 'fuel' param)
/// `Some(fuel)` means use a constant fuel
pub(crate) fn rewrite_recursive_fun_with_fueled_rec_call(
    ctx: &Ctx,
    function: &Function,
    body: &Exp,
    fuel: Option<usize>,
) -> Result<(bool, Exp, crate::recursion::Node), VirErr> {
    let caller_node = Node::Fun(function.x.name.clone());
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&caller_node);
    if !fun_is_recursive(ctx, function) {
        return Ok((false, body.clone(), scc_rep));
    }
    let num_decreases = function.x.decrease.len();
    if num_decreases == 0 {
        return Err(error(&function.span, "recursive function must have a decreases clause"));
    }
    let ctxt = Ctxt {
        recursive_function_name: function.x.name.clone(),
        num_decreases,
        scc_rep: scc_rep.clone(),
        ctx,
    };

    // New body: substitute rec%f(args, fuel) for f(args)
    let body = map_exp_visitor(&body, &mut |exp| match &exp.x {
        ExpX::Call(CallFun::Fun(x, resolved_method), typs, args)
            if is_recursive_call(&ctxt, x, resolved_method) && ctx.func_map[x].x.body.is_some() =>
        {
            let mut args = (**args).clone();
            let varx = match fuel {
                None => ExpX::Var(unique_local(&&air_unique_var(FUEL_PARAM))),
                Some(f) => ExpX::FuelConst(f),
            };
            let var_typ = Arc::new(TypX::Air(str_typ(FUEL_TYPE)));
            args.push(SpannedTyped::new(&exp.span, &var_typ, varx));
            let callx = ExpX::Call(CallFun::Recursive(x.clone()), typs.clone(), Arc::new(args));
            SpannedTyped::new(&exp.span, &exp.typ, callx)
        }
        _ => exp.clone(),
    });

    Ok((true, body, scc_rep))
}

pub(crate) fn check_termination_commands(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
    mut local_decls: Vec<LocalDecl>,
    proof_body: Stm,
    body: &Stm,
    uses_decreases_by: bool,
) -> Result<Vec<CommandsWithContext>, VirErr> {
    if !fun_is_recursive(ctx, function) {
        return Ok(vec![]);
    }

    let (ctxt, decreases_exps, stm) =
        check_termination(ctx, diagnostics, fun_ssts, function, body)?;

    let (mut decls, mut stm_assigns) = mk_decreases_at_entry(&ctxt, &body.span, &decreases_exps)?;
    stm_assigns.push(proof_body);
    stm_assigns.push(stm.clone());
    let stm_block = Spanned::new(body.span.clone(), StmX::Block(Arc::new(stm_assigns)));

    // TODO: If we decide to support debugging decreases failures, we should plumb _snap_map
    // up to the VIR model
    local_decls.append(&mut decls);
    let (commands, _snap_map) = crate::sst_to_air::body_stm_to_air(
        ctx,
        &function.span,
        &function.x.typ_params,
        &function.x.params,
        &FunctionSst {
            post_condition: PostConditionSst {
                dest: None,
                kind: if uses_decreases_by {
                    PostConditionKind::DecreasesBy
                } else {
                    PostConditionKind::DecreasesImplicitLemma
                },
                ens_exps: vec![],
                ens_spec_precondition_stms: vec![],
            },
            body: stm_block,
            local_decls,
            statics: vec![],
            reqs: Arc::new(vec![]),
            mask_set: MaskSet::empty(),
        },
        &vec![],
        false,
        false,
        false,
    )?;

    Ok(commands)
}

fn check_termination<'a>(
    ctx: &'a Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
    body: &Stm,
) -> Result<(Ctxt<'a>, Vec<Exp>, Stm), VirErr> {
    let num_decreases = function.x.decrease.len();
    if num_decreases == 0 {
        return Err(error(&function.span, "recursive function must have a decreases clause"));
    }

    // use expr_to_exp_skip_checks here because checks in decreases done by func_def_to_air
    let decreases_exps = vec_map_result(&function.x.decrease, |e| {
        expr_to_exp_skip_checks(
            ctx,
            diagnostics,
            fun_ssts,
            &params_to_pars(&function.x.params, true),
            e,
        )
    })?;
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&Node::Fun(function.x.name.clone()));
    let ctxt =
        Ctxt { recursive_function_name: function.x.name.clone(), num_decreases, scc_rep, ctx };
    let stm = map_stm_visitor(body, &mut |s| match &s.x {
        StmX::Call { fun, resolved_method, args, dest, .. }
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
            let error = error(&s.span, "could not prove termination");
            let stm_assert = Spanned::new(s.span.clone(), StmX::Assert(None, Some(error), check));

            let mut stms = vec![stm_assert];
            // REVIEW: when we support spec-ensures, we will need an assume here to get the ensures
            // of the recursive call just after it was proven to terminate
            // This is instead an interim fix for incompleteness in recommends checking, due to
            // the fact that we currently do not emit AIR calls to a spec function in the same SCC.
            // Even if we _did_ emit AIR calls to spec functions in the same SCC, they would be
            // uninterpreted, because the function definition axioms must be emitted later (so
            // they cannot be used to prove their own termination).
            // Because of this, the call's destination remains uninitialized, and lacks its typing
            // invariant, causeing imcompleteness (issue #564).
            // It _might_ be sound to emit just the functions' typing invariants first,
            // but we are not sure. So, as a partial fix for (some of) the resulting incompleteness),
            // we manually emit an assume with just the typing invariant of the destination.
            // It may be okay to emit this for non-spec functions too, but I have not checked, so
            // I'm restricting this to spec functions for now.
            if ctx.func_map[fun].x.mode == crate::ast::Mode::Spec {
                if let Some(Dest { dest, is_init: true }) = &dest {
                    let has_typx =
                        ExpX::UnaryOpr(UnaryOpr::HasType(dest.typ.clone()), dest.clone());
                    let has_typ = SpannedTyped::new(&s.span, &Arc::new(TypX::Bool), has_typx);
                    let has_typ_assume = Spanned::new(s.span.clone(), StmX::Assume(has_typ));
                    stms.push(has_typ_assume);
                }
            }
            stms.push(s.clone());
            let stm_block = Spanned::new(s.span.clone(), StmX::Block(Arc::new(stms)));
            Ok(stm_block)
        }
        StmX::Fuel(callee, fuel) if *fuel >= 1 => {
            let f2 = &ctx.func_map[callee];
            if f2.x.attrs.broadcast_forall && is_recursive_call(&ctxt, callee, &None) {
                // This isn't needed for soundness, since the broadcast_forall axiom isn't
                // declared until after this SCC, but we might as well signal an error,
                // since this reveal will have no effect.
                return Err(error(&s.span, "cannot recursively reveal broadcast_forall"));
            }
            Ok(s.clone())
        }
        _ => Ok(s.clone()),
    })?;
    Ok((ctxt, decreases_exps, stm))
}

pub(crate) fn check_termination_stm(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
    body: &Stm,
) -> Result<(Vec<LocalDecl>, Stm), VirErr> {
    if !fun_is_recursive(ctx, &function) {
        return Ok((vec![], body.clone()));
    }

    let (ctxt, decreases_exps, stm) =
        check_termination(ctx, diagnostics, fun_ssts, function, body)?;

    let (decls, mut stm_assigns) = mk_decreases_at_entry(&ctxt, &stm.span, &decreases_exps)?;
    stm_assigns.push(stm.clone());
    let stm_block = Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stm_assigns)));
    Ok((decls, stm_block))
}

pub(crate) fn expand_call_graph(
    func_map: &HashMap<Fun, Function>,
    trait_impl_map: &HashMap<(Fun, Path), Fun>,
    call_graph: &mut Graph<Node>,
    span_infos: &mut Vec<Span>,
    function: &Function,
) -> Result<(), VirErr> {
    // See recursive_types::check_traits for more documentation
    let f_node = Node::Fun(function.x.name.clone());

    // Add T --> f if T declares method f
    if let FunctionKind::TraitMethodDecl { trait_path } = &function.x.kind {
        // T --> f
        call_graph.add_edge(Node::Trait(trait_path.clone()), f_node.clone());
    }

    // Add D: T --> f and f --> T where f is one of D's methods that implements T
    if let FunctionKind::TraitMethodImpl { trait_path, impl_path, .. } = function.x.kind.clone() {
        let t_node = Node::Trait(trait_path.clone());
        let impl_node = Node::TraitImpl(ImplPath::TraitImplPath(impl_path.clone()));
        call_graph.add_edge(impl_node, f_node.clone());
        call_graph.add_edge(f_node.clone(), t_node);
    }

    // Add f --> T for any function f with "where ...: T(...)"
    for bound in function.x.typ_bounds.iter() {
        if let FunctionKind::TraitMethodDecl { trait_path } = &function.x.kind {
            if crate::recursive_types::suppress_bound_in_trait_decl(
                &trait_path,
                &function.x.typ_params,
                bound,
            ) {
                continue;
            }
        }
        let GenericBoundX::Trait(tr, _) = &**bound;
        call_graph.add_edge(f_node.clone(), Node::Trait(tr.clone()));
    }

    // Add f --> fd if fd is the decreases proof for f's definition
    if let Some(decrease_by) = &function.x.decrease_by {
        call_graph.add_edge(f_node.clone(), Node::Fun(decrease_by.clone()))
    }

    // Add f --> f2 edges where f calls f2
    // Add f --> D: T where one of f's expressions instantiates A: T with D: T
    //
    // When instantiating A: T with D: T, note that D: T could, from Rust's perspective,
    // be the Self: T bound that we remove (see the comments in recursive_types.rs) and
    // that therefore shouldn't be available here.  Fortunately, in this case,
    // rustc gives us the concrete D: T bound for the actual impl, so that
    // impl_paths contains the necessary impl_path to instantiate Self: T explicitly,
    // and we catch the nontermination resulting from Self: T.
    // See, for example, test_termination_1 in rust_verify_test/tests/traits.rs.
    //
    // However, for default methods, rustc does not provide the impl_path to us,
    // and we use a different way of catching uses of Self: T.
    // Specifically, we make sure there is an edge in the call graph from T to the
    // T's default methods, and any attempt by a default method to use Self: T
    // (say, when calling a function f<A: T>) will create an edge to someone who
    // uses T (in this example, f), which then creates a cycle that is reported as an error.
    // (See, for example, test_default14 in rust_verify_test/tests/traits.rs.)
    // The one exception to this is when a default method of T calls another default method of T;
    // this is not considered a cycle through T, but instead is treated as ordinary recursion.
    // (See, for example, test_default17 in rust_verify_test/tests/traits.rs.)
    let add_calls = &mut |expr: &crate::ast::Expr| {
        match &expr.x {
            ExprX::Call(CallTarget::Fun(kind, x, ts, impl_paths, autospec), _) => {
                assert!(*autospec == AutospecUsage::Final);
                let (callee, ts, impl_paths) =
                    if let CallTargetKind::Method(Some((x_resolved, ts_resolved, x_impl_paths))) =
                        kind
                    {
                        (x_resolved.clone(), ts_resolved.clone(), x_impl_paths.clone())
                    } else {
                        (x.clone(), ts.clone(), impl_paths.clone())
                    };

                let (callee, impl_paths) = crate::traits::redirect_calls_in_default_methods(
                    func_map,
                    trait_impl_map,
                    function,
                    &expr.span,
                    callee,
                    ts,
                    impl_paths,
                )?;

                for impl_path in impl_paths.iter() {
                    // f --> D: T
                    let expr_node = crate::recursive_types::new_span_info_node(
                        span_infos,
                        expr.span.clone(),
                        ": application of a function to some type arguments, which may depend on \
                            other trait implementations to satisfy trait bounds"
                            .to_string(),
                    );
                    call_graph.add_edge(f_node.clone(), expr_node.clone());
                    call_graph.add_edge(expr_node.clone(), Node::TraitImpl(impl_path.clone()));
                }

                // f --> f2
                call_graph.add_edge(f_node.clone(), Node::Fun(callee.clone()))
            }
            ExprX::ConstVar(callee, _) => {
                call_graph.add_edge(f_node.clone(), Node::Fun(callee.clone()))
            }
            ExprX::Call(CallTarget::BuiltinSpecFun(_bsf, _typs, impl_paths), _) => {
                for impl_path in impl_paths.iter() {
                    call_graph.add_edge(f_node.clone(), Node::TraitImpl(impl_path.clone()));
                }
            }
            ExprX::Fuel(callee, fuel) if *fuel >= 1 => {
                let f2 = &func_map[callee];
                if f2.x.attrs.broadcast_forall {
                    // f --> f2
                    call_graph.add_edge(f_node.clone(), Node::Fun(callee.clone()))
                }
            }
            ExprX::StaticVar(fun) => call_graph.add_edge(f_node.clone(), Node::Fun(fun.clone())),
            _ => {}
        }
        Ok(())
    };
    crate::ast_visitor::function_visitor_check::<VirErr, _>(function, add_calls)?;
    if let FunctionKind::TraitMethodImpl { inherit_body_from: Some(f_trait), .. } = &function.x.kind
    {
        crate::ast_visitor::function_visitor_check::<VirErr, _>(&func_map[f_trait], add_calls)?;
    }

    for fun in &function.x.extra_dependencies {
        call_graph.add_edge(f_node.clone(), Node::Fun(fun.clone()));
    }

    Ok(())
}
