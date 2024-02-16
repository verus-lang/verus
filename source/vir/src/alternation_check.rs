use std::collections::{HashMap, HashSet};

use air::scope_map::ScopeMap;
use ast_visitor::VisitorControlFlow;

use crate::{
    ast::{
        Expr, Fun, FunctionX, Idents, Krate, Mode, Param, Params, Path, Typ, TypX, Typs, VirErr,
    },
    ast_util::{path_as_friendly_rust_name, undecorate_typ},
    ast_visitor::{self, expr_visitor_dfs},
    context::Ctx,
    messages::error,
    scc::Graph,
};

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
struct FunBounds {
    fun: Fun,
    typs: Vec<String>,
}

impl FunBounds {
    fn print_name(&self) -> String {
        let mut res = path_as_friendly_rust_name(&self.fun.path);
        if self.typs.len() > 0 {
            res.push_str("<");
            for typ in &self.typs {
                res.push_str(&format!("{},", typ));
            }
            res.push_str(">");
        }
        res
    }
}

const DEBUG: bool = false;

struct CollectState {
    reached_spec_funcs: HashSet<FunBounds>,
}

impl CollectState {
    fn new() -> Self {
        CollectState { reached_spec_funcs: HashSet::new() }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
/// Positive if an encountered quantifier can be interpreted directly,
/// Negative if it needs to be swapped (i.e. under negation)
enum Polarity {
    Positive,
    Negative,
}

impl Polarity {
    fn flip(&self) -> Polarity {
        match self {
            Polarity::Negative => Polarity::Positive,
            Polarity::Positive => Polarity::Negative,
        }
    }
}

struct BuildState {
    /// the quantifier alternation graph that this pass is trying to build
    qa_graph: Graph<String>,
    /// currently outstanding variables
    /// u64 keeps count so that we can decrement and not lose typs on returning
    open_foralls: HashMap<String, u64>,
}

impl BuildState {
    fn new() -> Self {
        BuildState { qa_graph: Graph::<String>::new(), open_foralls: HashMap::new() }
    }

    fn add_function_edges(
        &mut self,
        params: &Params,
        ret: &Param,
        bindings: &HashMap<String, String>,
    ) {
        let ret_node = param_type_name_with_bindings(&ret.x.typ, bindings);
        for param in params.iter() {
            let param_node = param_type_name_with_bindings(&param.x.typ, bindings);
            if DEBUG {
                println!("Adding Func Edge: {} -> {}", &param_node, &ret_node);
            }
            self.qa_graph.add_edge(param_node, ret_node.clone());
        }
    }

    fn empty_foralls(&self) -> bool {
        self.open_foralls.iter().all(|(_, count)| *count == 0)
    }
}

fn param_type_name(typ: &Typ) -> String {
    // TODO: support for FnSpec
    match &*undecorate_typ(typ) {
        TypX::Bool => "Bool".to_string(),
        TypX::Datatype(path, _, _) => path_as_friendly_rust_name(path),
        // TODO: Double check templating rules for QA Graph
        TypX::TypParam(name) => name.to_string(),
        _ => panic!("Unsupported EPR Type: {:?}", &*undecorate_typ(typ)),
    }
}

fn param_type_name_with_bindings(typ: &Typ, bindings: &HashMap<String, String>) -> String {
    match &*undecorate_typ(typ) {
        TypX::Bool => "Bool".to_string(),
        TypX::Datatype(path, typs, _) => {
            let mut name = path_as_friendly_rust_name(path);
            if typs.len() > 0 {
                name.push_str("<");
                for t in typs.iter() {
                    assert!(matches!(&*undecorate_typ(t), TypX::TypParam(_)));
                    name.push_str(&param_type_name_with_bindings(t, bindings));
                    name.push_str(",");
                }
                name.push_str(">");
            }
            name
        }
        TypX::TypParam(name) => bindings.get(name.as_ref()).unwrap().to_string(),
        _ => panic!("Unsupported EPR Type: {:?}", &*undecorate_typ(typ)),
    }
}

fn compute_new_bindings(
    fun: &Fun,
    orig_types: &Idents,
    bound_types: Typs,
    curr_bindings: &HashMap<String, String>,
) -> (FunBounds, HashMap<String, String>) {
    assert!(orig_types.len() == bound_types.len());
    let orig_typ_names: Vec<String> = orig_types.iter().map(|x| x.as_ref()).cloned().collect();
    let bound_typ_names: Vec<String> = bound_types.iter().map(|x| param_type_name(x)).collect();
    // look at/update the active_param_typs
    let mut final_typ_names = Vec::new();
    let mut new_bindings = curr_bindings.clone();
    for (orig, bound) in orig_typ_names.iter().zip(bound_typ_names.iter()) {
        let final_typ = curr_bindings.get(bound).unwrap_or(bound);
        final_typ_names.push(final_typ.clone());
        new_bindings.insert(orig.clone(), final_typ.clone());
    }

    let fb = FunBounds { fun: fun.clone(), typs: final_typ_names };
    (fb, new_bindings)
}

pub fn alternation_check(ctx: &Ctx, krate: &Krate, module: Path) -> Result<(), VirErr> {
    fn collect_functions(
        ctx: &Ctx,
        state: &mut CollectState,
        expr: &Expr,
        active_param_typs: &HashMap<String, String>,
    ) -> Result<(), VirErr> {
        use crate::ast::ExprX::*;
        expr_visitor_dfs::<VirErr, _>(expr, &mut ScopeMap::new(), &mut |_, expr| match &expr.x {
            Call(target, exprs) => match target {
                crate::ast::CallTarget::Fun(call_target_kind, fun, typs, impl_paths, _) => {
                    // typs here are the actual types of the arguments, not the type params
                    if impl_paths.len() > 0 {
                        VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
                    } else {
                        if let Some(fun) = match call_target_kind {
                            crate::ast::CallTargetKind::Static => Some(fun),
                            crate::ast::CallTargetKind::Method(Some((fun, _, impl_paths))) => {
                                if impl_paths.len() > 0 {
                                    None
                                } else {
                                    Some(fun)
                                }
                            }
                            crate::ast::CallTargetKind::Method(None) => None,
                        } {
                            let f = &ctx.func_map[fun];
                            let (fb, new_active_param_typs) = compute_new_bindings(fun, &f.x.typ_params, typs.clone(), &active_param_typs);
                            // iterate through expressions in arguments
                            for expr in exprs.iter() {
                                match collect_functions(ctx, state, expr, &new_active_param_typs) {
                                    Ok(_) => (),
                                    Err(err) => return VisitorControlFlow::Stop(err),
                                }
                            }
                            // we've seen this function; add it to our list
                            match f.x.mode {
                                Mode::Spec => {
                                    // if the function is inlined, don't add it to reached set. 
                                    // Instead, save it to inline spec funcs to learn bindings
                                    if !f.x.attrs.inline {
                                        if DEBUG {
                                            println!("Reached Spec Fn: {}", fb.print_name());
                                        }
                                        state.reached_spec_funcs.insert(fb);
                                    }
                                    // if it has a body, recurse
                                    if let Some(f_body) = &f.x.body {
                                        match collect_functions(ctx, state, f_body, &new_active_param_typs) {
                                            Ok(_) => VisitorControlFlow::Return,
                                            Err(err) => VisitorControlFlow::Stop(err),
                                        }
                                    } else {
                                        VisitorControlFlow::Return
                                    }
                                }
                                Mode::Proof => {
                                    // parse ensures and requires recursively
                                    for r in f.x.require.iter() {
                                        match collect_functions(ctx, state, r, &new_active_param_typs) {
                                            Ok(_) => (),
                                            Err(err) => return VisitorControlFlow::Stop(err),
                                        }
                                    }
                                    for e in f.x.ensure.iter() {
                                        match collect_functions(ctx, state, e, &new_active_param_typs) {
                                            Ok(_) => (),
                                            Err(err) => return VisitorControlFlow::Stop(err),
                                        }
                                    }
                                    VisitorControlFlow::Return
                                }
                                Mode::Exec => {
                                    VisitorControlFlow::Stop(error(&expr.span, "exec calls are not supported in the EPR fragment"))
                                }
                            }

                        } else {
                            VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
                        }
                    }
                }
                crate::ast::CallTarget::FnSpec(_) |
                crate::ast::CallTarget::BuiltinSpecFun(_, _) => VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
            }
            Unary(..) |
            Quant(..) |
            Choose { .. } |
            UnaryOpr(..) |
            Binary(..) |
            BinaryOpr(..) |
            Loc(..) |
            Tuple(..) |
            Ctor(..) |
            Multi(..) |
            WithTriggers { .. } |
            Assign { .. } |
            AssertAssume { .. } |
            If(..) |
            Match(..) |
            Loop { .. } |
            Return(..) |
            Ghost { .. } |
            Block(..) => VisitorControlFlow::Recurse,

            Const(_) |
            Var(_) |
            VarLoc(_) |
            VarAt(_, _) |
            ConstVar(_, _) |
            StaticVar(_) |
            Fuel(_, _) |
            Header(_) |
            BreakOrContinue { .. } => VisitorControlFlow::Return,

            Closure(_, _) | // TODO: maybe supported down the line?
            NullaryOpr(..) |
            ExecClosure { .. } |
            AssertBy { .. } |
            AssertQuery { .. } |
            AssertCompute(..) |
            RevealString(..) |
            OpenInvariant(..) => VisitorControlFlow::Stop(error(&expr.span, "unsupported in EPR fragment")),
        });
        Ok(())
    }
    fn build_graph(
        ctx: &Ctx,
        state: &mut BuildState,
        polarity: Polarity,
        bindings: Option<&HashMap<String, String>>,
        expr: &Expr,
    ) -> Result<(), VirErr> {
        use crate::ast::ExprX::*;
        expr_visitor_dfs::<VirErr, _>(expr, &mut ScopeMap::new(), &mut |_, expr| match &expr.x {
            Unary(op, e) => match op {
                crate::ast::UnaryOp::Not => {
                    match build_graph(ctx, state, polarity.flip(), bindings, e) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                },
                _ => VisitorControlFlow::Recurse,
            },
            Quant(op, binders, e) => {
                let forall = (matches!(polarity, Polarity::Positive) && matches!(op.quant, air::ast::Quant::Forall))
                                || (matches!(polarity, Polarity::Negative) && matches!(op.quant, air::ast::Quant::Exists));
                if forall {
                    // forall case: add the new variables to open foralls, then recurse
                    for b in binders.iter() {
                        let typ_name = match bindings {
                            Some(bind) => param_type_name_with_bindings(&b.a, bind),
                            None => param_type_name(&b.a),
                        };
                        *state.open_foralls.entry(typ_name.clone()).or_insert(0) += 1;
                    }
                    match build_graph(ctx, state, polarity, bindings, e) {
                        Ok(_) => {
                            for b in binders.iter() {
                                let typ_name = match bindings {
                                    Some(bind) => param_type_name_with_bindings(&b.a, bind),
                                    None => param_type_name(&b.a),
                                };
                                let cur_count = state.open_foralls.get_mut(&typ_name).expect("should already have entry");
                                assert!(*cur_count >= 1);
                                *cur_count -= 1;
                            }
                            VisitorControlFlow::Return
                        },
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }

                } else {
                    // exists case: check through open foralls for edges to add, then recurse
                    for b in binders.iter() {
                        let typ_name = match bindings {
                            Some(bind) => param_type_name_with_bindings(&b.a, bind),
                            None => param_type_name(&b.a),
                        };
                        for (forall_name, count) in state.open_foralls.iter() {
                            // empty ones remain in the map with 0 count
                            if *count > 0 {
                                if DEBUG {
                                    println!("Adding QA Edge: {} -> {}", forall_name, &typ_name);
                                }
                                state.qa_graph.add_edge(forall_name.clone(), typ_name.clone());
                            }
                        }
                    }
                    match build_graph(ctx, state, polarity, bindings, e) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                }
            },
            Binary(op, left, right) => match op {
                crate::ast::BinaryOp::Implies => {
                    match {
                        // left is explored at opposite polarity
                        build_graph(ctx, state, polarity.flip(), bindings, left)
                    }.and({
                        // right is explored at same polarity
                        build_graph(ctx, state, polarity, bindings, right)
                    }) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }

                },
                // these operators introduce both polarities
                crate::ast::BinaryOp::Eq(_) |
                crate::ast::BinaryOp::Ne |
                crate::ast::BinaryOp::Xor => {
                    // TODO: Does Eq Mode matter?
                    if crate::ast_util::type_is_bool(&undecorate_typ(&left.typ)) {
                        match {
                            build_graph(ctx, state, Polarity::Positive, bindings, left)
                        }.and({
                            build_graph(ctx, state, Polarity::Negative, bindings, left)
                        }).and({
                            build_graph(ctx, state, Polarity::Positive, bindings, right)
                        }).and({
                            build_graph(ctx, state, Polarity::Negative, bindings, right)
                        }) {
                            Ok(_) => VisitorControlFlow::Return,
                            Err(err) => VisitorControlFlow::Stop(err),
                        }
                    } else {
                        VisitorControlFlow::Recurse
                    }
                },
                _ => VisitorControlFlow::Recurse,
            }
            // TODO: exprs here?
            Call(target, exprs) => match target {
                crate::ast::CallTarget::Fun(call_target_kind, fun, typs, impl_paths, _) => {
                    if impl_paths.len() > 0 {
                        VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
                    } else {
                        if let Some(fun) = match call_target_kind {
                            crate::ast::CallTargetKind::Static => Some(fun),
                            crate::ast::CallTargetKind::Method(Some((fun, _, impl_paths))) => {
                                if impl_paths.len() > 0 {
                                    None
                                } else {
                                    Some(fun)
                                }
                            }
                            crate::ast::CallTargetKind::Method(None) => None,
                        } {
                            for expr in exprs.iter() {
                                // explore the expression in both positive and negative polarities
                                // do this with original bindings, as we are in the context of the parent function.
                                match {
                                    build_graph(ctx, state, Polarity::Positive, bindings, expr)
                                }.and({
                                    build_graph(ctx, state, Polarity::Negative, bindings, expr)
                                }) {
                                    Ok(_) => (),
                                    Err(err) => return VisitorControlFlow::Stop(err),
                                }
                            }

                            let f = &ctx.func_map[fun];
                            let (_, new_bindings) = compute_new_bindings(fun, &f.x.typ_params, typs.clone(), &bindings.unwrap_or(&HashMap::new()));
                            match f.x.mode {
                                // spec funcs aren't recursed on second pass
                                Mode::Spec => {
                                    if f.x.attrs.inline {
                                        if let Some(body) = &f.x.body {
                                            // as we're inlining, the params don't contribute new foralls
                                            // simply recurse into the body at the same polarity
                                            match build_graph(ctx, state, polarity, Some(&new_bindings), body) {
                                                Ok(_) => VisitorControlFlow::Return,
                                                Err(err) => return VisitorControlFlow::Stop(err),
                                            }
                                        } else {
                                            VisitorControlFlow::Return
                                        }
                                    } else {
                                        // non-inline spec funcs aren't recursed on second pass
                                        VisitorControlFlow::Return
                                    }
                                }
                                Mode::Proof => {
                                    // should only be here when parsing the body of the lemma
                                    // params for a proof function don't get encoded as additional quantifiers
                                    // add the requires clause negatively, and the ensures positively
                                    match f.x.ensure.iter().fold(Ok(()), |acc,expr| {
                                        // shouldn't have any open foralls when invoking a lemma, afaik
                                        assert!(state.empty_foralls());
                                        acc.and(build_graph(ctx, state, Polarity::Positive, Some(&new_bindings), expr))
                                    }).and(f.x.require.iter().fold(Ok(()), |acc,expr| {
                                        // shouldn't have any open foralls when invoking a lemma, afaik
                                        assert!(state.empty_foralls());
                                        acc.and(build_graph(ctx, state, Polarity::Negative, Some(&new_bindings), expr))
                                    })) {
                                        Ok(_) => VisitorControlFlow::Return,
                                        Err(err) => return VisitorControlFlow::Stop(err),
                                    }
                                }
                                Mode::Exec => {
                                    VisitorControlFlow::Stop(error(&expr.span, "exec calls are not supported in the EPR fragment"))
                                }
                            }
                        } else {
                            VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
                        }
                    }
                }
                crate::ast::CallTarget::FnSpec(_) |
                crate::ast::CallTarget::BuiltinSpecFun(_, _) => VisitorControlFlow::Stop(error(&expr.span, "this call is not supported in the EPR fragment"))
            }
            AssertAssume { is_assume, expr } => {
                if *is_assume {
                    // assume means the expression is treated as just a ensures, so recurse positively
                    match build_graph(ctx, state, Polarity::Positive, bindings, expr) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                } else {
                    // assert means the expression is treated as both a require and ensure, so recurse both ways
                    match {
                        build_graph(ctx, state, polarity.flip(), bindings, expr)
                    }.and({
                        build_graph(ctx, state, polarity, bindings, expr)
                    }) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                }
            }
            If(cond, e1, e2) => {
                // TODO: Diff between spec and proof If?
                match {
                    // cond is explored negatively for if
                    build_graph(ctx, state, polarity.flip(), bindings, cond)
                }.and({
                    // e1 explored regularly
                    build_graph(ctx, state, polarity, bindings, e1)
                }).and({
                    if let Some(e2) = e2 {
                        {
                            // cond explored regularly for else
                            build_graph(ctx, state, polarity, bindings, cond)
                        }.and({
                            // e2 explored regularly
                            build_graph(ctx, state, polarity, bindings, e2)
                        })
                    } else {
                        Ok(())
                    }
                }) {
                    Ok(_) => VisitorControlFlow::Return,
                    Err(err) => return VisitorControlFlow::Stop(err),
                }
            }
            UnaryOpr(..) |
            BinaryOpr(..) |
            Loc(..) |
            Tuple(..) |
            Ctor(..) |
            Multi(..) |
            WithTriggers { .. } |
            Assign { .. } |
            Match(..) |
            Loop { .. } |
            Return(..) |
            Ghost { .. } |
            Block(..) => VisitorControlFlow::Recurse,

            Const(_) |
            Var(_) |
            VarLoc(_) |
            VarAt(_, _) |
            ConstVar(_, _) |
            StaticVar(_) |
            Fuel(_, _) |
            Header(_) |
            BreakOrContinue { .. } => VisitorControlFlow::Return,

            Choose { .. } | // TODO
            Closure(_, _) | // TODO: maybe supported down the line?
            NullaryOpr(..) |
            ExecClosure { .. } |
            AssertBy { .. } |
            AssertQuery { .. } |
            AssertCompute(..) |
            RevealString(..) |
            OpenInvariant(..) => VisitorControlFlow::Stop(error(&expr.span, "unsupported in EPR fragment")),
        });
        Ok(())
    }
    for f in krate.functions.iter().filter(|f| {
        (f.x.mode == Mode::Proof || f.x.mode == Mode::Exec)
            && f.x.owning_module.as_ref().is_some_and(|m| m == &module)
    }) {
        let FunctionX { name, require, ensure, decrease, body, mode, .. } = &f.x;
        // TODO: Can function attrs change something about EPR? Yes! inline
        // TODO: Can broadcast forall for unrelated data change EPR fragment status?
        if decrease.len() != 0 {
            return Err(error(&f.span, "Recursion/decrease not supported in EPR Mode"));
        }
        if matches!(mode, Mode::Exec) {
            return Err(error(&f.span, "Exec mode functions not supported in EPR Mode"));
        }
        if DEBUG {
            let function_name = path_as_friendly_rust_name(&name.path);
            dbg!(function_name);
        }
        // Pass 1: Collect all the functions mentioned
        let mut state = CollectState::new();
        for expr in ensure.iter() {
            collect_functions(ctx, &mut state, expr, &HashMap::new())?;
        }
        for expr in require.iter() {
            collect_functions(ctx, &mut state, expr, &HashMap::new())?;
        }
        if let Some(expr) = body {
            collect_functions(ctx, &mut state, expr, &HashMap::new())?;
        }
        // Pass 2: Build the "VC". Check for QA in ensures/requires
        let mut bstate = BuildState::new();
        // params for a proof functions don't get encoded as additional quantifiers, so
        // don't need to specify init_params
        // no bindings at top level as this is where the types come from
        for expr in ensure.iter() {
            // ensures start with negative polarity, as expression is negated
            assert!(bstate.empty_foralls());
            build_graph(ctx, &mut bstate, Polarity::Negative, None, expr)?;
        }
        for expr in require.iter() {
            // requires start with positive polarity
            assert!(bstate.empty_foralls());
            build_graph(ctx, &mut bstate, Polarity::Positive, None, expr)?;
        }
        if let Some(expr) = body {
            assert!(bstate.empty_foralls());
            build_graph(ctx, &mut bstate, Polarity::Positive, None, expr)?;
        }
        for spec in &state.reached_spec_funcs {
            let spec_func = &ctx.func_map[&spec.fun];
            let FunctionX { mode, body, params, ret, typ_params, .. } = &spec_func.x;
            if DEBUG {
                println!("Reached Spec Fn: {}", spec.print_name());
            }
            assert!(matches!(mode, Mode::Spec));
            assert!(typ_params.len() == spec.typs.len());
            let bindings = typ_params
                .iter()
                .map(|x| x.as_ref())
                .cloned()
                .zip(spec.typs.iter().cloned())
                .collect();
            // add the edges for this functions args to the state
            bstate.add_function_edges(params, ret, &bindings);
            // recurse on the body of this function to add the positive and negative QA edges to the VC
            // i.e
            // foo(x) { bar(x) && baz(x)}
            // becomes
            // forall x foo(x) <==> bar(x) && baz(x)
            if let Some(body) = body {
                let mut param_types = HashMap::new();
                for param in params.iter() {
                    let param_type = param_type_name_with_bindings(&param.x.typ, &bindings);
                    // track the number of new foralls for each argument type so we don't lose any
                    *param_types.entry(param_type).or_insert(0) += 1;
                }
                bstate.open_foralls = param_types.clone();
                build_graph(ctx, &mut bstate, Polarity::Negative, Some(&bindings), &body)?;
                bstate.open_foralls = param_types.clone();
                build_graph(ctx, &mut bstate, Polarity::Positive, Some(&bindings), &body)?;
            }
        }
        bstate.qa_graph.compute_sccs();
        let acyclic =
            bstate.qa_graph.sort_sccs().iter().all(|x| !bstate.qa_graph.node_is_in_cycle(x));
        if !acyclic {
            return Err(error(
                &f.span,
                "Function not in EPR, quantifier alternation graph contains cycle",
            ));
        }
    }
    Ok(())
}
