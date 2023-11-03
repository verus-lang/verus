use std::collections::{HashMap, HashSet};

use air::scope_map::ScopeMap;
use ast_visitor::VisitorControlFlow;

use crate::{
    ast::{Expr, Fun, FunctionX, Krate, Mode, Param, Params, Path, Typ, TypX, VirErr},
    ast_util::{path_as_friendly_rust_name, undecorate_typ},
    ast_visitor::{self, expr_visitor_dfs},
    context::Ctx,
    messages::error,
    scc::Graph,
};

struct CollectState {
    reached_spec_funcs: HashSet<Fun>,
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
        BuildState {
            qa_graph: Graph::<String>::new(),
            open_foralls: HashMap::new(),
        }
    }

    fn add_function_edges(&mut self, params: &Params, ret: &Param) {
        let ret_node = param_type_name(&ret.x.typ);
        for param in params.iter() {
            let param_node = param_type_name(&param.x.typ);
            // println!("Adding Func Edge: {} -> {}", &param_node, &ret_node);
            self.qa_graph.add_edge(param_node, ret_node.clone());
        }
    }

    fn empty_foralls(&self) -> bool {
        self.open_foralls.iter().all(|(_, count)| *count == 0)
    }
}

fn param_type_name(typ: &Typ) -> String {
    // TODO: Check if there are other decorators here
    // undecorate_typ
    match &*undecorate_typ(typ) {
        TypX::Bool => "Bool".to_string(),
        TypX::Datatype(path, _, _) => path_as_friendly_rust_name(path),
        _ => panic!("Unsupported EPR Type"),
    }
}

pub fn alternation_check(ctx: &Ctx, krate: &Krate, module: Path) -> Result<(), VirErr> {
    fn collect_functions(ctx: &Ctx, state: &mut CollectState, expr: &Expr) -> Result<(), VirErr> {
        use crate::ast::ExprX::*;
        expr_visitor_dfs::<VirErr, _>(expr, &mut ScopeMap::new(), &mut |_, expr| match &expr.x {
            Call(target, _) => match target {
                crate::ast::CallTarget::Fun(call_target_kind, fun, _, impl_paths, _) => {
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
                            match f.x.mode {
                                Mode::Spec => {
                                    // we've seen this function; add it to our list
                                    state.reached_spec_funcs.insert(fun.clone());
                                    // if it has a body, recurse
                                    if let Some(f_body) = &f.x.body {
                                        match collect_functions(ctx, state, f_body) {
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
                                        match collect_functions(ctx, state, r) {
                                            Ok(_) => (),
                                            Err(err) => return VisitorControlFlow::Stop(err),
                                        }
                                    }
                                    for e in f.x.ensure.iter() {
                                        match collect_functions(ctx, state, e) {
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
    fn build_graph(ctx: &Ctx, state: &mut BuildState, polarity : Polarity, expr: &Expr) -> Result<(), VirErr> {
        use crate::ast::ExprX::*;
        expr_visitor_dfs::<VirErr, _>(expr, &mut ScopeMap::new(), &mut |_, expr| match &expr.x {
            Unary(op, e) => match op {
                crate::ast::UnaryOp::Not => {
                    match build_graph(ctx, state, polarity.flip(), e) {
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
                        let typ_name = param_type_name(&b.a);
                        *state.open_foralls.entry(typ_name.clone()).or_insert(0) += 1;
                    }
                    match build_graph(ctx, state, polarity, e) {
                        Ok(_) => {
                            for b in binders.iter() {
                                let typ_name = param_type_name(&b.a);
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
                        let typ_name = param_type_name(&b.a);
                        for (forall_name, count) in state.open_foralls.iter() {
                            // empty ones remain in the map with 0 count
                            if *count > 0 {
                                // println!("Adding QA Edge: {} -> {}", forall_name, &typ_name);
                                state.qa_graph.add_edge(forall_name.clone(), typ_name.clone());
                            }
                        }
                    }
                    match build_graph(ctx, state, polarity, e) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                }
            },
            Binary(op, left, right) => match op {
                crate::ast::BinaryOp::Implies => {
                    match {
                        // left is explored at opposite polarity
                        build_graph(ctx, state, polarity.flip(), left)
                    }.and({
                        // right is explored at same polarity
                        build_graph(ctx, state, polarity, right)
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
                            build_graph(ctx, state, Polarity::Positive, left)
                        }.and({
                            build_graph(ctx, state, Polarity::Negative, left)
                        }).and({
                            build_graph(ctx, state, Polarity::Positive, right)
                        }).and({
                            build_graph(ctx, state, Polarity::Negative, right)
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
            Call(target, _) => match target {
                crate::ast::CallTarget::Fun(call_target_kind, fun, _, impl_paths, _) => {
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
                            match f.x.mode {
                                // spec funcs aren't recursed on second pass
                                Mode::Spec => VisitorControlFlow::Return,
                                Mode::Proof => {
                                    // should only be here when parsing the body of the lemma
                                    // params for a proof function don't get encoded as additional quantifiers
                                    // add the requires clause negatively, and the ensures positively
                                    match f.x.ensure.iter().fold(Ok(()), |acc,expr| {
                                        // shouldn't have any open foralls when invoking a lemma, afaik
                                        assert!(state.empty_foralls());
                                        acc.and(build_graph(ctx, state, Polarity::Positive, expr))
                                    }).and(f.x.require.iter().fold(Ok(()), |acc,expr| {
                                        // shouldn't have any open foralls when invoking a lemma, afaik
                                        assert!(state.empty_foralls());
                                        acc.and(build_graph(ctx, state, Polarity::Negative, expr))
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
                    match build_graph(ctx, state, Polarity::Positive, expr) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                } else {
                    // assert means the expression is treated as both a require and ensure, so recurse both ways
                    match {
                        build_graph(ctx, state, polarity.flip(), expr)
                    }.and({
                        build_graph(ctx, state, polarity, expr)
                    }) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                }
            }
            Choose { .. } | // TODO
            If(..) | // TODO
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
        let FunctionX {
            name, require, ensure, decrease, body, mode, ..
        } = &f.x;
        // TODO: Can function attrs change something about EPR? Yes! inline
        // TODO: Can broadcast forall for unrelated data change EPR fragment status?
        if decrease.len() != 0 {
            return Err(error(&f.span, "Recursion/decrease not supported in EPR Mode"));
        }
        if matches!(mode, Mode::Exec) {
            return Err(error(&f.span, "Exec mode functions not supported in EPR Mode"));
        }
        // let function_name = path_as_friendly_rust_name(&name.path);
        // dbg!(function_name);
        // Pass 1: Collect all the functions mentioned
        let mut state = CollectState::new();
        for expr in ensure.iter() {
            collect_functions(ctx, &mut state, expr)?;
        }
        for expr in require.iter() {
            collect_functions(ctx, &mut state, expr)?;
        }
        if let Some(expr) = body {
            collect_functions(ctx, &mut state, expr)?;
        }
        // Pass 2: Build the "VC". Check for QA in ensures/requires
        let mut bstate = BuildState::new();
        // params for a proof functions don't get encoded as additional quantifiers, so
        // don't need to specify init_params
        for expr in ensure.iter() {
            // ensures start with negative polarity, as expression is negated
            assert!(bstate.empty_foralls());
            build_graph(ctx, &mut bstate, Polarity::Negative, expr)?;
        }
        for expr in require.iter() {
            // requires start with positive polarity
            assert!(bstate.empty_foralls());
            build_graph(ctx, &mut bstate, Polarity::Positive, expr)?;
        }
        if let Some(expr) = body {
            assert!(bstate.empty_foralls());
            build_graph(ctx, &mut bstate, Polarity::Positive, expr)?;
        }
        for spec in &state.reached_spec_funcs {
            let spec_func = &ctx.func_map[spec];
            let FunctionX { mode, body, params, ret, attrs, .. } = &spec_func.x;
            // println!("Reached Spec Fn: {}", path_as_friendly_rust_name(&spec_func.x.name.path));
            assert!(matches!(mode, Mode::Spec));
            // add the edges for this functions args to the state
            bstate.add_function_edges(params, ret);
            // recurse on the body of this function to add the positive and negative QA edges to the VC
            // i.e
            // foo(x) { bar(x) && baz(x)}
            // becomes
            // forall x foo(x) <==> bar(x) && baz(x)
            if let Some(body) = body {
                let mut param_types = HashMap::new();
                for param in params.iter() {
                    let param_type = param_type_name(&param.x.typ);
                    // track the number of new foralls for each argument type so we don't lose any
                    *param_types.entry(param_type).or_insert(0) += 1;
                }
                bstate.open_foralls = param_types.clone();
                build_graph(ctx, &mut bstate, Polarity::Negative, &body)?;
                bstate.open_foralls = param_types.clone();
                build_graph(ctx, &mut bstate, Polarity::Positive, &body)?;
            }
        }
        bstate.qa_graph.compute_sccs();
        let acyclic =
            bstate.qa_graph.sort_sccs().iter().all(|x| !bstate.qa_graph.node_is_in_cycle(x));
        // dbg!(acyclic);
        if !acyclic {
            return Err(error(
                &f.span,
                "Function not in EPR, quantifier alternation graph contains cycle",
            ));
        }
    }
    Ok(())
}
