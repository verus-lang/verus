use std::collections::HashMap;

use air::scope_map::ScopeMap;
use ast_visitor::VisitorControlFlow;

use crate::{
    ast::{FunctionX, Krate, Mode, VirErr, Expr, Typ, TypX},
    ast_visitor::{self, expr_visitor_dfs},
    context::Ctx,
    scc::Graph, messages::error, ast_util::path_as_friendly_rust_name
};

struct State {
    /// the quantifier alternation graph that this pass is trying to build
    qa_graph : Graph<String>,
    /// true if an encountered quantifier can be interpreted directly,
    /// false if it needs to be swapped (i.e. under negation)
    positive_polarity : bool,
    /// currently outstanding variables
    /// u64 keeps count so that we can decrement and not lose typs on returning
    open_foralls : HashMap<String, u64>
}

impl State {
    fn new() -> Self {
        State {
            qa_graph : Graph::<String>::new(),
            // start at negative polarity as VC is negated
            positive_polarity : false,
            open_foralls : HashMap::new(),
        }
    }
}

fn param_type_name(typ : &Typ) -> String {
    match typ.as_ref() {
        TypX::Bool => "Bool".to_string(),
        TypX::Datatype(path,_ ,_) => path_as_friendly_rust_name(path),
        _ => panic!("Unsupported EPR Type")
    }
}

pub fn alternation_check(ctx: &Ctx, krate: &Krate, /* TODO: &mut graph ? */) -> Result<(), VirErr> {
    fn build_graph_visit(ctx: &Ctx, state: &mut State, expr: &Expr) -> Result<(), VirErr> {
        use crate::ast::ExprX::*;
        expr_visitor_dfs::<VirErr, _>(expr, &mut ScopeMap::new(), &mut |scope_map, expr| match &expr.x {
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
                                    // we've seen this function; add its nodes and edges for its args
                                    let ret_node = param_type_name(&f.x.ret.x.typ);
                                    let mut param_nodes = HashMap::new();
                                    for param in f.x.params.iter() {
                                        let param_node = param_type_name(&param.x.typ);
                                        // track the number of new foralls for each argument type so we don't lose any
                                        *param_nodes.entry(param_node.clone()).or_insert(0) += 1;
                                        state.qa_graph.add_edge(param_node, ret_node.clone());
                                    }
                                    // if it has a body, additional work to do before recursing
                                    if let Some(f_body) = &f.x.body {
                                        // open foralls for its args
                                        // TODO (if a function is inlined, this might not be necessary)
                                        // TODO (if an arg is not a quantified arg (i.e. a constant, does this still hold?))
                                        // this is to ensure that the definition forall is accounted for:
                                        // i.e 
                                        // foo(x) { bar(x) && baz(x)} 
                                        // becomes 
                                        // forall x foo(x) <==> bar(x) && baz(x)
                                        for (typ_name, count) in &param_nodes {
                                            *state.open_foralls.entry(typ_name.clone()).or_insert(0) += count;
                                        }
                                        match build_graph_visit(ctx, state, f_body) {
                                            Ok(_) => {
                                                // remove the foralls we added for this definition
                                                for (typ_name, count) in param_nodes {
                                                    let cur_count = state.open_foralls.get_mut(&typ_name).expect("should already have entry");
                                                    assert!(*cur_count >= count);
                                                    *cur_count -= count;
                                                }
                                                VisitorControlFlow::Return
                                            },
                                            Err(err) => VisitorControlFlow::Stop(err),
                                        }
                                    } else {
                                        VisitorControlFlow::Return
                                    }
                                }
                                // TODO: is this relevant at all? when will we see a proof fn inside spec code?
                                Mode::Proof => {
                                    // TODO update state or arguments to track polarity
                                    for r in f.x.require.iter() {
                                        match build_graph_visit(ctx, state, r) {
                                            Ok(_) => (),
                                            Err(err) => return VisitorControlFlow::Stop(err),
                                        }
                                    }
                                    // TODO update state or arguments to track polarity
                                    for e in f.x.ensure.iter() {
                                        match build_graph_visit(ctx, state, e) {
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
            Unary(op, e) => match op {
                crate::ast::UnaryOp::Not => {
                    state.positive_polarity = !state.positive_polarity;
                    match build_graph_visit(ctx, state, e) {
                        Ok(_) => {
                            state.positive_polarity = !state.positive_polarity;
                            VisitorControlFlow::Return
                        },
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                },
                _ => VisitorControlFlow::Recurse,
            },
            Quant(op, binders, e) => {
                let forall = (state.positive_polarity && matches!(op.quant, air::ast::Quant::Forall)) 
                                || (!state.positive_polarity && matches!(op.quant, air::ast::Quant::Exists));
                if forall {
                    // forall case: add the new variables to open foralls, then recurse
                    for b in binders.iter() {
                        let typ_name = param_type_name(&b.a);
                        *state.open_foralls.entry(typ_name.clone()).or_insert(0) += 1;
                    }
                    match build_graph_visit(ctx, state, e) {
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
                                state.qa_graph.add_edge(forall_name.clone(), typ_name.clone());
                            }
                        }
                    }
                    match build_graph_visit(ctx, state, e) {
                        Ok(_) => VisitorControlFlow::Return,
                        Err(err) => return VisitorControlFlow::Stop(err),
                    }
                }
            },
            Closure(_, _) => todo!(),
            Choose { params, cond, body } => todo!(),

            // TODO: I think for everything that isn't negation, we can just peak inside
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
    for f in krate.functions.iter().filter(|f| f.x.mode == Mode::Proof) {
        let FunctionX { require, ensure, decrease, body, broadcast_forall, attrs, .. } = &f.x;
        // let Some(body) = body else { return Ok(()) };
        let mut state = State::new();
        for expr in ensure.iter() {
            build_graph_visit(ctx, &mut state, expr)?;
        }
        dbg!(state.qa_graph);
    }
    Ok(())
}
