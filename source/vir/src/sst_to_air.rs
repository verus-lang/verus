use crate::ast::{
    BinaryOp, Ident, Idents, IntRange, Mode, Params, Path, Typ, TypX, UnaryOp, UnaryOpr,
};
use crate::ast_util::path_to_string;
use crate::context::Ctx;
use crate::def::{
    prefix_ensures, prefix_fuel_id, prefix_recursive, prefix_requires, prefix_type_id,
    suffix_global_id, suffix_local_id, suffix_typ_param_id, SnapPos, Spanned, FUEL_BOOL,
    FUEL_BOOL_DEFAULT, FUEL_DEFAULTS, FUEL_ID, FUEL_PARAM, FUEL_TYPE, POLY, SNAPSHOT_CALL, SUCC,
    UNIT,
};
use crate::sst::{BndX, Dest, Exp, ExpX, Stm, StmX};
use crate::util::vec_map;
use air::ast::{
    BindX, BinderX, Binders, Command, CommandX, Commands, Constant, Decl, DeclX, Expr, ExprX,
    MultiOp, Quant, QueryX, Span, Stmt, StmtX, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_typ, ident_var, int_typ, mk_and, mk_eq, mk_exists,
    mk_implies, mk_ite, mk_not, mk_or, str_apply, str_ident, str_typ, str_var, string_var,
};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[inline(always)]
pub(crate) fn path_to_air_ident(path: &Path) -> Ident {
    Arc::new(path_to_string(path))
}

pub(crate) fn apply_range_fun(name: &str, range: &IntRange, exprs: Vec<Expr>) -> Expr {
    let mut args = exprs;
    match range {
        IntRange::Int | IntRange::Nat => {}
        IntRange::U(range) | IntRange::I(range) => {
            let bits = Constant::Nat(Arc::new(range.to_string()));
            args.insert(0, Arc::new(ExprX::Const(bits)));
        }
        IntRange::USize | IntRange::ISize => {
            args.insert(0, str_var(crate::def::ARCH_SIZE));
        }
    }
    str_apply(name, &args)
}

pub(crate) fn typ_to_air(_ctx: &Ctx, typ: &Typ) -> air::ast::Typ {
    match &**typ {
        TypX::Unit => str_typ(UNIT),
        TypX::Int(_) => int_typ(),
        TypX::Bool => bool_typ(),
        TypX::Path(path) => ident_typ(&path_to_air_ident(path)),
        TypX::Boxed(_) => str_typ(POLY),
        TypX::TypParam(_) => str_typ(POLY),
    }
}

pub fn typ_to_id(typ: &Typ) -> Expr {
    match &**typ {
        TypX::Unit => str_var(crate::def::TYPE_ID_UNIT),
        TypX::Int(range) => match range {
            IntRange::Int => str_var(crate::def::TYPE_ID_INT),
            IntRange::Nat => str_var(crate::def::TYPE_ID_NAT),
            IntRange::U(_) | IntRange::USize => {
                apply_range_fun(crate::def::TYPE_ID_UINT, range, vec![])
            }
            IntRange::I(_) | IntRange::ISize => {
                apply_range_fun(crate::def::TYPE_ID_SINT, range, vec![])
            }
        },
        TypX::Bool => str_var(crate::def::TYPE_ID_BOOL),
        TypX::Path(path) => string_var(&prefix_type_id(&Arc::new(path_to_string(&path)))),
        TypX::Boxed(_) => panic!("internal error: type arguments should be unboxed"),
        TypX::TypParam(x) => ident_var(&suffix_typ_param_id(x)),
    }
}

// If expr has type typ, what can we assume to be true about expr?
pub(crate) fn typ_invariant(typ: &Typ, expr: &Expr, use_has_type: bool) -> Option<Expr> {
    match &**typ {
        TypX::Int(IntRange::Int) => None,
        TypX::Int(IntRange::Nat) => {
            let zero = Arc::new(ExprX::Const(Constant::Nat(Arc::new("0".to_string()))));
            Some(Arc::new(ExprX::Binary(air::ast::BinaryOp::Le, zero, expr.clone())))
        }
        TypX::Int(range) => {
            let f_name = match range {
                IntRange::Int => panic!("internal error: Int"),
                IntRange::Nat => panic!("internal error: Int"),
                IntRange::U(_) | IntRange::USize => crate::def::U_INV,
                IntRange::I(_) | IntRange::ISize => crate::def::I_INV,
            };
            Some(apply_range_fun(&f_name, &range, vec![expr.clone()]))
        }
        TypX::TypParam(x) if use_has_type => Some(str_apply(
            crate::def::HAS_TYPE,
            &vec![expr.clone(), ident_var(&suffix_typ_param_id(&x))],
        )),
        _ => None,
    }
}

pub(crate) fn ctor_to_apply<'a>(
    ctx: &'a Ctx,
    path: &Path,
    variant: &Ident,
    binders: &'a Binders<Exp>,
) -> (Ident, impl Iterator<Item = &'a Arc<BinderX<Arc<Spanned<ExpX>>>>>) {
    let fields = &ctx.datatypes[path]
        .iter()
        .find(|v| &v.name == variant)
        .expect(format!("couldn't find datatype variant {} in ctor", variant).as_str())
        .a;
    (
        variant.clone(),
        fields.iter().map(move |f| {
            binders
                .iter()
                .find(|binder| binder.name == f.name)
                .expect(format!("couldn't find datatype binder {} in ctor", f.name).as_str())
        }),
    )
}

pub(crate) fn constant_to_expr(_ctx: &Ctx, constant: &crate::ast::Constant) -> Expr {
    match constant {
        crate::ast::Constant::Bool(b) => Arc::new(ExprX::Const(Constant::Bool(*b))),
        crate::ast::Constant::Nat(s) => Arc::new(ExprX::Const(Constant::Nat(s.clone()))),
    }
}

pub(crate) fn exp_to_expr(ctx: &Ctx, exp: &Exp) -> Expr {
    match &exp.x {
        ExpX::Const(c) => {
            let expr = constant_to_expr(ctx, c);
            expr
        }
        ExpX::Var(x) => string_var(&suffix_local_id(x)),
        ExpX::Old(span, x) => Arc::new(ExprX::Old(span.clone(), suffix_local_id(x))),
        ExpX::Call(rec, x, typs, args) => {
            let air_ident = path_to_air_ident(&x);
            let name =
                suffix_global_id(&if *rec { prefix_recursive(&air_ident) } else { air_ident });
            let mut exprs: Vec<Expr> = vec_map(typs, typ_to_id);
            for arg in args.iter() {
                exprs.push(exp_to_expr(ctx, arg));
            }
            ident_apply(&name, &exprs)
        }
        ExpX::Ctor(path, variant, binders) => {
            let (variant, args) = ctor_to_apply(ctx, path, variant, binders);
            let args = args.map(|b| exp_to_expr(ctx, &b.a)).collect::<Vec<_>>();
            Arc::new(ExprX::Apply(variant, Arc::new(args)))
        }
        ExpX::Unary(op, exp) => match op {
            UnaryOp::Not => mk_not(&exp_to_expr(ctx, exp)),
            UnaryOp::Trigger(_) => exp_to_expr(ctx, exp),
            UnaryOp::Clip(IntRange::Int) => exp_to_expr(ctx, exp),
            UnaryOp::Clip(range) => {
                let expr = exp_to_expr(ctx, exp);
                let f_name = match range {
                    IntRange::Int => panic!("internal error: Int"),
                    IntRange::Nat => crate::def::NAT_CLIP,
                    IntRange::U(_) | IntRange::USize => crate::def::U_CLIP,
                    IntRange::I(_) | IntRange::ISize => crate::def::I_CLIP,
                };
                apply_range_fun(&f_name, &range, vec![expr])
            }
        },
        ExpX::UnaryOpr(op, exp) => match op {
            UnaryOpr::Box(typ) => {
                let expr = exp_to_expr(ctx, exp);
                let f_name = match &**typ {
                    TypX::Unit => str_ident(crate::def::BOX_UNIT),
                    TypX::Bool => str_ident(crate::def::BOX_BOOL),
                    TypX::Int(_) => str_ident(crate::def::BOX_INT),
                    TypX::Path(path) => crate::def::prefix_box(&Arc::new(path_to_string(&path))),
                    TypX::Boxed(_) => panic!("internal error: Box(Boxed)"),
                    TypX::TypParam(_) => panic!("internal error: Box(TypParam)"),
                };
                ident_apply(&f_name, &vec![expr])
            }
            UnaryOpr::Unbox(typ) => {
                let expr = exp_to_expr(ctx, exp);
                let f_name = match &**typ {
                    TypX::Unit => str_ident(crate::def::UNBOX_UNIT),
                    TypX::Bool => str_ident(crate::def::UNBOX_BOOL),
                    TypX::Int(_) => str_ident(crate::def::UNBOX_INT),
                    TypX::Path(path) => crate::def::prefix_unbox(&Arc::new(path_to_string(&path))),
                    TypX::Boxed(_) => panic!("internal error: Box(Boxed)"),
                    TypX::TypParam(_) => panic!("internal error: Box(TypParam)"),
                };
                ident_apply(&f_name, &vec![expr])
            }
        },
        ExpX::Binary(op, lhs, rhs) => {
            let lh = exp_to_expr(ctx, lhs);
            let rh = exp_to_expr(ctx, rhs);
            let expx = match op {
                BinaryOp::And => {
                    return mk_and(&vec![lh, rh]);
                }
                BinaryOp::Or => {
                    return mk_or(&vec![lh, rh]);
                }
                BinaryOp::Implies => {
                    return mk_implies(&lh, &rh);
                }
                BinaryOp::Add => ExprX::Multi(MultiOp::Add, Arc::new(vec![lh, rh])),
                BinaryOp::Sub => ExprX::Multi(MultiOp::Sub, Arc::new(vec![lh, rh])),
                BinaryOp::Mul => ExprX::Multi(MultiOp::Mul, Arc::new(vec![lh, rh])),
                BinaryOp::Ne => {
                    let eq = ExprX::Binary(air::ast::BinaryOp::Eq, lh, rh);
                    ExprX::Unary(air::ast::UnaryOp::Not, Arc::new(eq))
                }
                _ => {
                    let aop = match op {
                        BinaryOp::And => panic!("internal error"),
                        BinaryOp::Or => panic!("internal error"),
                        BinaryOp::Implies => panic!("internal error"),
                        BinaryOp::Eq => air::ast::BinaryOp::Eq,
                        BinaryOp::Ne => panic!("internal error"),
                        BinaryOp::Le => air::ast::BinaryOp::Le,
                        BinaryOp::Ge => air::ast::BinaryOp::Ge,
                        BinaryOp::Lt => air::ast::BinaryOp::Lt,
                        BinaryOp::Gt => air::ast::BinaryOp::Gt,
                        BinaryOp::Add => panic!("internal error"),
                        BinaryOp::Sub => panic!("internal error"),
                        BinaryOp::Mul => panic!("internal error"),
                        BinaryOp::EuclideanDiv => air::ast::BinaryOp::EuclideanDiv,
                        BinaryOp::EuclideanMod => air::ast::BinaryOp::EuclideanMod,
                    };
                    ExprX::Binary(aop, lh, rh)
                }
            };
            Arc::new(expx)
        }
        ExpX::If(e1, e2, e3) => {
            mk_ite(&exp_to_expr(ctx, e1), &exp_to_expr(ctx, e2), &exp_to_expr(ctx, e3))
        }
        ExpX::Field { lhs, datatype: _, field_name: name } => {
            // TODO: this should include datatype_name in the function name
            let lh = exp_to_expr(ctx, lhs);
            Arc::new(ExprX::Apply(name.clone(), Arc::new(vec![lh])))
        }
        ExpX::Bind(bnd, exp) => match &bnd.x {
            BndX::Let(binders) => {
                let expr = exp_to_expr(ctx, exp);
                let binders = vec_map(&*binders, |b| {
                    Arc::new(BinderX { name: suffix_local_id(&b.name), a: exp_to_expr(ctx, &b.a) })
                });
                Arc::new(ExprX::Bind(Arc::new(BindX::Let(Arc::new(binders))), expr))
            }
            BndX::Quant(quant, binders, trigs) => {
                let expr = exp_to_expr(ctx, exp);
                let mut invs: Vec<Expr> = Vec::new();
                for binder in binders.iter() {
                    let typ_inv =
                        typ_invariant(&binder.a, &ident_var(&suffix_local_id(&binder.name)), true);
                    if let Some(inv) = typ_inv {
                        invs.push(inv);
                    }
                }
                let inv = mk_and(&invs);
                let expr = match quant {
                    Quant::Forall => mk_implies(&inv, &expr),
                    Quant::Exists => mk_and(&vec![inv, expr]),
                };
                let binders = vec_map(&*binders, |b| {
                    Arc::new(BinderX { name: suffix_local_id(&b.name), a: typ_to_air(ctx, &b.a) })
                });
                let triggers =
                    vec_map(&*trigs, |trig| Arc::new(vec_map(trig, |x| exp_to_expr(ctx, x))));
                Arc::new(ExprX::Bind(
                    Arc::new(BindX::Quant(*quant, Arc::new(binders), Arc::new(triggers))),
                    expr,
                ))
            }
        },
    }
}

struct State {
    local_shared: Vec<Decl>, // shared between all queries for a single function
    commands: Vec<Command>,
    snapshot_count: u32,    // Used to ensure unique Idents for each snapshot
    latest_snapshot: Ident, // The ID of the closest snapshot that dominates the current position in the AST
    snap_map: Vec<(Span, SnapPos)>, // Maps each statement's span to the closest dominating snapshot's ID
}

fn stm_to_stmts(ctx: &Ctx, state: &mut State, stm: &Stm) -> Vec<Stmt> {
    match &stm.x {
        StmX::Call(x, typs, args, dest) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            let func = &ctx.func_map[x];
            if func.x.require.len() > 0 {
                let f_req = prefix_requires(&path_to_air_ident(&func.x.path));
                let mut req_args = vec_map(typs, typ_to_id);
                for arg in args.iter() {
                    req_args.push(exp_to_expr(ctx, arg));
                }
                let e_req = Arc::new(ExprX::Apply(f_req, Arc::new(req_args)));
                let description = match &func.x.custom_req_err {
                    None => Some("precondition not satisfied".to_string()),
                    Some(s) => Some(s.clone()),
                };
                let option_span = Arc::new(Some(Span { description, ..stm.span.clone() }));
                stmts.push(Arc::new(StmtX::Assert(option_span, e_req)));
            }
            let mut ens_args: Vec<Expr> = vec_map(typs, typ_to_id);
            match dest {
                None => {
                    for arg in args.iter() {
                        ens_args.push(exp_to_expr(ctx, arg));
                    }
                    if ctx.debug {
                        state
                            .snap_map
                            .push((stm.span.clone(), SnapPos::Full(state.latest_snapshot.clone())));
                    }
                }
                Some(Dest { var, mutable }) => {
                    let x = suffix_local_id(&var.clone());
                    let mut overwrite = false;
                    for arg in args.iter() {
                        let arg_x = crate::sst_visitor::map_exp_visitor(arg, &mut |e| match &e.x {
                            ExpX::Var(x) if x == var => {
                                overwrite = true;
                                Spanned::new(
                                    arg.span.clone(),
                                    ExpX::Old(str_ident(SNAPSHOT_CALL), x.clone()),
                                )
                            }
                            _ => e.clone(),
                        });
                        ens_args.push(exp_to_expr(ctx, &arg_x));
                    }
                    if overwrite {
                        stmts.push(Arc::new(StmtX::Snapshot(str_ident(SNAPSHOT_CALL))));
                    }
                    ens_args.push(Arc::new(ExprX::Var(x.clone())));
                    if *mutable {
                        let havoc = StmtX::Havoc(x.clone());
                        stmts.push(Arc::new(havoc));
                    }
                    if ctx.debug {
                        // Add a snapshot after we modify the destination
                        state.snapshot_count += 1;
                        let name = format!("{}_mutation", state.snapshot_count);
                        let snapshot = Arc::new(StmtX::Snapshot(Arc::new(name.clone())));
                        stmts.push(snapshot);
                        state.latest_snapshot = Arc::new(name);
                        // Update the snap_map so that it reflects the state _after_ the
                        // statement takes effect.
                        state
                            .snap_map
                            .push((stm.span.clone(), SnapPos::Full(state.latest_snapshot.clone())));
                    }
                }
            }
            if func.x.ensure.len() > 0 {
                let f_ens = prefix_ensures(&path_to_air_ident(&func.x.path));
                let e_ens = Arc::new(ExprX::Apply(f_ens, Arc::new(ens_args)));
                stmts.push(Arc::new(StmtX::Assume(e_ens)));
            }
            vec![Arc::new(StmtX::Block(Arc::new(stmts)))] // wrap in block for readability
        }
        StmX::Assert(expr) => {
            let air_expr = exp_to_expr(ctx, &expr);
            let option_span = Arc::new(Some(stm.span.clone()));
            if ctx.debug {
                state
                    .snap_map
                    .push((stm.span.clone(), SnapPos::Full(state.latest_snapshot.clone())));
            }
            vec![Arc::new(StmtX::Assert(option_span, air_expr))]
        }
        StmX::Assume(expr) => {
            if ctx.debug {
                state
                    .snap_map
                    .push((stm.span.clone(), SnapPos::Full(state.latest_snapshot.clone())));
            }
            vec![Arc::new(StmtX::Assume(exp_to_expr(ctx, &expr)))]
        }
        StmX::Decl { ident, typ, mutable, init: _ } => {
            state.local_shared.push(if *mutable {
                Arc::new(DeclX::Var(suffix_local_id(&ident), typ_to_air(ctx, &typ)))
            } else {
                Arc::new(DeclX::Const(suffix_local_id(&ident), typ_to_air(ctx, &typ)))
            });
            if ctx.debug {
                state
                    .snap_map
                    .push((stm.span.clone(), SnapPos::Full(state.latest_snapshot.clone())));
            }
            vec![]
        }
        StmX::Assign(lhs, rhs) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            let ident = match &lhs.x {
                ExpX::Var(ident) => ident,
                _ => panic!("unexpected lhs {:?} in assign", lhs),
            };
            stmts.push(Arc::new(StmtX::Assign(suffix_local_id(&ident), exp_to_expr(ctx, rhs))));
            if ctx.debug {
                // Add a snapshot after we modify the destination
                state.snapshot_count += 1;
                let name = format!("{}_mutation", state.snapshot_count);
                let snapshot = Arc::new(StmtX::Snapshot(Arc::new(name.clone())));
                stmts.push(snapshot);
                state.latest_snapshot = Arc::new(name);
                // Update the snap_map so that it reflects the state _after_ the
                // statement takes effect.
                state
                    .snap_map
                    .push((stm.span.clone(), SnapPos::Full(state.latest_snapshot.clone())));
            }
            stmts
        }
        StmX::If(cond, lhs, rhs) => {
            let pos_cond = exp_to_expr(ctx, &cond);
            let neg_cond = Arc::new(ExprX::Unary(air::ast::UnaryOp::Not, pos_cond.clone()));
            let pos_assume = Arc::new(StmtX::Assume(pos_cond));
            let neg_assume = Arc::new(StmtX::Assume(neg_cond));
            let mut lhss = stm_to_stmts(ctx, state, lhs);
            let mut rhss = match rhs {
                None => vec![],
                Some(rhs) => stm_to_stmts(ctx, state, rhs),
            };
            lhss.insert(0, pos_assume);
            rhss.insert(0, neg_assume);
            let lblock = Arc::new(StmtX::Block(Arc::new(lhss)));
            let rblock = Arc::new(StmtX::Block(Arc::new(rhss)));
            let mut stmts = vec![Arc::new(StmtX::Switch(Arc::new(vec![lblock, rblock])))];
            if ctx.debug {
                // Add a snapshot for the state after we join the lhs and rhs back together
                state.snapshot_count += 1;
                let name = format!("{}_join", state.snapshot_count);
                let snapshot = Arc::new(StmtX::Snapshot(Arc::new(name.clone())));
                stmts.push(snapshot);
                state.latest_snapshot = Arc::new(name);
                // Update the snap_map so that it reflects the state _after_ the
                // statement takes effect.
                state
                    .snap_map
                    .push((stm.span.clone(), SnapPos::End(state.latest_snapshot.clone())));
            }
            stmts
        }
        StmX::While { cond, body, invs, typ_inv_vars, modified_vars } => {
            let pos_cond = exp_to_expr(ctx, &cond);
            let neg_cond = Arc::new(ExprX::Unary(air::ast::UnaryOp::Not, pos_cond.clone()));
            let pos_assume = Arc::new(DeclX::Axiom(pos_cond));
            let neg_assume = Arc::new(StmtX::Assume(neg_cond));
            let invs: Vec<(Span, Expr)> =
                invs.iter().map(|e| (e.span.clone(), exp_to_expr(ctx, e))).collect();

            let entry_snap_id = if ctx.debug {
                // Add a snapshot to capture the start of the while loop
                // We add the snapshot via Block to avoid copying the entire AST of the loop body
                state.snapshot_count += 1;
                let name = format!("{}_while_begin", state.snapshot_count);
                let entry_snap = Arc::new(name);
                state.latest_snapshot = entry_snap.clone();
                Some(entry_snap)
            } else {
                None
            };

            let mut air_body = stm_to_stmts(ctx, state, body);

            /*
            Generate a separate SMT query for the loop body.
            Rationale: large functions with while loops tend to be slow to verify.
            Therefore, it's good to try to factor large functions
            into smaller, easier-to-verify pieces.
            Since we have programmer-supplied invariants anyway,
            this is a good place for such refactoring.
            This isn't necessarily a benefit for small functions or small loops,
            but in practice, verification for large functions and large loops are slow
            enough that programmers often do this refactoring by hand anyway,
            so it's a benefit when verification gets hard, which is arguably what matters most.
            (The downside: the programmer might have to write more complete invariants,
            but this is part of the point: the invariants specify a precise interface
            between the outer function and the inner loop body, so we don't have to import
            the outer function's entire context into the verification of the loop body,
            which would slow verification of the loop body.)
            */
            let mut local = state.local_shared.clone();
            for (x, typ) in typ_inv_vars.iter() {
                let typ_inv = typ_invariant(typ, &ident_var(&suffix_local_id(x)), false);
                if let Some(expr) = typ_inv {
                    local.push(Arc::new(DeclX::Axiom(expr)));
                }
            }
            for (_, inv) in invs.iter() {
                local.push(Arc::new(DeclX::Axiom(inv.clone())));
            }
            local.push(pos_assume);
            for (span, inv) in invs.iter() {
                let description = Some("invariant not satisfied at end of loop body".to_string());
                let option_span = Arc::new(Some(Span { description, ..span.clone() }));
                let inv_stmt = StmtX::Assert(option_span, inv.clone());
                air_body.push(Arc::new(inv_stmt));
            }
            let assertion = if air_body.len() == 1 {
                air_body[0].clone()
            } else {
                Arc::new(StmtX::Block(Arc::new(air_body)))
            };

            let assertion = if !ctx.debug {
                assertion
            } else {
                // Update the snap_map to associate the start of the while loop with the new snapshot
                let entry_snap_id = entry_snap_id.unwrap(); // Always Some if ctx.debug
                let snapshot: Stmt = Arc::new(StmtX::Snapshot(Arc::new(entry_snap_id.to_string())));
                state.snap_map.push((body.span.clone(), SnapPos::Start(entry_snap_id.clone())));
                let block_contents: Vec<Stmt> = vec![snapshot, assertion];
                let new_block: Stmt = Arc::new(StmtX::Block(Arc::new(block_contents)));
                new_block
            };

            let query = Arc::new(QueryX { local: Arc::new(local), assertion });
            state.commands.push(Arc::new(CommandX::CheckValid(query)));

            // At original site of while loop, assert invariant, havoc, assume invariant + neg_cond
            let mut stmts: Vec<Stmt> = Vec::new();
            for (span, inv) in invs.iter() {
                let description = Some("invariant not satisfied before loop".to_string());
                let option_span = Arc::new(Some(Span { description, ..span.clone() }));
                let inv_stmt = StmtX::Assert(option_span, inv.clone());
                stmts.push(Arc::new(inv_stmt));
            }
            for x in modified_vars.iter() {
                stmts.push(Arc::new(StmtX::Havoc(suffix_local_id(&x))));
            }
            for (x, typ) in typ_inv_vars.iter() {
                if modified_vars.contains(x) {
                    let typ_inv = typ_invariant(typ, &ident_var(&suffix_local_id(x)), false);
                    if let Some(expr) = typ_inv {
                        stmts.push(Arc::new(StmtX::Assume(expr)));
                    }
                }
            }
            for (_, inv) in invs.iter() {
                let inv_stmt = StmtX::Assume(inv.clone());
                stmts.push(Arc::new(inv_stmt));
            }
            stmts.push(neg_assume);
            if ctx.debug {
                // Add a snapshot for the state after we emerge from the while loop
                state.snapshot_count += 1;
                let name = format!("{}_while_end", state.snapshot_count);
                let snapshot = Arc::new(StmtX::Snapshot(Arc::new(name.clone())));
                stmts.push(snapshot);
                // Update the snap_map so that it reflects the state _after_ the
                // statement takes effect.
                state.latest_snapshot = Arc::new(name);
                state
                    .snap_map
                    .push((stm.span.clone(), SnapPos::End(state.latest_snapshot.clone())));
            }
            stmts
        }
        StmX::Fuel(x, fuel) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            if *fuel >= 1 {
                // (assume (fuel_bool fuel%f))
                let id_fuel = prefix_fuel_id(&path_to_air_ident(&x));
                let expr_fuel_bool = str_apply(&FUEL_BOOL, &vec![ident_var(&id_fuel)]);
                stmts.push(Arc::new(StmtX::Assume(expr_fuel_bool)));
            }
            if *fuel >= 2 {
                // (assume (exists ((fuel Fuel)) (= fuel_nat%f (succ ... succ fuel))))
                let mut added_fuel = str_var(FUEL_PARAM);
                for _ in 0..*fuel - 1 {
                    added_fuel = str_apply(SUCC, &vec![added_fuel]);
                }
                let eq = mk_eq(
                    &ident_var(&crate::def::prefix_fuel_nat(&path_to_air_ident(&x))),
                    &added_fuel,
                );
                let binder = ident_binder(&str_ident(FUEL_PARAM), &str_typ(FUEL_TYPE));
                stmts.push(Arc::new(StmtX::Assume(mk_exists(&vec![binder], &vec![], &eq))));
            }
            if ctx.debug {
                state
                    .snap_map
                    .push((stm.span.clone(), SnapPos::Full(state.latest_snapshot.clone())));
            }
            stmts
        }
        StmX::Block(stms) => stms.iter().map(|s| stm_to_stmts(ctx, state, s)).flatten().collect(),
    }
}

fn set_fuel(local: &mut Vec<Decl>, hidden: &Vec<Path>) {
    let fuel_expr = if hidden.len() == 0 {
        str_var(&FUEL_DEFAULTS)
    } else {
        let mut disjuncts: Vec<Expr> = Vec::new();
        let id = str_ident("id");
        let x_id = ident_var(&id);

        // (= (fuel_bool id) (fuel_bool_default id))
        let fuel_bool = str_apply(&FUEL_BOOL, &vec![x_id.clone()]);
        let fuel_bool_default = str_apply(&FUEL_BOOL_DEFAULT, &vec![x_id.clone()]);
        let eq = air::ast::BinaryOp::Eq;
        disjuncts.push(Arc::new(ExprX::Binary(eq, fuel_bool.clone(), fuel_bool_default)));

        // ... || id == hidden1 || id == hidden2 || ...
        for hide in hidden {
            let x_hide = ident_var(&prefix_fuel_id(&path_to_air_ident(hide)));
            disjuncts.push(Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, x_id.clone(), x_hide)));
        }

        // (forall ((id FuelId)) ...)
        let trigger: Trigger = Arc::new(vec![fuel_bool.clone()]);
        let triggers: Triggers = Arc::new(vec![trigger]);
        let binders: Binders<air::ast::Typ> = Arc::new(vec![ident_binder(&id, &str_typ(FUEL_ID))]);
        let bind = Arc::new(BindX::Quant(Quant::Forall, binders, triggers));
        let or = Arc::new(ExprX::Multi(air::ast::MultiOp::Or, Arc::new(disjuncts)));
        Arc::new(ExprX::Bind(bind, or))
    };
    local.push(Arc::new(DeclX::Axiom(fuel_expr)));
}

pub fn body_stm_to_air(
    ctx: &Ctx,
    typ_params: &Idents,
    params: &Params,
    ret: &Option<(Ident, Typ, Mode)>,
    hidden: &Vec<Path>,
    reqs: &Vec<Exp>,
    enss: &Vec<Exp>,
    stm: &Stm,
) -> (Commands, Vec<(Span, SnapPos)>) {
    // Verifying a single function can generate multiple SMT queries.
    // Some declarations (local_shared) are shared among the queries.
    // Others are private to each query.
    let mut local_shared: Vec<Decl> = Vec::new();
    for x in typ_params.iter() {
        local_shared
            .push(Arc::new(DeclX::Const(suffix_typ_param_id(&x), str_typ(crate::def::TYPE))));
    }
    for param in params.iter() {
        local_shared.push(Arc::new(DeclX::Const(
            suffix_local_id(&param.x.name),
            typ_to_air(ctx, &param.x.typ),
        )));
    }
    match ret {
        None => {}
        Some((x, typ, _)) => {
            local_shared.push(Arc::new(DeclX::Const(suffix_local_id(&x), typ_to_air(ctx, &typ))));
        }
    }

    set_fuel(&mut local_shared, hidden);

    let mut declared: HashMap<Ident, Typ> = HashMap::new();
    let mut assigned: HashSet<Ident> = HashSet::new();
    for param in params.iter() {
        declared.insert(param.x.name.clone(), param.x.typ.clone());
        assigned.insert(param.x.name.clone());
    }

    let initial_snapshot_name = Arc::new("0_entry".to_string());

    let mut state = State {
        local_shared,
        commands: Vec::new(),
        snapshot_count: 0,
        latest_snapshot: initial_snapshot_name.clone(),
        snap_map: Vec::new(),
    };

    let stm = crate::sst_vars::stm_assign(&mut declared, &mut assigned, &mut HashSet::new(), stm);
    let mut stmts = stm_to_stmts(ctx, &mut state, &stm);

    if ctx.debug {
        let snapshot = Arc::new(StmtX::Snapshot(initial_snapshot_name));
        let mut new_stmts = vec![snapshot];
        new_stmts.append(&mut stmts);
        stmts = new_stmts;
    }

    let mut local = state.local_shared.clone();

    for ens in enss {
        let description = Some("postcondition not satisfied".to_string());
        let option_span = Arc::new(Some(Span { description, ..ens.span.clone() }));
        let ens_stmt = StmtX::Assert(option_span, exp_to_expr(ctx, ens));
        stmts.push(Arc::new(ens_stmt));
    }
    let assertion =
        if stmts.len() == 1 { stmts[0].clone() } else { Arc::new(StmtX::Block(Arc::new(stmts))) };

    for param in params.iter() {
        let typ_inv =
            typ_invariant(&param.x.typ, &ident_var(&suffix_local_id(&param.x.name)), false);
        if let Some(expr) = typ_inv {
            local.push(Arc::new(DeclX::Axiom(expr)));
        }
    }

    for req in reqs {
        local.push(Arc::new(DeclX::Axiom(exp_to_expr(ctx, req))));
    }

    let query = Arc::new(QueryX { local: Arc::new(local), assertion });
    state.commands.push(Arc::new(CommandX::CheckValid(query)));
    (Arc::new(state.commands), state.snap_map)
}
