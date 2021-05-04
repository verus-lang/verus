use crate::ast::{BinaryOp, Ident, IntRange, Mode, Params, Typ, UnaryOp};
use crate::context::Ctx;
use crate::def::{
    prefix_ensures, prefix_fuel_id, prefix_requires, suffix_global_id, suffix_local_id, Spanned,
    FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_DEFAULTS, FUEL_ID, SNAPSHOT_CALL,
};
use crate::sst::{BndX, Dest, Exp, ExpX, Stm, StmX};
use crate::util::vec_map;
use air::ast::{
    BindX, BinderX, Binders, CommandX, Commands, Constant, Decl, DeclX, Expr, ExprX, MultiOp,
    Quant, QueryX, Span, Stmt, StmtX, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_typ, ident_var, int_typ, str_apply, str_ident,
    str_typ, str_var, string_var,
};
use std::rc::Rc;

pub(crate) fn typ_to_air(typ: &Typ) -> air::ast::Typ {
    match typ {
        Typ::Int(_) => int_typ(),
        Typ::Bool => bool_typ(),
        Typ::Path(segments) => ident_typ(&Rc::new(
            segments.iter().map(|x| (**x).as_str()).collect::<Vec<_>>().join("::"),
        )),
    }
}

pub(crate) fn apply_range_fun(name: &str, range: &IntRange, expr: &Expr) -> Expr {
    match range {
        IntRange::Int | IntRange::Nat => str_apply(name, &vec![expr.clone()]),
        IntRange::U(range) | IntRange::I(range) => {
            let bits = Constant::Nat(Rc::new(range.to_string()));
            str_apply(name, &vec![Rc::new(ExprX::Const(bits)), expr.clone()])
        }
        IntRange::USize | IntRange::ISize => {
            let bits = str_var(crate::def::ARCH_SIZE);
            str_apply(name, &vec![bits, expr.clone()])
        }
    }
}

// If expr has type typ, what can we assume to be true about expr?
pub(crate) fn typ_invariant(typ: &Typ, expr: &Expr) -> Option<Expr> {
    match typ {
        Typ::Int(IntRange::Int) => None,
        Typ::Int(IntRange::Nat) => {
            let zero = Rc::new(ExprX::Const(Constant::Nat(Rc::new("0".to_string()))));
            Some(Rc::new(ExprX::Binary(air::ast::BinaryOp::Le, zero, expr.clone())))
        }
        Typ::Int(range) => {
            let f_name = match range {
                IntRange::Int => panic!("internal error: Int"),
                IntRange::Nat => panic!("internal error: Int"),
                IntRange::U(_) | IntRange::USize => crate::def::U_INV,
                IntRange::I(_) | IntRange::ISize => crate::def::I_INV,
            };
            Some(apply_range_fun(&f_name, &range, &expr))
        }
        _ => None,
    }
}

pub(crate) fn exp_to_expr(exp: &Exp) -> Expr {
    match &exp.x {
        ExpX::Const(c) => {
            let expr = Rc::new(ExprX::Const(c.clone()));
            expr
        }
        ExpX::Var(x) => string_var(&suffix_local_id(x)),
        ExpX::Old(span, x) => Rc::new(ExprX::Old(span.clone(), suffix_local_id(x))),
        ExpX::Call(x, args) => {
            let name = suffix_global_id(&x);
            ident_apply(&name, &vec_map(args, exp_to_expr))
        }
        ExpX::Unary(op, exp) => match op {
            UnaryOp::Not => Rc::new(ExprX::Unary(air::ast::UnaryOp::Not, exp_to_expr(exp))),
            UnaryOp::Trigger(_) => exp_to_expr(exp),
            UnaryOp::Clip(IntRange::Int) => exp_to_expr(exp),
            UnaryOp::Clip(range) => {
                let expr = exp_to_expr(exp);
                let f_name = match range {
                    IntRange::Int => panic!("internal error: Int"),
                    IntRange::Nat => crate::def::NAT_CLIP,
                    IntRange::U(_) | IntRange::USize => crate::def::U_CLIP,
                    IntRange::I(_) | IntRange::ISize => crate::def::I_CLIP,
                };
                apply_range_fun(&f_name, &range, &expr)
            }
        },
        ExpX::Binary(op, lhs, rhs) => {
            let lh = exp_to_expr(lhs);
            let rh = exp_to_expr(rhs);
            let expx = match op {
                BinaryOp::And => ExprX::Multi(MultiOp::And, Rc::new(vec![lh, rh])),
                BinaryOp::Or => ExprX::Multi(MultiOp::Or, Rc::new(vec![lh, rh])),
                BinaryOp::Add => ExprX::Multi(MultiOp::Add, Rc::new(vec![lh, rh])),
                BinaryOp::Sub => ExprX::Multi(MultiOp::Sub, Rc::new(vec![lh, rh])),
                BinaryOp::Mul => ExprX::Multi(MultiOp::Mul, Rc::new(vec![lh, rh])),
                BinaryOp::Ne => {
                    let eq = ExprX::Binary(air::ast::BinaryOp::Eq, lh, rh);
                    ExprX::Unary(air::ast::UnaryOp::Not, Rc::new(eq))
                }
                _ => {
                    let aop = match op {
                        BinaryOp::And => panic!("internal error"),
                        BinaryOp::Or => panic!("internal error"),
                        BinaryOp::Implies => air::ast::BinaryOp::Implies,
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
            Rc::new(expx)
        }
        ExpX::If(e1, e2, e3) => {
            Rc::new(ExprX::IfElse(exp_to_expr(e1), exp_to_expr(e2), exp_to_expr(e3)))
        }
        ExpX::Field { lhs, datatype_name: _, field_name: name } => {
            // TODO: this should include datatype_name in the function name
            let lh = exp_to_expr(lhs);
            Rc::new(ExprX::Apply(name.clone(), Rc::new(vec![lh])))
        }
        ExpX::Bind(bnd, exp) => match &bnd.x {
            BndX::Let(binders) => {
                let expr = exp_to_expr(exp);
                let binders = vec_map(&*binders, |b| {
                    Rc::new(BinderX { name: suffix_local_id(&b.name), a: exp_to_expr(&b.a) })
                });
                Rc::new(ExprX::Bind(Rc::new(BindX::Let(Rc::new(binders))), expr))
            }
            BndX::Quant(quant, binders, trigs) => {
                let expr = exp_to_expr(exp);
                let binders = vec_map(&*binders, |b| {
                    Rc::new(BinderX { name: suffix_local_id(&b.name), a: typ_to_air(&b.a) })
                });
                let triggers = vec_map(&*trigs, |trig| Rc::new(vec_map(trig, exp_to_expr)));
                Rc::new(ExprX::Bind(
                    Rc::new(BindX::Quant(*quant, Rc::new(binders), Rc::new(triggers))),
                    expr,
                ))
            }
        },
    }
}

pub fn stm_to_stmts(ctx: &Ctx, stm: &Stm, decls: &mut Vec<Decl>) -> Vec<Stmt> {
    match &stm.x {
        StmX::Call(x, args, dest) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            let func = &ctx.func_map[x];
            if func.x.require.len() > 0 {
                let f_req = prefix_requires(&func.x.name);
                let args = Rc::new(vec_map(args, exp_to_expr));
                let e_req = Rc::new(ExprX::Apply(f_req, args));
                let description = Some("precondition not satisfied".to_string());
                let option_span = Rc::new(Some(Span { description, ..stm.span.clone() }));
                stmts.push(Rc::new(StmtX::Assert(option_span, e_req)));
            }
            let mut ens_args: Vec<Expr>;
            match dest {
                None => {
                    ens_args = vec_map(args, exp_to_expr);
                }
                Some(Dest { var, mutable }) => {
                    ens_args = Vec::new();
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
                        ens_args.push(exp_to_expr(&arg_x));
                    }
                    if overwrite {
                        stmts.push(Rc::new(StmtX::Snapshot(str_ident(SNAPSHOT_CALL))));
                    }
                    ens_args.push(Rc::new(ExprX::Var(x.clone())));
                    if *mutable {
                        let havoc = StmtX::Havoc(x.clone());
                        stmts.push(Rc::new(havoc));
                    }
                }
            }
            if func.x.ensure.len() > 0 {
                let f_ens = prefix_ensures(&func.x.name);
                let e_ens = Rc::new(ExprX::Apply(f_ens, Rc::new(ens_args)));
                stmts.push(Rc::new(StmtX::Assume(e_ens)));
            }
            vec![Rc::new(StmtX::Block(Rc::new(stmts)))] // wrap in block for readability
        }
        StmX::Assume(expr) => vec![Rc::new(StmtX::Assume(exp_to_expr(&expr)))],
        StmX::Assert(expr) => {
            let air_expr = exp_to_expr(&expr);
            let option_span = Rc::new(Some(stm.span.clone()));
            vec![Rc::new(StmtX::Assert(option_span, air_expr))]
        }
        StmX::Decl { ident, typ, mutable } => {
            decls.push(if *mutable {
                Rc::new(DeclX::Var(suffix_local_id(&ident), typ_to_air(&typ)))
            } else {
                Rc::new(DeclX::Const(suffix_local_id(&ident), typ_to_air(&typ)))
            });
            vec![]
        }
        StmX::Assign(lhs, rhs) => {
            let ident = match &lhs.x {
                ExpX::Var(ident) => ident,
                _ => panic!("unexpected lhs {:?} in assign", lhs),
            };
            vec![Rc::new(StmtX::Assign(suffix_local_id(&ident), exp_to_expr(rhs)))]
        }
        StmX::If(cond, lhs, rhs) => {
            let pos_cond = exp_to_expr(&cond);
            let neg_cond = Rc::new(ExprX::Unary(air::ast::UnaryOp::Not, pos_cond.clone()));
            let pos_assume = Rc::new(StmtX::Assume(pos_cond));
            let neg_assume = Rc::new(StmtX::Assume(neg_cond));
            let mut lhss = stm_to_stmts(ctx, lhs, decls);
            let mut rhss = match rhs {
                None => vec![],
                Some(rhs) => stm_to_stmts(ctx, rhs, decls),
            };
            lhss.insert(0, pos_assume);
            rhss.insert(0, neg_assume);
            let lblock = Rc::new(StmtX::Block(Rc::new(lhss)));
            let rblock = Rc::new(StmtX::Block(Rc::new(rhss)));
            vec![Rc::new(StmtX::Switch(Rc::new(vec![lblock, rblock])))]
        }
        StmX::Fuel(x, fuel) => {
            if *fuel == 0 {
                vec![]
            } else {
                // (assume (fuel_bool fuel%f))
                let id_fuel = prefix_fuel_id(&x);
                let expr_fuel_bool = str_apply(&FUEL_BOOL, &vec![ident_var(&id_fuel)]);
                vec![Rc::new(StmtX::Assume(expr_fuel_bool))]
            }
        }
        StmX::Block(stms) => stms.iter().map(|s| stm_to_stmts(ctx, s, decls)).flatten().collect(),
    }
}

fn set_fuel(local: &mut Vec<Decl>, hidden: &Vec<Ident>) {
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
        disjuncts.push(Rc::new(ExprX::Binary(eq, fuel_bool.clone(), fuel_bool_default)));

        // ... || id == hidden1 || id == hidden2 || ...
        for hide in hidden {
            let x_hide = ident_var(&prefix_fuel_id(&hide));
            disjuncts.push(Rc::new(ExprX::Binary(air::ast::BinaryOp::Eq, x_id.clone(), x_hide)));
        }

        // (forall ((id FuelId)) ...)
        let trigger: Trigger = Rc::new(vec![fuel_bool.clone()]);
        let triggers: Triggers = Rc::new(vec![trigger]);
        let binders: Binders<air::ast::Typ> = Rc::new(vec![ident_binder(&id, &str_typ(FUEL_ID))]);
        let bind = Rc::new(BindX::Quant(Quant::Forall, binders, triggers));
        let or = Rc::new(ExprX::Multi(air::ast::MultiOp::Or, Rc::new(disjuncts)));
        Rc::new(ExprX::Bind(bind, or))
    };
    local.push(Rc::new(DeclX::Axiom(fuel_expr)));
}

pub fn stm_to_air(
    ctx: &Ctx,
    params: &Params,
    ret: &Option<(Ident, Typ, Mode)>,
    hidden: &Vec<Ident>,
    reqs: &Vec<Exp>,
    enss: &Vec<Exp>,
    stm: &Stm,
) -> Commands {
    let mut local: Vec<Decl> = vec_map(params, |param| {
        Rc::new(DeclX::Const(suffix_local_id(&param.x.name), typ_to_air(&param.x.typ)))
    });
    match ret {
        None => {}
        Some((x, typ, _)) => {
            local.push(Rc::new(DeclX::Const(suffix_local_id(&x), typ_to_air(&typ))));
        }
    }

    let mut stmts = stm_to_stmts(ctx, &stm, &mut local);
    for ens in enss {
        let description = Some("postcondition not satisfied".to_string());
        let option_span = Rc::new(Some(Span { description, ..ens.span.clone() }));
        let ens_stmt = StmtX::Assert(option_span, exp_to_expr(ens));
        stmts.push(Rc::new(ens_stmt));
    }
    let assertion =
        if stmts.len() == 1 { stmts[0].clone() } else { Rc::new(StmtX::Block(Rc::new(stmts))) };

    set_fuel(&mut local, hidden);
    for param in params.iter() {
        let typ_inv = typ_invariant(&param.x.typ, &ident_var(&suffix_local_id(&param.x.name)));
        if let Some(expr) = typ_inv {
            local.push(Rc::new(DeclX::Axiom(expr)));
        }
    }
    for req in reqs {
        local.push(Rc::new(DeclX::Axiom(exp_to_expr(req))));
    }
    let query = Rc::new(QueryX { local: Rc::new(local), assertion });
    let command = Rc::new(CommandX::CheckValid(query));
    Rc::new(vec![command])
}
