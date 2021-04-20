use crate::ast::{BinaryOp, Ident, Params, Typ, UnaryOp};
use crate::def::{
    prefix_fuel_id, suffix_global_id, suffix_local_id, FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_DEFAULTS,
    FUEL_ID,
};
use crate::sst::{Exp, ExpX, Stm, StmX};
use crate::util::box_slice_map;
use air::ast::{
    BindX, Binders, CommandX, Commands, Decl, DeclX, Expr, ExprX, MultiOp, Quant, QueryX, Stmt,
    StmtX, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_var, int_typ, str_apply_vec, str_ident, str_typ,
    str_var, string_var,
};
use std::rc::Rc;

pub fn typ_to_air(typ: &Typ) -> air::ast::Typ {
    match typ {
        Typ::Int => int_typ(),
        Typ::Bool => bool_typ(),
    }
}

pub(crate) fn exp_to_expr(exp: &Exp) -> Expr {
    match &exp.x {
        ExpX::Const(c) => {
            let expr = Rc::new(ExprX::Const(c.clone()));
            expr
        }
        ExpX::Var(x) => string_var(&suffix_local_id(x)),
        ExpX::Call(x, args) => {
            let name = suffix_global_id(&x);
            ident_apply(&name, &box_slice_map(args, exp_to_expr))
        }
        ExpX::Unary(op, exp) => match op {
            UnaryOp::Not => Rc::new(ExprX::Unary(air::ast::UnaryOp::Not, exp_to_expr(exp))),
        },
        ExpX::Binary(op, lhs, rhs) => {
            let lh = exp_to_expr(lhs);
            let rh = exp_to_expr(rhs);
            let expx = match op {
                BinaryOp::And => ExprX::Multi(MultiOp::And, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Or => ExprX::Multi(MultiOp::Or, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Add => ExprX::Multi(MultiOp::Add, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Sub => ExprX::Multi(MultiOp::Sub, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Mul => ExprX::Multi(MultiOp::Mul, Rc::new(Box::new([lh, rh]))),
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
    }
}

pub fn stm_to_stmt(stm: &Stm, decls: &mut Vec<Decl>) -> Option<Stmt> {
    match &stm.x {
        StmX::Assume(expr) => Some(Rc::new(StmtX::Assume(exp_to_expr(&expr)))),
        StmX::Assert(expr) => {
            let air_expr = exp_to_expr(&expr);
            let option_span = Rc::new(Some(stm.span.clone()));
            Some(Rc::new(StmtX::Assert(option_span, air_expr)))
        }
        StmX::Decl { ident, typ, mutable } => {
            decls.push(if *mutable {
                Rc::new(DeclX::Var(suffix_local_id(&ident), typ_to_air(&typ)))
            } else {
                Rc::new(DeclX::Const(suffix_local_id(&ident), typ_to_air(&typ)))
            });
            None
        }
        StmX::Assign(lhs, rhs) => {
            let ident = match &lhs.x {
                ExpX::Var(ident) => ident,
                _ => panic!("unexpected lhs {:?} in assign", lhs),
            };
            Some(Rc::new(StmtX::Assign(suffix_local_id(&ident), exp_to_expr(rhs))))
        }
        StmX::Fuel(x, fuel) => {
            if *fuel == 0 {
                None
            } else {
                // (assume (fuel_bool fuel%f))
                let id_fuel = prefix_fuel_id(&x);
                let expr_fuel_bool = str_apply_vec(&FUEL_BOOL, &vec![ident_var(&id_fuel)]);
                Some(Rc::new(StmtX::Assume(expr_fuel_bool)))
            }
        }
        StmX::Block(stms) => {
            let stmts = stms.iter().filter_map(|s| stm_to_stmt(s, decls)).collect::<Vec<_>>();
            Some(Rc::new(StmtX::Block(Rc::new(stmts.into_boxed_slice()))))
        }
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
        let fuel_bool = str_apply_vec(&FUEL_BOOL, &vec![x_id.clone()]);
        let fuel_bool_default = str_apply_vec(&FUEL_BOOL_DEFAULT, &vec![x_id.clone()]);
        let eq = air::ast::BinaryOp::Eq;
        disjuncts.push(Rc::new(ExprX::Binary(eq, fuel_bool.clone(), fuel_bool_default)));

        // ... || id == hidden1 || id == hidden2 || ...
        for hide in hidden {
            let x_hide = ident_var(&prefix_fuel_id(&hide));
            disjuncts.push(Rc::new(ExprX::Binary(air::ast::BinaryOp::Eq, x_id.clone(), x_hide)));
        }

        // (forall ((id FuelId)) ...)
        let trigger: Trigger = Rc::new(Box::new([fuel_bool.clone()]));
        let triggers: Triggers = Rc::new(Box::new([trigger]));
        let binders: Binders<air::ast::Typ> =
            Rc::new(Box::new([ident_binder(&id, &str_typ(FUEL_ID))]));
        let bind = Rc::new(BindX::Quant(Quant::Forall, binders, triggers));
        let or =
            Rc::new(ExprX::Multi(air::ast::MultiOp::Or, Rc::new(disjuncts.into_boxed_slice())));
        Rc::new(ExprX::Bind(bind, or))
    };
    local.push(Rc::new(DeclX::Axiom(fuel_expr)));
}

pub fn stm_to_air(params: &Params, hidden: &Vec<Ident>, stm: &Stm) -> Commands {
    let mut local: Vec<Decl> = params
        .iter()
        .map(|param| {
            Rc::new(DeclX::Const(suffix_local_id(&param.x.name), typ_to_air(&param.x.typ)))
        })
        .collect();
    let assertion = stm_to_stmt(&stm, &mut local)
        .unwrap_or(Rc::new(StmtX::Block(Rc::new(vec![].into_boxed_slice()))));
    set_fuel(&mut local, hidden);
    let query = Rc::new(QueryX { local: Rc::new(local.into_boxed_slice()), assertion });
    let command = Rc::new(CommandX::CheckValid(query));
    Rc::new(Box::new([command]))
}
