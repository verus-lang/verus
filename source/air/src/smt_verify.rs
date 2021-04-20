use crate::ast::{
    BinaryOp, BindX, Constant, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query, Span,
    SpanOption, StmtX, Typ, TypX, UnaryOp, ValidityResult,
};
use crate::context::Context;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{Pattern, SatResult, Sort, Symbol};

pub const PREFIX_LABEL: &str = "%%location_label%%";

fn new_const<'ctx>(context: &mut Context<'ctx>, name: &String, typ: &Typ) -> Dynamic<'ctx> {
    match &**typ {
        TypX::Bool => Bool::new_const(context.context, name.clone()).into(),
        TypX::Int => Int::new_const(context.context, name.clone()).into(),
        TypX::Named(x) => {
            let sort = &context.typs[x];
            let fdecl = z3::FuncDecl::new(context.context, name.clone(), &[], sort);
            fdecl.apply(&[])
        }
    }
}

fn expr_to_smt<'ctx>(context: &mut Context<'ctx>, expr: &Expr) -> Dynamic<'ctx> {
    match &**expr {
        ExprX::Const(Constant::Bool(b)) => Bool::from_bool(&context.context, *b).into(),
        ExprX::Const(Constant::Nat(n)) => Int::from_str(&context.context, n).unwrap().into(),
        ExprX::Var(x) => match context.vars.get(x) {
            None => panic!("internal error: variable {} not found", x),
            Some(x) => x.clone(),
        },
        ExprX::Apply(x, exprs) => {
            let mut exprs_vec: Vec<Dynamic> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(expr_to_smt(context, expr));
            }
            let mut smt_exprs: Vec<&Dynamic> = Vec::new();
            for i in 0..exprs_vec.len() {
                smt_exprs.push(&exprs_vec[i]);
            }
            context.funs[x].apply(&smt_exprs)
        }
        ExprX::Unary(op, expr) => match op {
            UnaryOp::Not => Bool::not(&expr_to_smt(context, expr).as_bool().unwrap()).into(),
        },
        ExprX::Binary(op, lhs, rhs) => {
            let lh = expr_to_smt(context, lhs);
            let rh = expr_to_smt(context, rhs);
            match op {
                BinaryOp::Implies => lh.as_bool().unwrap().implies(&rh.as_bool().unwrap()).into(),
                BinaryOp::Eq => lh._eq(&rh).into(),
                BinaryOp::Le => lh.as_int().unwrap().le(&rh.as_int().unwrap()).into(),
                BinaryOp::Ge => lh.as_int().unwrap().ge(&rh.as_int().unwrap()).into(),
                BinaryOp::Lt => lh.as_int().unwrap().lt(&rh.as_int().unwrap()).into(),
                BinaryOp::Gt => lh.as_int().unwrap().gt(&rh.as_int().unwrap()).into(),
                BinaryOp::EuclideanDiv => lh.as_int().unwrap().div(&rh.as_int().unwrap()).into(),
                BinaryOp::EuclideanMod => lh.as_int().unwrap().rem(&rh.as_int().unwrap()).into(),
            }
        }
        ExprX::Multi(op @ MultiOp::And, exprs) | ExprX::Multi(op @ MultiOp::Or, exprs) => {
            let mut exprs_vec: Vec<Bool> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(expr_to_smt(context, expr).as_bool().unwrap());
            }
            let mut smt_exprs: Vec<&Bool> = Vec::new();
            for i in 0..exprs_vec.len() {
                smt_exprs.push(&exprs_vec[i]);
            }
            match op {
                MultiOp::And => Bool::and(&context.context, &smt_exprs).into(),
                MultiOp::Or => Bool::or(&context.context, &smt_exprs).into(),
                _ => panic!("internal error: MultiOp"),
            }
        }
        ExprX::Multi(MultiOp::Distinct, exprs) => {
            let mut exprs_vec: Vec<Dynamic> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(expr_to_smt(context, expr));
            }
            let mut smt_exprs: Vec<&Dynamic> = Vec::new();
            for i in 0..exprs_vec.len() {
                smt_exprs.push(&exprs_vec[i]);
            }
            Dynamic::distinct(&context.context, &smt_exprs[..]).into()
        }
        ExprX::Multi(op, exprs) => {
            let mut exprs_vec: Vec<Int> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(expr_to_smt(context, expr).as_int().unwrap());
            }
            let mut smt_exprs: Vec<&Int> = Vec::new();
            for i in 0..exprs_vec.len() {
                smt_exprs.push(&exprs_vec[i]);
            }
            match (op, &smt_exprs[..]) {
                (MultiOp::Add, _) => Int::add(&context.context, &smt_exprs).into(),
                (MultiOp::Sub, [unary]) => unary.unary_minus().into(),
                (MultiOp::Sub, _) => Int::sub(&context.context, &smt_exprs).into(),
                (MultiOp::Mul, _) => Int::mul(&context.context, &smt_exprs).into(),
                _ => panic!("internal error: MultiOp"),
            }
        }
        ExprX::IfElse(expr1, expr2, expr3) => {
            let smt1 = expr_to_smt(context, expr1);
            let smt2 = expr_to_smt(context, expr2);
            let smt3 = expr_to_smt(context, expr3);
            smt1.as_bool().unwrap().ite(&smt2, &smt3)
        }
        ExprX::Bind(bind, e1) => {
            let mut bound_vars: Vec<(Ident, Dynamic<'ctx>)> = Vec::new();
            match &**bind {
                BindX::Let(binders) => {
                    for binder in binders.iter() {
                        bound_vars.push((binder.name.clone(), expr_to_smt(context, &binder.a)));
                    }
                }
                BindX::Quant(_, binders, _) => {
                    for binder in binders.iter() {
                        let x_smt = new_const(context, &binder.name, &binder.a);
                        bound_vars.push((binder.name.clone(), x_smt));
                    }
                }
            }
            // Push our bindings
            // Remember any overwritten shadowed bindings so we can restore them
            let mut undos: HashMap<Ident, Option<Dynamic<'ctx>>> = HashMap::new();
            for (x, x_smt) in &bound_vars {
                let prev_var = context.vars.insert(x.clone(), x_smt.clone());
                undos.insert(x.clone(), prev_var);
            }
            // Translate subexpressions (in context with bound variables)
            let expr_smt = match &**bind {
                BindX::Let(_) => expr_to_smt(context, e1),
                BindX::Quant(quant, _, triggers) => {
                    let mut bounds: Vec<&Dynamic<'ctx>> = Vec::new();
                    for i in 0..bound_vars.len() {
                        bounds.push(&bound_vars[i].1);
                    }
                    let mut patterns: Vec<Pattern<'ctx>> = Vec::new();
                    for trigger in triggers.iter() {
                        let mut trigger_smt: Vec<Dynamic<'ctx>> = Vec::new();
                        for expr in trigger.iter() {
                            trigger_smt.push(expr_to_smt(context, expr));
                        }
                        let mut pattern: Vec<&Dynamic<'ctx>> = Vec::new();
                        for i in 0..trigger_smt.len() {
                            pattern.push(&trigger_smt[i]);
                        }
                        patterns.push(Pattern::new(context.context, &pattern));
                    }
                    let mut patterns_borrow: Vec<&Pattern<'ctx>> = Vec::new();
                    for i in 0..patterns.len() {
                        patterns_borrow.push(&patterns[i]);
                    }
                    let body = expr_to_smt(context, e1);
                    match quant {
                        Quant::Forall => {
                            z3::ast::forall_const(context.context, &bounds, &patterns_borrow, &body)
                        }
                        Quant::Exists => {
                            z3::ast::exists_const(context.context, &bounds, &patterns_borrow, &body)
                        }
                    }
                }
            };
            // Remove our bindings from the context, restore any shadowed bindings
            for (x, undo) in undos {
                match undo {
                    None => {
                        context.vars.remove(&x);
                    }
                    Some(prev) => {
                        context.vars.insert(x.clone(), prev);
                    }
                }
            }
            // Done
            expr_smt
        }
        ExprX::LabeledAssertion(_, _) => panic!("internal error: LabeledAssertion"),
    }
}

#[derive(Debug)]
pub(crate) struct AssertionInfo {
    pub(crate) span: SpanOption,
    pub(crate) label: Ident,
    pub(crate) decl: Decl,
}

fn label_asserts<'ctx>(
    context: &mut Context<'ctx>,
    infos: &mut Vec<AssertionInfo>,
    expr: &Expr,
) -> Expr {
    match &**expr {
        ExprX::Binary(BinaryOp::Implies, lhs, rhs) => {
            // asserts are on rhs
            Rc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs.clone(),
                label_asserts(context, infos, rhs),
            ))
        }
        ExprX::Multi(op @ MultiOp::And, exprs) | ExprX::Multi(op @ MultiOp::Or, exprs) => {
            let mut exprs_vec: Vec<Expr> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(label_asserts(context, infos, expr));
            }
            Rc::new(ExprX::Multi(*op, Rc::new(exprs_vec.into_boxed_slice())))
        }
        ExprX::LabeledAssertion(span, expr) => {
            let label = Rc::new(PREFIX_LABEL.to_string() + &infos.len().to_string());
            let decl = Rc::new(DeclX::Const(label.clone(), Rc::new(TypX::Bool)));
            let assertion_info = AssertionInfo { span: span.clone(), label: label.clone(), decl };
            infos.push(assertion_info);
            let lhs = Rc::new(ExprX::Var(label));
            // See comments about Z3_model_eval below for why do we use => instead of or.
            Rc::new(ExprX::Binary(BinaryOp::Implies, lhs, label_asserts(context, infos, expr)))
        }
        _ => expr.clone(),
    }
}

fn get_sort<'ctx>(context: &Context<'ctx>, typ: &Typ) -> Rc<Sort<'ctx>> {
    match &**typ {
        TypX::Bool => Rc::new(Sort::bool(context.context)),
        TypX::Int => Rc::new(Sort::int(context.context)),
        TypX::Named(x) => context.typs[x].clone(),
    }
}

pub(crate) fn smt_add_decl<'ctx>(context: &mut Context<'ctx>, decl: &Decl) {
    match &**decl {
        DeclX::Sort(x) => {
            context.smt_log.log_decl(decl);
            let sort = Sort::uninterpreted(context.context, Symbol::String((**x).clone()));
            let prev = context.typs.insert(x.clone(), Rc::new(sort));
            assert_eq!(prev, None);
        }
        DeclX::Datatypes(datatypes) => {
            context.smt_log.log_decl(decl);
            let mut names: HashSet<Ident> = HashSet::new();
            for datatype in datatypes.iter() {
                names.insert(datatype.name.clone());
            }
            let mut sorts: Vec<Vec<Vec<Rc<Sort>>>> = Vec::new();
            for datatype in datatypes.iter() {
                let mut sorts0: Vec<Vec<Rc<Sort>>> = Vec::new();
                for variant in datatype.a.iter() {
                    let mut sorts1: Vec<Rc<Sort>> = Vec::new();
                    for field in variant.a.iter() {
                        match &*field.a {
                            TypX::Named(x) if names.contains(x) => {
                                sorts1.push(Rc::new(Sort::bool(context.context))); // dummy sort
                            }
                            _ => {
                                sorts1.push(get_sort(context, &field.a));
                            }
                        }
                    }
                    sorts0.push(sorts1);
                }
                sorts.push(sorts0);
            }
            let mut builders = Vec::new();
            for i in 0..datatypes.len() {
                let datatype = &datatypes[i];
                let mut builder =
                    z3::DatatypeBuilder::new(&context.context, datatype.name.to_string());
                for j in 0..datatype.a.len() {
                    let variant = &datatype.a[j];
                    let mut smt_fields: Vec<(&str, z3::DatatypeAccessor)> = Vec::new();
                    for k in 0..variant.a.len() {
                        let field = &variant.a[k];
                        let sort = &sorts[i][j][k];
                        let accessor = match &*field.a {
                            TypX::Named(x) if names.contains(x) => {
                                z3::DatatypeAccessor::Datatype(z3::Symbol::String(x.to_string()))
                            }
                            _ => z3::DatatypeAccessor::Sort(sort),
                        };
                        smt_fields.push((field.name.as_str(), accessor));
                    }
                    builder = builder.variant(&variant.name.to_string(), smt_fields);
                }
                builders.push(builder);
            }
            let datatype_sorts = z3::datatype_builder::create_datatypes(builders);
            for (datatype, sort) in datatypes.iter().zip(datatype_sorts) {
                let prev = context.typs.insert(datatype.name.clone(), Rc::new(sort.sort));
                assert_eq!(prev, None);
                for (variant, smt_variant) in datatype.a.iter().zip(sort.variants) {
                    context.funs.insert(variant.name.clone(), Rc::new(smt_variant.constructor));
                    let is_variant = Rc::new("is-".to_string() + &variant.name.to_string());
                    context.funs.insert(is_variant, Rc::new(smt_variant.tester));
                    for (field, smt_field) in variant.a.iter().zip(smt_variant.accessors) {
                        context.funs.insert(field.name.clone(), Rc::new(smt_field));
                    }
                }
            }
        }
        DeclX::Const(x, typ) => {
            context.smt_log.log_decl(decl);
            let x_smt = new_const(context, x, typ);
            context.vars.insert(x.clone(), x_smt);
        }
        DeclX::Fun(x, typs, typ) => {
            context.smt_log.log_decl(decl);
            let sort = get_sort(context, typ);
            let sorts = crate::util::box_slice_map(typs, |t| get_sort(context, t));
            let mut sorts_borrow: Vec<&Sort> = Vec::new();
            for i in 0..sorts.len() {
                sorts_borrow.push(&*sorts[i]);
            }
            let fdecl = z3::FuncDecl::new(
                context.context,
                (**x).clone(),
                &sorts_borrow.into_boxed_slice(),
                &*sort,
            );
            context.funs.insert(x.clone(), Rc::new(fdecl));
        }
        DeclX::Var(_, _) => {}
        DeclX::Axiom(expr) => {
            context.smt_log.log_assert(&expr);
            let smt_expr = expr_to_smt(context, &expr).as_bool().unwrap();
            context.solver.assert(&smt_expr);
        }
    }
}

fn smt_check_assertion<'ctx>(
    context: &mut Context<'ctx>,
    infos: &Vec<AssertionInfo>,
    expr: &Expr,
) -> ValidityResult {
    let mut discovered_span = Rc::new(None);
    let not_expr = Rc::new(ExprX::Unary(UnaryOp::Not, expr.clone()));
    context.smt_log.log_assert(&not_expr);
    context.solver.assert(&expr_to_smt(context, &not_expr).as_bool().unwrap());

    context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
    context.set_z3_param_u32("rlimit", context.rlimit, false);

    context.smt_log.log_word("check-sat");
    let sat = context.solver.check();

    context.smt_log.log_set_option("rlimit", "0");
    context.set_z3_param_u32("rlimit", 0, false);

    match sat {
        SatResult::Unsat => ValidityResult::Valid,
        SatResult::Sat | SatResult::Unknown => {
            context.smt_log.log_word("get-model");
            let model = context.solver.get_model();
            match model {
                None => {
                    panic!("SMT solver did not generate a model");
                }
                Some(model) => {
                    // dbg!(&context.solver);
                    // println!("model = >>{}<<", model.to_string());
                    for info in infos.iter() {
                        /*
                        Unfortunately, the Rust Z3 crate's eval calls Z3_model_eval
                        with model_completion = true.
                        This hides exactly what we're interested in:
                        the set of variables that are actually assigned in the model.
                        It happens, though, that Z3 completes boolean variables in
                        the model with false,
                        so we can just look for the variables that evaluate to true.
                        */
                        let x_info = context.vars[&info.label].as_bool().unwrap();
                        if let Some(b) = model.eval(&x_info) {
                            if let Some(b2) = b.as_bool() {
                                if b2 {
                                    discovered_span = info.span.clone();
                                }
                            }
                        }
                    }
                }
            }
            ValidityResult::Invalid(discovered_span)
        }
    }
}

pub(crate) fn smt_check_query<'ctx>(context: &mut Context<'ctx>, query: &Query) -> ValidityResult {
    context.smt_log.log_push();
    context.solver.push();
    context.push_name_scope();

    // add query-local declarations
    for decl in query.local.iter() {
        if let Err(err) = crate::typecheck::add_decl(context, decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, decl);
    }

    // after lowering, there should be just one assertion
    let assertion = match &*query.assertion {
        StmtX::Assert(_, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };

    // add labels to assertions for error reporting
    let mut infos: Vec<AssertionInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &assertion);
    for info in &infos {
        if let Some(Span { as_string, .. }) = &*info.span {
            context.smt_log.comment(as_string);
        }
        if let Err(err) = crate::typecheck::add_decl(context, &info.decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, &info.decl);
    }

    // check assertion
    let result = smt_check_assertion(context, &infos, &labeled_assertion);

    // clean up
    context.pop_name_scope();
    context.smt_log.log_pop();
    context.solver.pop(1);
    result
}
