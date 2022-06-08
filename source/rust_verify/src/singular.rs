use air::ast::{BinaryOp, Command, CommandX, Constant, Expr, ExprX, Ident, MultiOp, Query};
use air::context::{QueryContext, ValidityResult};
use air::printer::Printer;
use air::singular_manager::SingularManager;
use sise::Node;
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) fn expr_to_singular(
    expr: &Expr,
    tmp_idx: &mut u32,
    node_map: &mut HashMap<Node, Ident>,
) -> String {
    match &**expr {
        ExprX::Const(Constant::Nat(n)) => n.to_string(),
        ExprX::Var(x) => x.to_string(),
        ExprX::Binary(BinaryOp::EuclideanMod, lhs, rhs) => {
            // x % y ->  x - y*tmp
            let pp = Printer::new(false);
            let key = pp.expr_to_node(expr);
            let value = node_map.get(&key);
            let t = match value {
                Some(tmp_var) => tmp_var.to_string(),
                None => {
                    let tmp_new = Arc::new(format!("tmp_{}", tmp_idx.to_string()));
                    *tmp_idx += 1;
                    node_map.insert(key, tmp_new.clone());
                    tmp_new.to_string()
                }
            };
            let s1 = expr_to_singular(lhs, tmp_idx, node_map);
            let s2 = expr_to_singular(rhs, tmp_idx, node_map);

            format!("(({}) - (({})*({})))", s1, s2, t)
        }
        ExprX::Binary(BinaryOp::Eq, lhs, rhs) => {
            let s1 = expr_to_singular(lhs, tmp_idx, node_map);
            let s2 = expr_to_singular(rhs, tmp_idx, node_map);
            format!("({}) - ({})", s1, s2)
        }
        ExprX::Multi(op, exprs) => {
            let mut ss = vec![];
            let sop = match op {
                MultiOp::Add => ") + (",
                MultiOp::Sub => ") - (",
                MultiOp::Mul => ") * (", // still reachable with constant multiplication
                _ => panic!("unsupported singular multi op"),
            };
            for e in &**exprs {
                ss.push(expr_to_singular(&e, tmp_idx, node_map));
            }
            format!("(({}))", ss.join(sop))
        }
        ExprX::Apply(fname, exprs) => {
            if vir::def::MUL == (**fname).as_str() {
                return expr_to_singular(
                    &Arc::new(ExprX::Multi(MultiOp::Mul, exprs.clone())),
                    tmp_idx,
                    node_map,
                );
            } else if vir::def::EUC_MOD == (**fname).as_str() {
                if exprs.len() != 2 {
                    panic!("internal error: singular mod translation");
                }
                return expr_to_singular(
                    &Arc::new(ExprX::Binary(
                        BinaryOp::EuclideanMod,
                        exprs[0].clone(),
                        exprs[1].clone(),
                    )),
                    tmp_idx,
                    node_map,
                );
            } else {
                // treat as uninterpreted functions
                let pp = Printer::new(false);
                let key = pp.expr_to_node(expr);
                let value = node_map.get(&key);
                match value {
                    Some(tmp_var) => tmp_var.to_string(),
                    None => {
                        let tmp_new = Arc::new(format!("tmp_{}", tmp_idx.to_string()));
                        *tmp_idx += 1;
                        node_map.insert(key, tmp_new.clone());
                        tmp_new.to_string()
                    }
                }
            }
        }
        _ => panic!("unsupported singular expression: {:?}", expr),
    }
}

pub fn singular_printer(vars: &Vec<Ident>, req_exprs: &Vec<Expr>, ens_exprs: &Vec<Expr>) -> String {
    let mut tmp_count: u32 = 0; // count the number of required tmp vars
    let mut vars2: Vec<String> = vec![];
    let mut node_map: HashMap<Node, Ident> = HashMap::new(); // for uninterpreted functions and mod translation

    if ens_exprs.len() != 1 {
        panic!("Singular ensures expression: only one ensures is assumed")
    }

    // Using @ is safe. For example, `poly g1 = x2+y3` is translated as poly `g1 = x^2 + y^3`
    for v in vars {
        let mut v2 = v.to_string();
        v2.push('@');
        vars2.push(v2);
    }

    // gather polynomials that will be the basis of ideal
    // for requires,  equality -> register ideal (rhs - lhs)
    let mut ideals_singular: Vec<String> = vec![];
    if req_exprs.len() == 0 {
        tmp_count = tmp_count + 1;
        ideals_singular.push(format!("tmp_0"));
    } else {
        for req in req_exprs {
            if let ExprX::Binary(BinaryOp::Eq, _, _) = &**req {
            } else {
                panic!("integer ring expression: equality assumed");
            }
            ideals_singular.push(expr_to_singular(&req, &mut tmp_count, &mut node_map));
        }
    }

    let mut reduces_singular: Vec<String> = vec![];
    let ens = ens_exprs[0].clone();
    if let ExprX::Binary(BinaryOp::Eq, lhs, zero) = &*ens {
        // for `mod` ensure expr, "X % m == 0" assumed
        // RHS is required to be Zero to prevent proving something like `5m % m == 3m`
        match &**lhs {
            ExprX::Apply(fname, exprs) if vir::def::EUC_MOD == (**fname).as_str() => {
                // push 'm' to ideal basis
                ideals_singular.push(expr_to_singular(&exprs[1], &mut tmp_count, &mut node_map));
                // reduce 'X' with generated ideal
                reduces_singular.push(expr_to_singular(&exprs[0], &mut tmp_count, &mut node_map));
                if let ExprX::Const(Constant::Nat(ss)) = &**zero {
                    assert_eq!(**ss, "0".to_string());
                } else {
                    panic!("Singular expression: equality with zero assumed");
                }
            }
            _ => reduces_singular.push(expr_to_singular(&ens, &mut tmp_count, &mut node_map)),
        }
    } else {
        panic!("Singular ensures expression: equality assumed");
    }

    let ring_string;
    if tmp_count == 0 {
        ring_string = format!("ring r=integer,({}),dp", vars2.join(","));
    } else {
        // create tmp variable for uninterpreted functions and mod operator.
        let mut tmp_vars: Vec<String> = vec![];
        for i in 0..(tmp_count + 1) {
            tmp_vars.push(format!("tmp_{}", i.to_string()));
        }
        ring_string = format!("ring r=integer,({},{}),dp", vars2.join(","), tmp_vars.join(","),);
    }
    let ideal_string = format!("{}{}", "ideal ideal_I = ", ideals_singular.join(","));
    let ideal_to_groebner = String::from("ideal ideal_G = groebner(ideal_I)");
    let reduce_string = format!("{}{}{}", "reduce(", reduces_singular[0], ", ideal_G)");
    let quit_string = String::from("quit");

    let res = format!(
        "{}; {}; {}; {}; {};",
        ring_string, ideal_string, ideal_to_groebner, reduce_string, quit_string
    );
    res
}

pub fn check_singular_valid(
    _context: &mut air::context::Context,
    command: &Command,
    _query_context: QueryContext<'_, '_>,
    // &mut self,
    // vars: Vec<String>,
    // enss: Vec<Expr>,
    // reqs: Vec<Expr>,
    // s: &Span,
) -> ValidityResult {
    let query: Query = if let CommandX::CheckValid(query) = &**command {
        query.clone()
    } else {
        panic!("singular")
    };

    let decl = query.local.clone();
    let statement = query.assertion.clone();

    let mut vars: Vec<Ident> = vec![];
    let mut enss = vec![];
    let mut reqs = vec![];

    // just a tmp var
    let mut err = Arc::new(air::errors::ErrorX {
        msg: "msg".to_string().into(),
        spans: vec![],
        labels: Vec::new(),
    });

    for d in &**decl {
        if let air::ast::DeclX::Var(name, _typ) = &**d {
            vars.push(name.clone());
        }
    }

    if let air::ast::StmtX::Block(stmts) = &*statement {
        for stm in &**stmts {
            match &**stm {
                air::ast::StmtX::Assume(exp) => {
                    reqs.push(exp.clone());
                }
                air::ast::StmtX::Assert(error, exp) => {
                    enss.push(exp.clone());
                    err = error.clone();
                }
                _ => {
                    panic!("internal error");
                }
            };
        }
    };

    let query = singular_printer(&vars, &reqs, &enss);

    // air::singular_manager::log_singular(context, &vars, &reqs, &enss, &query);

    let singular_manager = SingularManager::new();
    let mut singular_process = singular_manager.launch();
    let res = singular_process.send_commands(query.as_bytes().to_vec());
    if (res.len() == 1) && (res[0] == "0") {
        ValidityResult::Valid
    } else if res[0].contains("?") {
        ValidityResult::UnexpectedOutput(String::from(format!(
            "{} \ngenerated singular query: {}",
            res[0].as_str(),
            query
        )))
    } else {
        ValidityResult::Invalid(
            None,
            air::errors::error(
                format!(
                    "Ensures polynomial failed to be reduced to zero: reduced polynomial is {}\n generated singular query: {} ",
                    res[0].as_str(),
                    query
                ),
                &err.spans[0], // TODO
            ),
        )
    }
}
