use air::ast::{BinaryOp, Command, CommandX, Constant, Expr, ExprX, Ident, MultiOp, Query};
use air::context::{QueryContext, ValidityResult};
use air::errors::Error;
use air::printer::Printer;
use air::singular_manager::SingularManager;
use sise::Node;
use std::collections::HashMap;
use std::sync::Arc;

// Singular reserved keyword
const RING_DECL: &str = "ring";
const IDEAL_DECL: &str = "ideal";
const DP_ORDERING: &str = "dp";
const GROEBNER_APPLY: &str = "groebner";
const REDUCE_APPLY: &str = "reduce";
const TO_INTEGER_RING: &str = "integer";
const QUIT_SINGULAR: &str = "quit";

// Verus-side reserved variable names for encoding purposes
const RING_R: &str = "ring_R";
const IDEAL_I: &str = "ideal_I";
const IDEAL_G: &str = "ideal_G";
const TMP_PREFIX: &str = "singular_tmp_";

fn assert_not_reserved(name: String) {
    let reserved_keywords = vec![
        RING_DECL,
        IDEAL_DECL,
        DP_ORDERING,
        GROEBNER_APPLY,
        REDUCE_APPLY,
        TO_INTEGER_RING,
        QUIT_SINGULAR,
        RING_R,
        IDEAL_I,
        IDEAL_G,
    ];
    for keyword in reserved_keywords {
        if name == keyword {
            panic!("Integer_ring/Singular: Usage of reserved keyword at variable name: {}", name);
        }
    }
    if name.starts_with(TMP_PREFIX) {
        panic!("Integer_ring/Singular: Usage of reserved prefix `{}` at {}", TMP_PREFIX, name);
    }
}

pub(crate) fn expr_to_singular(
    expr: &Expr,
    tmp_idx: &mut u32,
    node_map: &mut HashMap<Node, Ident>,
) -> Result<String, ()> {
    let result_string = match &**expr {
        ExprX::Const(Constant::Nat(n)) => n.to_string(),
        ExprX::Var(x) => {
            assert_not_reserved(x.to_string());
            x.to_string()
        }
        ExprX::Binary(BinaryOp::EuclideanMod, lhs, rhs) => {
            // x % y ->  x - y*tmp
            let pp = Printer::new(false);
            let key = pp.expr_to_node(expr);
            let value = node_map.get(&key);
            let t = match value {
                Some(tmp_var) => tmp_var.to_string(),
                None => {
                    let tmp_new = Arc::new(format!("{}{}", TMP_PREFIX, tmp_idx.to_string()));
                    *tmp_idx += 1;
                    node_map.insert(key, tmp_new.clone());
                    tmp_new.to_string()
                }
            };
            let s1 = expr_to_singular(lhs, tmp_idx, node_map)?;
            let s2 = expr_to_singular(rhs, tmp_idx, node_map)?;

            format!("(({}) - (({})*({})))", s1, s2, t)
        }
        ExprX::Binary(BinaryOp::Eq, lhs, rhs) => {
            let s1 = expr_to_singular(lhs, tmp_idx, node_map)?;
            let s2 = expr_to_singular(rhs, tmp_idx, node_map)?;
            format!("({}) - ({})", s1, s2)
        }
        ExprX::Multi(op, exprs) => {
            let mut ss = vec![];
            let sop = match op {
                MultiOp::Add => " + ",
                MultiOp::Sub => " - ",
                MultiOp::Mul => " * ", // still reachable with constant multiplication
                _ => panic!("unsupported integer_ring operator: {:?}", op.clone()),
            };
            for e in &**exprs {
                ss.push(format!("({})", expr_to_singular(&e, tmp_idx, node_map)?));
            }
            format!("({})", ss.join(sop))
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
                        let tmp_new = Arc::new(format!("{}{}", TMP_PREFIX, tmp_idx.to_string()));
                        *tmp_idx += 1;
                        node_map.insert(key, tmp_new.clone());
                        tmp_new.to_string()
                    }
                }
            }
        }
        _ => return Err(()),
    };
    Ok(result_string)
}

pub fn singular_printer(
    vars: &Vec<Ident>,
    req_exprs: &Vec<(Expr, Error)>,
    ens_expr: &(Expr, Error),
) -> Result<String, Error> {
    let mut tmp_count: u32 = 0; // count the number of required tmp vars
    let mut vars2: Vec<String> = vec![];
    let mut node_map: HashMap<Node, Ident> = HashMap::new(); // for uninterpreted functions and mod translation

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
        ideals_singular.push(format!("{}0", TMP_PREFIX));
    } else {
        for (req, err) in req_exprs {
            if let ExprX::Binary(BinaryOp::Eq, _, _) = &**req {
            } else {
                return Err(err.clone());
            }
            match expr_to_singular(&req, &mut tmp_count, &mut node_map) {
                Ok(translated) => ideals_singular.push(translated),
                Err(_) => return Err(err.clone()),
            }
        }
    }

    let mut reduces_singular: Vec<String> = vec![];
    let (ens, ens_err) = ens_expr;
    if let ExprX::Binary(BinaryOp::Eq, lhs, zero) = &**ens {
        // for `mod` ensure expr, "X % m == 0" assumed
        // RHS is required to be Zero to prevent proving something like `5m % m == 3m`
        match &**lhs {
            ExprX::Apply(fname, exprs) if vir::def::EUC_MOD == (**fname).as_str() => {
                // push 'm' to ideal basis
                match expr_to_singular(&exprs[1], &mut tmp_count, &mut node_map) {
                    Ok(translated) => ideals_singular.push(translated),
                    Err(_) => return Err(ens_err.clone()),
                };

                // reduce 'X' with generated ideal
                match expr_to_singular(&exprs[0], &mut tmp_count, &mut node_map) {
                    Ok(translated) => reduces_singular.push(translated),
                    Err(_) => return Err(ens_err.clone()),
                };

                if let ExprX::Const(Constant::Nat(ss)) = &**zero {
                    if **ss != "0".to_string() {
                        return Err(ens_err.clone()); // "Singular expression: equality with zero assumed"
                    }
                } else {
                    return Err(ens_err.clone()); // "Singular expression: equality with zero assumed"
                }
            }
            _ => match expr_to_singular(&ens, &mut tmp_count, &mut node_map) {
                Ok(translated) => reduces_singular.push(translated),
                Err(_) => return Err(ens_err.clone()),
            },
        }
    } else {
        return Err(ens_err.clone()); // "Singular ensures expression: equality assumed"
    }

    let ring_string;
    if tmp_count == 0 {
        ring_string = format!(
            "{} {}={},({}),{}",
            RING_DECL,
            RING_R,
            TO_INTEGER_RING,
            vars2.join(","),
            DP_ORDERING
        );
    } else {
        // create tmp variable for uninterpreted functions and mod operator.
        let mut tmp_vars: Vec<String> = vec![];
        for i in 0..(tmp_count + 1) {
            tmp_vars.push(format!("{}{}", TMP_PREFIX, i.to_string()));
        }
        ring_string = format!(
            "{} {}={},({},{}),{}",
            RING_DECL,
            RING_R,
            TO_INTEGER_RING,
            vars2.join(","),
            tmp_vars.join(","),
            DP_ORDERING
        );
    }
    let ideal_string = format!("{} {} = {}", IDEAL_DECL, IDEAL_I, ideals_singular.join(","));
    let ideal_to_groebner = format!("{} {} = {}({})", IDEAL_DECL, IDEAL_G, GROEBNER_APPLY, IDEAL_I);
    let reduce_string = format!("{}({}, {})", REDUCE_APPLY, reduces_singular[0], IDEAL_G);
    let quit_string = String::from(QUIT_SINGULAR);

    let res = format!(
        "{}; {}; {}; {}; {};",
        ring_string, ideal_string, ideal_to_groebner, reduce_string, quit_string
    );
    Ok(res)
}

pub fn check_singular_valid(
    context: &mut air::context::Context,
    command: &Command,
    _query_context: QueryContext<'_, '_>,
) -> ValidityResult {
    let query: Query = if let CommandX::CheckValid(query) = &**command {
        query.clone()
    } else {
        panic!("internal error: integer_ring")
    };

    let decl = query.local.clone();
    let statement = query.assertion.clone();
    let stmts: air::ast::Stmts = if let air::ast::StmtX::Block(stmts) = &*statement {
        stmts.clone()
    } else {
        panic!("internal error: integer_ring")
    };

    let arc_ens: &air::ast::Stmt = stmts.last().unwrap();
    let ens = match &**arc_ens {
        air::ast::StmtX::Assert(error, exp) => (exp.clone(), error.clone()),
        _ => {
            panic!("internal error");
        }
    };

    let mut vars: Vec<Ident> = vec![];
    for d in &**decl {
        if let air::ast::DeclX::Var(name, _typ) = &**d {
            vars.push(name.clone());
        }
    }

    let mut reqs = vec![];
    for idx in 0..(stmts.len() - 1) {
        let stm = &stmts[idx];
        match &**stm {
            air::ast::StmtX::Assert(error, exp) => {
                reqs.push((exp.clone(), error.clone()));
            }
            _ => {
                panic!("internal error");
            }
        };
    }

    let query = match singular_printer(&vars, &reqs, &ens) {
        Ok(query_string) => query_string,
        Err(err) => return ValidityResult::Invalid(None, err),
    };

    air::singular_manager::log_singular(context, &query);

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
                    "postcondition not satisfied: Ensures polynomial failed to be reduced to zero, reduced polynomial is {}\n generated singular query: {} ",
                    res[0].as_str(),
                    query
                ),
                &ens.1.spans[0],
            ),
        )
    }
}
