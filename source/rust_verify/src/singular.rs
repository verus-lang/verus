use air::ast::{BinaryOp, Command, CommandX, Constant, Expr, ExprX, Ident, MultiOp, Query};
use air::context::{QueryContext, ValidityResult};
use air::printer::Printer;
use air::singular_manager::SingularManager;
use sise::Node;
use std::collections::HashMap;
use std::sync::Arc;
use vir::messages::{error, Message};

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
const USER_VAR_PREFIX: &str = "user_var_";

const RESERVED_KEYWORDS: [&str; 10] = [
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

fn sanitize_var_name(name: String) -> String {
    // From singular docs
    // (See Sec. 3.5.3 of https://www.singular.uni-kl.de/index.php/singular.pdf)
    // Var names should start with a letter
    // May only include letters, digits, @, and _

    // Sanitization scheme:
    //  - Begin with USER_VAR_PREFIX to avoid any reserved identifiers
    //  - Any character can be sanitized as `_{unicode_value}_`
    //  - Encode _ as __
    //  - All other characters can stay the same

    let mut res = USER_VAR_PREFIX.to_string();
    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '@' {
            res.push(c);
        } else if c == '_' {
            res.push_str("__");
        } else {
            res.push('_');
            res.push_str(&format!("{:x}", c as u32));
            res.push('_');
        }
    }
    res
}

fn assert_not_reserved(name: &str) -> Result<(), String> {
    for keyword in RESERVED_KEYWORDS {
        if name == keyword {
            return Err(format!(
                "Integer_ring/Singular: Usage of reserved keyword at variable name: {}",
                name
            ));
        }
    }
    if name.starts_with(TMP_PREFIX) {
        return Err(format!(
            "Integer_ring/Singular: Usage of reserved prefix `{}` at {}",
            TMP_PREFIX, name
        ));
    }
    Ok(())
}

pub(crate) fn expr_to_singular(
    expr: &Expr,
    tmp_idx: &mut u32,
    node_map: &mut HashMap<Node, Ident>,
) -> Result<String, String> {
    let message_interface = Arc::new(vir::messages::VirMessageInterface {});
    let result_string = match &**expr {
        ExprX::Const(Constant::Nat(n)) => n.to_string(),
        ExprX::Var(x) => {
            let sanitized = sanitize_var_name(x.to_string());
            assert_not_reserved(&sanitized)?;
            sanitized
        }
        ExprX::Binary(BinaryOp::EuclideanMod, lhs, rhs) => {
            // x % y ->  x - y*tmp
            let pp = Printer::new(message_interface.clone(), false);
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
                _ => return Err(format!("unsupported integer_ring operator: {:?}", op.clone())),
            };
            for e in &**exprs {
                ss.push(format!("({})", expr_to_singular(&e, tmp_idx, node_map)?));
            }
            format!("({})", ss.join(sop))
        }
        ExprX::Apply(fname, exprs) => {
            if vir::def::ADD == (**fname).as_str() {
                return expr_to_singular(
                    &Arc::new(ExprX::Multi(MultiOp::Add, exprs.clone())),
                    tmp_idx,
                    node_map,
                );
            } else if vir::def::SUB == (**fname).as_str() {
                return expr_to_singular(
                    &Arc::new(ExprX::Multi(MultiOp::Sub, exprs.clone())),
                    tmp_idx,
                    node_map,
                );
            } else if vir::def::MUL == (**fname).as_str() {
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
            } else if vir::def::EUC_DIV == (**fname).as_str() {
                return Err(format!(
                    "unsupported operator: division. Consider registering the division result as a new variable before calling integer_ring lemma"
                ));
            } else {
                // treat as uninterpreted functions
                let pp = Printer::new(message_interface.clone(), false);
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
        _ => return Err(format!("Unsupported Expression: {:?}", expr)),
    };
    Ok(result_string)
}

pub fn singular_printer(
    vars: &Vec<Ident>,
    req_exprs: &Vec<(Expr, Message)>,
    ens_expr: &(Expr, Message),
) -> Result<String, Message> {
    let mut tmp_count: u32 = 0; // count the number of required tmp vars
    let mut vars2: Vec<String> = vec![];
    let mut node_map: HashMap<Node, Ident> = HashMap::new(); // for uninterpreted functions and mod translation

    // Using @ is safe. For example, `poly g1 = x2+y3` is translated as poly `g1 = x^2 + y^3`
    for v in vars {
        let mut v2 = v.to_string();
        v2.push('@');
        vars2.push(sanitize_var_name(v2));
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
                return Err(err.clone().secondary_label(
                    &err.spans[0].clone(),
                    "Inequality operator is not supported",
                ));
            }
            match expr_to_singular(&req, &mut tmp_count, &mut node_map) {
                Ok(translated) => ideals_singular.push(translated),
                Err(error_info) => {
                    return Err(err.clone().secondary_label(&err.spans[0].clone(), error_info));
                }
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
                    Err(error_info) => {
                        return Err(ens_err
                            .clone()
                            .secondary_label(&ens_err.spans[0].clone(), error_info));
                    }
                };

                // reduce 'X' with generated ideal
                match expr_to_singular(&exprs[0], &mut tmp_count, &mut node_map) {
                    Ok(translated) => reduces_singular.push(translated),
                    Err(error_info) => {
                        return Err(ens_err
                            .clone()
                            .secondary_label(&ens_err.spans[0].clone(), error_info));
                    }
                };

                if let ExprX::Const(Constant::Nat(ss)) = &**zero {
                    if **ss != "0".to_string() {
                        return Err(ens_err.clone().secondary_label(
                            &ens_err.spans[0].clone(),
                            "Singular expression: equality with zero assumed",
                        ));
                    }
                } else {
                    return Err(ens_err.clone().secondary_label(
                        &ens_err.spans[0].clone(),
                        "Singular expression: equality with zero assumed",
                    ));
                }
            }
            _ => match expr_to_singular(&ens, &mut tmp_count, &mut node_map) {
                Ok(translated) => reduces_singular.push(translated),
                Err(error_info) => {
                    return Err(ens_err
                        .clone()
                        .secondary_label(&ens_err.spans[0].clone(), error_info));
                }
            },
        }
    } else {
        return Err(ens_err.clone().secondary_label(
            &ens_err.spans[0].clone(),
            "Singular ensures expression: equality assumed",
        ));
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

    let res =
        format!("{}; {}; {}; {};", ring_string, ideal_string, ideal_to_groebner, reduce_string);
    Ok(res)
}

pub fn check_singular_valid(
    context: &mut air::context::Context,
    command: &Command,
    func_span: &vir::messages::Span,
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
        // last element is ensures clause
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

    let reqs = {
        reqs.into_iter()
            .map(|r| {
                let (expr, error) = r;
                let error: vir::messages::Message = error
                    .clone()
                    .downcast()
                    .expect("unexpected value in Any -> Message conversion");
                (expr, error)
            })
            .collect()
    };

    let ens = {
        let (expr, error) = ens;
        let error: vir::messages::Message =
            error.clone().downcast().expect("unexpected value in Any -> Message conversion");
        (expr, error)
    };

    let query = match singular_printer(&vars, &reqs, &ens) {
        Ok(query_string) => query_string,
        Err(err) => return ValidityResult::Invalid(None, err),
    };

    air::singular_manager::log_singular(context, &query, &func_span.as_string);

    let quit_string = format!("{};", QUIT_SINGULAR);
    let query = format!("{} {}", query, quit_string);

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
            error(
                &ens.1.spans[0],
                format!(
                    "postcondition not satisfied: Ensures polynomial failed to be reduced to zero, reduced polynomial is {}\n generated singular query: {} ",
                    res[0].as_str(),
                    query
                ),
            ),
        )
    }
}
