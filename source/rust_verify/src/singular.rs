use air::ast::{BinaryOp, Command, CommandX, Constant, Expr, ExprX, Ident, MultiOp, Query};
use air::context::{QueryContext, ValidityResult};
use air::messages::Message;
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

fn is_zero(expr: &Expr) -> bool {
    if let ExprX::Const(Constant::Nat(ss)) = &**expr {
        return **ss == "0".to_string();
    }
    return false;
}

struct SingularEncoder {
    tmp_idx: u32,
    node_map: HashMap<Node, Ident>,
    pp: Printer,
    polys: Vec<String>,
}

impl SingularEncoder {
    fn new() -> Self {
        SingularEncoder {
            tmp_idx: 0,
            node_map: HashMap::new(),
            pp: Printer::new(false),
            polys: vec!["0".to_string()],
        }
    }

    fn allocate_temp_var(&mut self) -> String {
        let res = self.tmp_idx;
        self.tmp_idx += 1;
        format!("{}{}", TMP_PREFIX, res)
    }

    fn expr_to_singular(&mut self, expr: &Expr) -> Result<String, String> {
        match &**expr {
            ExprX::Const(Constant::Nat(n)) => return Ok(n.to_string()),
            ExprX::Var(x) => {
                let sanitized = sanitize_var_name(x.to_string());
                assert_not_reserved(&sanitized)?;
                return Ok(sanitized);
            }
            ExprX::Binary(BinaryOp::EuclideanMod, lhs, rhs) => {
                // x % y ->  x - y*tmp
                let key = self.pp.expr_to_node(expr);
                let value = self.node_map.get(&key);
                let t = match value {
                    Some(tmp_var) => tmp_var.to_string(),
                    None => {
                        let tmp_var = self.allocate_temp_var();
                        self.node_map.insert(key, Arc::new(tmp_var.clone()));
                        tmp_var
                    }
                };
                let lhs = self.expr_to_singular(&lhs)?;
                let rhs = self.expr_to_singular(&rhs)?;
                return Ok(format!("(({}) - (({})*({})))", lhs, rhs, t));
            }
            ExprX::Multi(op, exprs) => {
                let mut ss = vec![];
                let sop = match op {
                    MultiOp::Add => " + ",
                    MultiOp::Sub => " - ",
                    MultiOp::Mul => " * ", // still reachable with constant multiplication
                    _ => {
                        return Err(format!("unsupported integer_ring operator: {:?}", op.clone()))
                    }
                };
                for e in &**exprs {
                    ss.push(format!("({})", self.expr_to_singular(&e)?));
                }
                return Ok(format!("({})", ss.join(sop)));
            }
            ExprX::Apply(fname, exprs) => {
                if vir::def::ADD == (**fname).as_str() {
                    return self
                        .expr_to_singular(&Arc::new(ExprX::Multi(MultiOp::Add, exprs.clone())));
                } else if vir::def::SUB == (**fname).as_str() {
                    return self
                        .expr_to_singular(&Arc::new(ExprX::Multi(MultiOp::Sub, exprs.clone())));
                } else if vir::def::MUL == (**fname).as_str() {
                    return self
                        .expr_to_singular(&Arc::new(ExprX::Multi(MultiOp::Mul, exprs.clone())));
                } else if vir::def::EUC_MOD == (**fname).as_str() {
                    if exprs.len() != 2 {
                        panic!("internal error: singular mod translation");
                    }
                    return self.expr_to_singular(&Arc::new(ExprX::Binary(
                        BinaryOp::EuclideanMod,
                        exprs[0].clone(),
                        exprs[1].clone(),
                    )));
                } else if vir::def::EUC_DIV == (**fname).as_str() {
                    return Err(format!(
                        "unsupported operator: division. Consider registering the division result as a new variable before calling integer_ring lemma"
                    ));
                } else {
                    // treat as uninterpreted functions
                    let key = self.pp.expr_to_node(expr);
                    let value = self.node_map.get(&key);
                    match value {
                        Some(tmp_var) => {
                            return Ok(tmp_var.to_string());
                        }
                        None => {
                            let tmp_var = self.allocate_temp_var();
                            self.node_map.insert(key, Arc::new(tmp_var.clone()));
                            return Ok(tmp_var);
                        }
                    }
                }
            }
            _ => return Err(format!("integer_ring unsupported expression: {:?}", expr)),
        }
    }

    fn decompose_modulus(&mut self, expr: &Expr) -> Result<Option<(String, String)>, String> {
        if let ExprX::Binary(BinaryOp::EuclideanMod, a, m) = &**expr {
            let a = self.expr_to_singular(a)?;
            let m = self.expr_to_singular(m)?;
            return Ok(Some((a, m)));
        }

        if let ExprX::Apply(fname, exprs) = &**expr {
            if vir::def::EUC_MOD == (**fname).as_str() {
                if exprs.len() != 2 {
                    panic!("internal error: singular mod translation");
                }
                let a = &exprs[0];
                let m = &exprs[1];
                let a = self.expr_to_singular(a)?;
                let m = self.expr_to_singular(m)?;
                return Ok(Some((a, m)));
            }
        }

        return Ok(None);
    }

    fn encode_requires_poly(&mut self, expr: &Expr) -> Result<(), String> {
        if let ExprX::Binary(BinaryOp::Eq, lhs, rhs) = &**expr {
            let dlhs = self.decompose_modulus(lhs)?;
            let drhs = self.decompose_modulus(rhs)?;

            if let (Some((a1, m1)), Some((a2, m2))) = (dlhs, drhs) {
                if m1 == m2 {
                    let t = self.allocate_temp_var();
                    self.polys.push(format!("({}) - ({}) - {} * ({})", a1, a2, t, m1));
                    return Ok(());
                }
                return Err(format!("integer_ring requires not sharing divisor: {:?}", expr));
            }

            let lhs = self.expr_to_singular(lhs)?;
            let rhs = self.expr_to_singular(rhs)?;
            self.polys.push(format!("{} - {}", lhs, rhs));
            return Ok(());
        }
        return Err(format!("Integer_ring requires/ensures not in equational form: {:?}", expr));
    }

    fn encode_ensures_poly(&mut self, expr: &Expr) -> Result<String, String> {
        if let ExprX::Binary(BinaryOp::Eq, lhs, rhs) = &**expr {
            let dlhs = self.decompose_modulus(lhs)?;
            let drhs = self.decompose_modulus(rhs)?;

            if is_zero(lhs) && drhs.is_some() {
                let (a, m) = drhs.unwrap();
                self.polys.push(m);
                return Ok(format!("({})", a));
            }

            if is_zero(rhs) && dlhs.is_some() {
                let (a, m) = dlhs.unwrap();
                self.polys.push(m);
                return Ok(format!("({})", a));
            }
            
            if let (Some((a1, m1)), Some((a2, m2))) = (dlhs, drhs) {
                if m1 == m2 {
                    self.polys.push(m1);
                    return Ok(format!("({}) - ({})", a1, a2));
                }
                return Err(format!("integer_ring requires not sharing divisor: {:?}", expr));
            }

            let lhs = self.expr_to_singular(lhs)?;
            let rhs = self.expr_to_singular(rhs)?;
            return Ok(format!("({}) - ({})", lhs, rhs));
        }

        return Err(format!("Integer_ring requires/ensures not in equational form: {:?}", expr));
    }
}

pub fn singular_printer(
    vars: &Vec<Ident>,
    req_exprs: &Vec<(Expr, Message)>,
    ens_expr: &(Expr, Message),
) -> Result<String, Message> {
    let mut encoder = SingularEncoder::new();

    // // Using @ is safe. For example, `poly g1 = x2+y3` is translated as poly `g1 = x^2 + y^3`
    let mut vars2: Vec<String> = vec![];
    for v in vars {
        let mut v2 = v.to_string();
        v2.push('@');
        vars2.push(sanitize_var_name(v2));
    }

    for (req, err) in req_exprs {
        match encoder.encode_requires_poly(req) {
            Ok(_) => {}
            Err(error_info) => {
                return Err(err.clone().secondary_label(&err.spans[0].clone(), error_info));
            }
        }
    }

    let (ens, err) = ens_expr;

    match encoder.encode_ensures_poly(ens) {
        Ok(goal) => {
            let ring_string;
            // create tmp variable for uninterpreted functions and mod operator.
            let mut tmp_vars: Vec<String> = vec![];
            for i in 0..(encoder.tmp_idx + 1) {
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
            let ideal_string =
                format!("{} {} = {}", IDEAL_DECL, IDEAL_I, encoder.polys.join(",\n"));
            let ideal_to_groebner =
                format!("{} {} = {}({})", IDEAL_DECL, IDEAL_G, GROEBNER_APPLY, IDEAL_I);
            let reduce_string = format!("{}({}, {})", REDUCE_APPLY, goal, IDEAL_G);

            let res = format!(
                "{};\n{};\n{};\n{};",
                ring_string, ideal_string, ideal_to_groebner, reduce_string
            );
            Ok(res)
        }
        Err(error_info) => {
            return Err(err.clone().secondary_label(&err.spans[0].clone(), error_info));
        }
    }
}

pub fn check_singular_valid(
    context: &mut air::context::Context,
    command: &Command,
    func_span: &air::ast::Span,
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

    let query = match singular_printer(&vars, &reqs, &ens) {
        Ok(query_string) => query_string,
        Err(err) => return ValidityResult::Invalid(None, err),
    };

    air::singular_manager::log_singular(context, &query, func_span);

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
            air::messages::error(
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
