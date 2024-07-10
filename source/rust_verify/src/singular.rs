use air::ast::{
    BinaryOp, Command, CommandX, Constant, Expr, ExprX, Ident, MultiOp, SingularQueryX,
};
use air::context::{QueryContext, SmtSolver, ValidityResult};
use air::printer::Printer;
use air::singular_manager::SingularManager;
use sise::Node;
use std::collections::HashMap;
use std::sync::Arc;
use vir::messages::error;

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
                "usage of the keyword {} is not supported when using the integer_ring solver",
                keyword
            ));
        }
    }
    if name.starts_with(TMP_PREFIX) {
        return Err(format!(
            "usage of reserved prefix `{}` in {} is not supported when using the integer_ring solver",
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
    user_vars: Vec<String>,
    polys: Vec<String>,
    mod_poly: Option<String>,
}

impl SingularEncoder {
    fn new(solver: SmtSolver, user_vars: Vec<String>) -> Self {
        let message_interface = Arc::new(vir::messages::VirMessageInterface {});
        let pp = Printer::new(message_interface.clone(), false, solver);
        SingularEncoder {
            tmp_idx: 0,
            node_map: HashMap::new(),
            pp,
            user_vars,
            polys: vec!["0".to_string()],
            mod_poly: None,
        }
    }

    fn allocate_temp_var(&mut self) -> String {
        self.tmp_idx += 1;
        let res = self.tmp_idx;
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
                // x % y ->  x - y * tmp
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
                        return Err(format!("unsupported integer_ring operator: {:?}", op.clone()));
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
                return Err(format!("requires not sharing divisor in integer_ring"));
            }

            let lhs = self.expr_to_singular(lhs)?;
            let rhs = self.expr_to_singular(rhs)?;
            self.polys.push(format!("{} - {}", lhs, rhs));
            return Ok(());
        }
        return Err(format!("requires not in equational form in integer_ring"));
    }

    fn encode_ensures_poly_inner(&mut self, expr: &Expr) -> Result<String, String> {
        if let ExprX::Binary(BinaryOp::Eq, lhs, rhs) = &**expr {
            let dlhs = self.decompose_modulus(lhs)?;
            let drhs = self.decompose_modulus(rhs)?;

            if is_zero(lhs) && drhs.is_some() {
                let (a, m) = drhs.unwrap();
                self.mod_poly = Some(m);
                return Ok(format!("({})", a));
            }

            if is_zero(rhs) && dlhs.is_some() {
                let (a, m) = dlhs.unwrap();
                self.mod_poly = Some(m);
                return Ok(format!("({})", a));
            }

            if let (Some((a1, m1)), Some((a2, m2))) = (dlhs, drhs) {
                if m1 == m2 {
                    self.mod_poly = Some(m1);
                    return Ok(format!("({}) - ({})", a1, a2));
                }
                // potentially, we can support this case by not adding the mod_poly, unclear how helpful it would be
                return Err(format!("integer_ring ensures not sharing divisor: {:?}", expr));
            }

            let lhs = self.expr_to_singular(lhs)?;
            let rhs = self.expr_to_singular(rhs)?;
            return Ok(format!("({}) - ({})", lhs, rhs));
        }

        return Err(format!("integer_ring ensures not in equational form"));
    }

    fn encode_ensures_poly(&mut self, ens: &Expr) -> Result<String, String> {
        let goal = self.encode_ensures_poly_inner(ens)?;
        let ring_string;
        // create tmp variable for uninterpreted functions and mod operator.
        let mut tmp_vars: Vec<String> = vec![];
        for i in 0..(self.tmp_idx + 1) {
            tmp_vars.push(format!("{}{}", TMP_PREFIX, i.to_string()));
        }

        ring_string = format!(
            "{} {}={},({},{}),{}",
            RING_DECL,
            RING_R,
            TO_INTEGER_RING,
            self.user_vars.join(","),
            tmp_vars.join(","),
            DP_ORDERING
        );
        let mut ideal_string = format!("{} {} = {}", IDEAL_DECL, IDEAL_I, self.polys.join(",\n"));

        // clear the mod poly, since this does not necessarily apply to the next goal.
        if let Some(mp) = self.mod_poly.take() {
            ideal_string.push_str(&format!(",\n{}", mp));
        }

        let ideal_to_groebner =
            format!("{} {} = {}({})", IDEAL_DECL, IDEAL_G, GROEBNER_APPLY, IDEAL_I);
        let reduce_string = format!("{}({}, {})", REDUCE_APPLY, goal, IDEAL_G);

        let res = format!(
            "{};\n{};\n{};\n{};\n",
            ring_string, ideal_string, ideal_to_groebner, reduce_string
        );
        Ok(res)
    }
}

fn encode_singular_queries(
    solver: SmtSolver, // Needed by the AIR printer, even for Singular queries
    command: &Command,
    func_span: &vir::messages::Span,
    queries: &mut Vec<(String, vir::messages::Message)>,
) -> Result<(), ValidityResult> {
    let CommandX::CheckSingular(ref query) = &**command else {
        panic!("internal error: integer_ring")
    };

    let SingularQueryX { requires: reqs, ensures: enss, local: _local } = &**query;

    let mut vars: Vec<String> = vec![];
    for d in &**query.local {
        if let air::ast::DeclX::Var(name, _typ) = &**d {
            vars.push(sanitize_var_name(name.to_string()));
        }
    }

    let mut encoder = SingularEncoder::new(solver, vars);

    // encode requires
    for stmt in &**reqs {
        if let air::ast::StmtX::Assert(_, err, _, expr) = &**stmt {
            let err: vir::messages::Message =
                err.clone().downcast().expect("unexpected value in Any -> Message conversion");
            if let Err(info) = encoder.encode_requires_poly(expr) {
                return Err(ValidityResult::Invalid(
                    None,
                    Some(err.clone().secondary_label(func_span, info)),
                    None,
                ));
            }
        }
    }

    // each ensures is a separate query string
    for stmts in &**enss {
        if let air::ast::StmtX::Assert(_, err, _, expr) = &**stmts {
            let err: vir::messages::Message =
                err.clone().downcast().expect("unexpected value in Any -> Message conversion");
            let res = encoder.encode_ensures_poly(expr);
            if let Err(info) = res {
                return Err(ValidityResult::Invalid(
                    None,
                    Some(err.clone().secondary_label(func_span, info)),
                    None,
                ));
            }
            queries.push((res.unwrap(), err.clone()));
        }
    }
    return Ok(());
}

pub fn check_singular_valid(
    context: &mut air::context::Context,
    command: &Command,
    func_span: &vir::messages::Span,
    _query_context: QueryContext<'_, '_>,
) -> ValidityResult {
    let mut queries = vec![];
    if let Err(res) =
        encode_singular_queries(context.get_solver().clone(), command, func_span, &mut queries)
    {
        // in case of any encoding error, skip running Singular
        return res;
    }

    let singular_manager = SingularManager::new();
    let mut singular_process = singular_manager.launch();

    for (query, err) in queries {
        air::singular_manager::log_singular(context, &query, &func_span.as_string);
        let res = singular_process.send_commands(query.as_bytes().to_vec());
        if (res.len() == 1) && (res[0] == "0") {
            // this query is ok (poly reduced to 0)
            continue;
        } else if (res.len() == 2) && (res[1] == "0") {
            // multiple ensures are encoded as separate queries
            // where each query redefines the ideal
            // ignore the first line of the output, which is a comment on the redefinition
            assert!(res[0].contains("// ** redefining"));
            continue;
        } else if res[0].contains("?") {
            /*
                if the contains "?", it generally indicates an error in the query, for example:

                ? `sa` is not defined
                ? error occurred in or before test line 4: `      (c - (d * tmp_1)) - y;`
                ? expected ideal-expression. type 'help ideal;'
                ? `ideal_I` is undefined
                ...

                probably not a good idea to try to parse this output. each line actually starts with a few spaces followed by a `?`.
            */
            return ValidityResult::UnexpectedOutput(String::from(format!(
                "{}\ngenerated singular query: {}",
                res[0].as_str(),
                query
            )));
        } else {
            // the resultant poly fails to reduce to 0. the poly is not going to be very informative, so we just return the error message.
            let err = error(
                &err.spans[0],
                "postcondition not satisfied, Singular cannot prove one of the the ensures"
                    .to_string(),
            )
            .primary_label(&err.spans[0], "Singular cannot prove this");
            return ValidityResult::Invalid(None, Some(err), None);
        }
    }

    return ValidityResult::Valid(
        #[cfg(feature = "axiom-usage-info")]
        air::context::UsageInfo::None,
    );
}
