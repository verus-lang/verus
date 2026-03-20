use air::ast::{
    BinaryOp, Command, CommandX, Constant, Expr, ExprX, Ident, MultiOp, SingularQueryX, UnaryOp,
};
use air::context::{QueryContext, SmtSolver, ValidityResult};
use air::messages::Diagnostics;
use air::printer::Printer;
use air::singular_manager::SingularManager;
use indexmap::IndexSet;
use sise::Node;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;
use vir::messages::{ToAny, error};

// Singular reserved keyword
const RING_DECL: &str = "ring";
const IDEAL_DECL: &str = "ideal";
const DP_ORDERING: &str = "dp";
const GROEBNER_APPLY: &str = "groebner";
const REDUCE_APPLY: &str = "reduce";
const TO_INTEGER_RING: &str = "integer";

// Verus-side reserved variable names for encoding purposes
const RING_R: &str = "ring_R";
const IDEAL_I: &str = "ideal_I";
const IDEAL_G: &str = "ideal_G";
const TMP_PREFIX: &str = "singular_tmp_";
const USER_VAR_PREFIX: &str = "user_var_";

fn sanitize_var_name(name: &String) -> String {
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

fn is_zero(expr: &Expr) -> bool {
    if let ExprX::Const(Constant::Nat(ss)) = &**expr {
        return **ss == "0".to_string();
    }
    return false;
}

struct SingularEncoder {
    tmp_idx: u32,
    node_map: HashMap<Node, Ident>,
    singular_expr_map: HashMap<SingularExpr, Ident>,
    pp: Printer,
    user_vars: Vec<String>,
}

#[derive(PartialEq, Eq, Clone, Hash)]
enum Var {
    User(Ident),
    Tmp(Ident),
}

#[derive(PartialEq, Eq, Clone, Hash)]
enum SingularExpr {
    Binary(BinOp, Rc<SingularExpr>, Rc<SingularExpr>),
    Literal(Arc<String>),
    Var(Var),
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
enum BinOp {
    Add,
    Sub,
    Mul,
    EuclideanMod,
}

enum SingularReqClause {
    Ideal(SingularExpr),
    NotEqualToZero(SingularExpr),
}

struct SingularEnsClause {
    // Expression we want to test if it is equals 0
    eq0: SingularExpr,
    // If the user writes `ensures a % m == 0` or `a % m == b % m` then the m becomes
    // an extra ideal.
    modulus: Option<SingularExpr>,
}

impl SingularExpr {
    fn find_divisors(&self, set: &mut IndexSet<SingularExpr>) {
        match self {
            SingularExpr::Binary(bin_op, lhs, rhs) => {
                lhs.find_divisors(set);
                rhs.find_divisors(set);
                match bin_op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul => {}
                    BinOp::EuclideanMod => {
                        set.insert((&**rhs).clone());
                    }
                }
            }
            SingularExpr::Literal(_) | SingularExpr::Var(_) => {}
        }
    }

    fn to_diagnostic_string(&self) -> String {
        match self {
            SingularExpr::Binary(bin_op, lhs, rhs) => {
                let op = match bin_op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::EuclideanMod => "%",
                };
                let l = lhs.to_diagnostic_string();
                let r = rhs.to_diagnostic_string();
                format!("({:} {:} {:})", l, op, r)
            }
            SingularExpr::Literal(l) => (**l).clone(),
            SingularExpr::Var(Var::User(ident)) => {
                let id = ident.to_string();
                id[0..id.len() - vir::def::SUFFIX_PARAM.len()].to_string()
            }
            SingularExpr::Var(Var::Tmp(tmp)) => tmp.to_string(),
        }
    }

    fn to_singular_string(&self) -> String {
        match self {
            SingularExpr::Binary(bin_op, lhs, rhs) => {
                let op = match bin_op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::EuclideanMod => panic!("EuclideanMod should be translated out"),
                };
                let l = lhs.to_singular_string();
                let r = rhs.to_singular_string();
                format!("({:} {:} {:})", l, op, r)
            }
            SingularExpr::Literal(l) => (**l).clone(),
            SingularExpr::Var(Var::User(ident)) => sanitize_var_name(&ident),
            SingularExpr::Var(Var::Tmp(tmp)) => tmp.to_string(),
        }
    }

    fn decompose_modulus(&self) -> Option<(&SingularExpr, &SingularExpr)> {
        match self {
            SingularExpr::Binary(BinOp::EuclideanMod, a, b) => Some((&*a, &*b)),
            _ => None,
        }
    }

    fn sub(self, rhs: Self) -> Self {
        SingularExpr::Binary(BinOp::Sub, Rc::new(self), Rc::new(rhs))
    }

    fn mul(self, rhs: Self) -> Self {
        SingularExpr::Binary(BinOp::Mul, Rc::new(self), Rc::new(rhs))
    }

    fn modulo(self, rhs: Self) -> Self {
        SingularExpr::Binary(BinOp::EuclideanMod, Rc::new(self), Rc::new(rhs))
    }
}

impl SingularReqClause {
    fn to_singular_string(&self) -> String {
        match self {
            SingularReqClause::Ideal(r) => r.to_singular_string(),
            SingularReqClause::NotEqualToZero(_) => {
                panic!("to_singular_string called on NotEqualToZero");
            }
        }
    }
}

impl SingularEncoder {
    fn new(solver: SmtSolver, user_vars: Vec<String>) -> Self {
        let message_interface = Arc::new(vir::messages::VirMessageInterface {});
        let pp = Printer::new(message_interface.clone(), false, solver);
        SingularEncoder {
            tmp_idx: 0,
            node_map: HashMap::new(),
            singular_expr_map: HashMap::new(),
            pp,
            user_vars,
        }
    }

    fn allocate_temp_var(&mut self) -> Arc<String> {
        self.tmp_idx += 1;
        let res = self.tmp_idx;
        Arc::new(format!("{}{}", TMP_PREFIX, res))
    }

    fn expr_to_singular(&mut self, expr: &Expr) -> Result<SingularExpr, String> {
        match &**expr {
            ExprX::Const(Constant::Nat(n)) => Ok(SingularExpr::Literal(n.clone())),
            ExprX::Var(x) => Ok(SingularExpr::Var(Var::User(x.clone()))),
            ExprX::Binary(BinaryOp::EuclideanMod, lhs, rhs) => {
                // x % y ->  x - y * tmp
                let lhs = self.expr_to_singular(&lhs)?;
                let rhs = self.expr_to_singular(&rhs)?;
                Ok(lhs.modulo(rhs))
            }
            ExprX::Multi(op, exprs) => {
                let bin_op = match op {
                    MultiOp::Add => BinOp::Add,
                    MultiOp::Sub => BinOp::Sub,
                    MultiOp::Mul => BinOp::Mul, // still reachable with constant multiplication
                    _ => {
                        return Err(format!("unsupported integer_ring operator: {:?}", op.clone()));
                    }
                };
                assert!(exprs.len() >= 1);

                let mut res = self.expr_to_singular(&exprs[0])?;
                for e in exprs.iter().skip(1) {
                    res = SingularExpr::Binary(
                        bin_op,
                        Rc::new(res),
                        Rc::new(self.expr_to_singular(e)?),
                    );
                }
                Ok(res)
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
                            return Ok(SingularExpr::Var(Var::Tmp(tmp_var.clone())));
                        }
                        None => {
                            let tmp_var = self.allocate_temp_var();
                            self.node_map.insert(key, tmp_var.clone());
                            return Ok(SingularExpr::Var(Var::Tmp(tmp_var)));
                        }
                    }
                }
            }
            _ => return Err(format!("integer_ring unsupported expression: {:?}", expr)),
        }
    }

    fn encode_requires_poly(&mut self, expr: &Expr) -> Result<SingularReqClause, String> {
        if let ExprX::Binary(BinaryOp::Eq, lhs, rhs) = &**expr {
            let lhs = self.expr_to_singular(lhs)?;
            let rhs = self.expr_to_singular(rhs)?;

            let dlhs = lhs.decompose_modulus();
            let drhs = rhs.decompose_modulus();

            if let (Some((a1, m1)), Some((a2, m2))) = (dlhs, drhs) {
                if m1 == m2 {
                    return Ok(SingularReqClause::Ideal(
                        a1.clone().sub(a2.clone()).modulo(m1.clone()),
                    ));
                }
                return Err(format!("requires not sharing divisor in integer_ring"));
            }

            return Ok(SingularReqClause::Ideal(lhs.sub(rhs)));
        }
        if let ExprX::Unary(UnaryOp::Not, inner) = &**expr {
            if let ExprX::Binary(BinaryOp::Eq, lhs, rhs) = &**inner {
                if is_zero(lhs) {
                    let x = self.expr_to_singular(rhs)?;
                    return Ok(SingularReqClause::NotEqualToZero(x));
                } else if is_zero(rhs) {
                    let x = self.expr_to_singular(lhs)?;
                    return Ok(SingularReqClause::NotEqualToZero(x));
                }
            }
        }
        return Err(format!("requires not in equational form in integer_ring"));
    }

    fn encode_ensures_poly(&mut self, expr: &Expr) -> Result<SingularEnsClause, String> {
        if let ExprX::Binary(BinaryOp::Eq, lhs_e, rhs_e) = &**expr {
            let lhs = self.expr_to_singular(lhs_e)?;
            let rhs = self.expr_to_singular(rhs_e)?;

            let dlhs = lhs.decompose_modulus();
            let drhs = rhs.decompose_modulus();

            if is_zero(lhs_e) && drhs.is_some() {
                let (a, m) = drhs.unwrap();
                return Ok(SingularEnsClause { eq0: a.clone(), modulus: Some(m.clone()) });
            }

            if is_zero(rhs_e) && dlhs.is_some() {
                let (a, m) = dlhs.unwrap();
                return Ok(SingularEnsClause { eq0: a.clone(), modulus: Some(m.clone()) });
            }

            if let (Some((a1, m1)), Some((a2, m2))) = (dlhs, drhs) {
                if m1 == m2 {
                    return Ok(SingularEnsClause {
                        eq0: a1.clone().sub(a2.clone()),
                        modulus: Some(m1.clone()),
                    });
                }
                // potentially, we can support this case by not adding the mod_poly, unclear how helpful it would be
                return Err(format!("integer_ring ensures not sharing divisor: {:?}", expr));
            }

            return Ok(SingularEnsClause { eq0: lhs.sub(rhs), modulus: None });
        }

        return Err(format!("integer_ring ensures not in equational form"));
    }

    fn translate(&mut self, e: &SingularExpr) -> SingularExpr {
        match e {
            SingularExpr::Binary(bin_op, lhs, rhs) => {
                let l = self.translate(lhs);
                let r = self.translate(rhs);
                match bin_op {
                    BinOp::EuclideanMod => {
                        let t = match self.singular_expr_map.get(e) {
                            Some(tmp_var) => tmp_var.clone(),
                            None => {
                                let tmp_var = self.allocate_temp_var();
                                self.singular_expr_map.insert(e.clone(), tmp_var.clone());
                                tmp_var
                            }
                        };
                        let t = SingularExpr::Var(Var::Tmp(t));
                        l.sub(r.mul(t))
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul => {
                        SingularExpr::Binary(*bin_op, Rc::new(l), Rc::new(r))
                    }
                }
            }
            SingularExpr::Literal(_) | SingularExpr::Var(_) => e.clone(),
        }
    }

    fn translate_req(&mut self, c: &SingularReqClause) -> SingularReqClause {
        match c {
            SingularReqClause::Ideal(s) => SingularReqClause::Ideal(self.translate(s)),
            SingularReqClause::NotEqualToZero(_) => {
                panic!("translate_req called on NotEqualToZero");
            }
        }
    }

    fn translate_ens(&mut self, c: &SingularEnsClause) -> SingularEnsClause {
        let SingularEnsClause { eq0, modulus } = c;
        let eq0 = self.translate(eq0);
        let modulus = match modulus {
            Some(m) => Some(self.translate(m)),
            None => None,
        };
        SingularEnsClause { eq0, modulus }
    }

    fn ideals_from_requires(
        &self,
        reqs: &[(SingularReqClause, vir::messages::Span)],
    ) -> Vec<String> {
        let mut v = vec!["0".to_string()];
        v.append(&mut reqs.iter().map(|m| m.0.to_singular_string()).collect::<Vec<_>>());
        v
    }

    fn mk_singular_query(
        &self,
        ideals_from_requires: &Vec<String>,
        ens: &SingularEnsClause,
    ) -> String {
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

        let ideals = match &ens.modulus {
            None => ideals_from_requires.join(",\n"),
            Some(r) => {
                let mut i = ideals_from_requires.clone();
                i.push(r.to_singular_string());
                i.join(",\n")
            }
        };

        let ideal_string = format!("{} {} = {}", IDEAL_DECL, IDEAL_I, ideals);

        let ideal_to_groebner =
            format!("{} {} = {}({})", IDEAL_DECL, IDEAL_G, GROEBNER_APPLY, IDEAL_I);
        let reduce_string =
            format!("{}({}, {})", REDUCE_APPLY, ens.eq0.to_singular_string(), IDEAL_G);

        format!("{};\n{};\n{};\n{};\n", ring_string, ideal_string, ideal_to_groebner, reduce_string)
    }
}

fn diagnostics_for_ne0(
    req_clauses: &Vec<(SingularReqClause, vir::messages::Span)>,
    ens_clauses: &Vec<(SingularEnsClause, vir::messages::Message)>,
    diagnostics: &impl Diagnostics,
    func_span: &vir::messages::Span,
) {
    let mut provided: Vec<(SingularExpr, vir::messages::Span)> = vec![];
    let mut expected_set: IndexSet<SingularExpr> = IndexSet::new();
    for (r, span) in req_clauses.iter() {
        match r {
            SingularReqClause::Ideal(e) => {
                e.find_divisors(&mut expected_set);
            }
            SingularReqClause::NotEqualToZero(e) => {
                provided.push((e.clone(), span.clone()));
            }
        }
    }
    for (e, _) in ens_clauses.iter() {
        let SingularEnsClause { eq0, modulus } = e;
        eq0.find_divisors(&mut expected_set);
        if let Some(m) = modulus {
            m.find_divisors(&mut expected_set);
            expected_set.insert(m.clone());
        }
    }

    let mut provided_set = IndexSet::new();
    for (c, span) in provided.iter() {
        if !expected_set.contains(c) {
            diagnostics.report(&vir::messages::warning(span,
                "integer_ring: this precondition is superfluous and has no impact on the integer_ring decision procedure").to_any());
        }
        provided_set.insert(c);
    }

    for e in expected_set.iter() {
        if !provided_set.contains(e) {
            diagnostics.report(&vir::messages::warning(func_span,
                format!("integer_ring: this lemma should have `{:} != 0` as a precondition, since this expression is used as a divisor. (This will be a hard error in the future.)", e.to_diagnostic_string())).to_any());
        }
    }
}

fn encode_singular_queries(
    solver: SmtSolver, // Needed by the AIR printer, even for Singular queries
    command: &Command,
    func_span: &vir::messages::Span,
    queries: &mut Vec<(String, vir::messages::Message)>,
    diagnostics: &impl Diagnostics,
) -> Result<(), ValidityResult> {
    let CommandX::CheckSingular(query) = &**command else { panic!("internal error: integer_ring") };

    let SingularQueryX { requires: reqs, ensures: enss, local: _local } = &**query;

    let mut vars: Vec<String> = vec![];
    for d in &**query.local {
        if let air::ast::DeclX::Var(name, _typ) = &**d {
            vars.push(sanitize_var_name(&name));
        }
    }

    let mut encoder = SingularEncoder::new(solver, vars);

    // process the requires/ensures, turn the AIR expressions into SingularExprs

    let mut req_clauses: Vec<(SingularReqClause, vir::messages::Span)> = vec![];
    for stmt in &**reqs {
        if let air::ast::StmtX::Assert(_, err, _, expr) = &**stmt {
            let err: vir::messages::Message =
                err.clone().downcast().expect("unexpected value in Any -> Message conversion");
            match encoder.encode_requires_poly(expr) {
                Ok(clause) => {
                    req_clauses.push((clause, err.spans[0].clone()));
                }
                Err(info) => {
                    return Err(ValidityResult::Invalid(
                        None,
                        Some(err.clone().secondary_label(func_span, info)),
                        None,
                    ));
                }
            }
        }
    }

    let mut ens_clauses: Vec<(SingularEnsClause, vir::messages::Message)> = vec![];
    for stmts in &**enss {
        if let air::ast::StmtX::Assert(_, err, _, expr) = &**stmts {
            let err: vir::messages::Message =
                err.clone().downcast().expect("unexpected value in Any -> Message conversion");
            match encoder.encode_ensures_poly(expr) {
                Ok(clause) => {
                    ens_clauses.push((clause, err));
                }
                Err(info) => {
                    return Err(ValidityResult::Invalid(
                        None,
                        Some(err.clone().secondary_label(func_span, info)),
                        None,
                    ));
                }
            }
        }
    }

    // Check if the preconditions of the form `d != 0` are correct
    // (i.e., that they line up with divisors d used in the other expressions)

    diagnostics_for_ne0(&req_clauses, &ens_clauses, diagnostics, func_span);

    let mut req_clauses = req_clauses
        .into_iter()
        .filter(|(r, _)| !matches!(r, SingularReqClause::NotEqualToZero(_)))
        .collect::<Vec<_>>();

    // Translate a % d into a - d * tmp

    for r in req_clauses.iter_mut() {
        r.0 = encoder.translate_req(&r.0);
    }
    for e in ens_clauses.iter_mut() {
        e.0 = encoder.translate_ens(&e.0);
    }

    // Make the queries (one per ensures clause)

    let ideals = encoder.ideals_from_requires(&req_clauses);
    for (ens_clause, err) in ens_clauses.iter() {
        let query = encoder.mk_singular_query(&ideals, ens_clause);
        queries.push((query, err.clone()));
    }

    return Ok(());
}

pub fn check_singular_valid(
    context: &mut air::context::Context,
    command: &Command,
    func_span: &vir::messages::Span,
    _query_context: QueryContext<'_, '_>,
    diagnostics: &impl Diagnostics,
) -> ValidityResult {
    let mut queries = vec![];
    if let Err(res) = encode_singular_queries(
        context.get_solver().clone(),
        command,
        func_span,
        &mut queries,
        diagnostics,
    ) {
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

    return ValidityResult::Valid(air::context::UsageInfo::None);
}
