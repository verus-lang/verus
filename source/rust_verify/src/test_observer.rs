//! Built-in test observer activated by `-V observers=test`.
//! Records callback data and, at the end of verification, emits it as a JSON note
//! (`OBSERVER:{...}`) that `rust_verify_test/tests/observer.rs` deserializes.

use serde::Serialize;
use std::any::Any;
use vir::ast_util::LowerUniqueVar;

/// Counts the control-flow shapes in a query assertion: `Breakable` regions and `Break`
/// statements (present when loops are lowered without isolation) and `Switch` nodes (one per
/// `if` or `match`).
#[derive(Default)]
struct ShapeCounts {
    breakables: usize,
    breaks: usize,
    switches: usize,
}

fn count_shapes(stmt: &air::ast::Stmt, c: &mut ShapeCounts) {
    use air::ast::StmtX;
    match &**stmt {
        StmtX::Breakable(_, body) => {
            c.breakables += 1;
            count_shapes(body, c);
        }
        StmtX::Break(_) => c.breaks += 1,
        StmtX::DeadEnd(body) => count_shapes(body, c),
        StmtX::Block(stmts) => stmts.iter().for_each(|s| count_shapes(s, c)),
        StmtX::Switch(stmts) => {
            c.switches += 1;
            stmts.iter().for_each(|s| count_shapes(s, c));
        }
        _ => {}
    }
}

#[derive(Serialize)]
pub struct TestObserver {
    pub krate_function_names: Vec<String>,
    pub krate_datatype_names: Vec<String>,
    pub havocs: Vec<String>,
    pub assigns: Vec<String>,
    pub variable_defs: Vec<String>,
    pub for_loop_vars: Vec<(String, String)>,
    pub reveal_strings: Vec<String>,
    pub quantifier_binders: Vec<String>,
    pub assert_id_kinds: Vec<String>,
    #[serde(rename = "function_lowered")]
    pub function_lowered_count: usize,
    #[serde(rename = "query_lowered")]
    pub query_lowered_count: usize,
    pub query_snapshot_counts: Vec<usize>,
    pub version_correlations: Vec<(String, u32, String)>,
    #[serde(skip)]
    pub correlator: vir::vir_observer::VersionCorrelator,
    pub lambda_decls: Vec<String>,
    pub choose_decls: Vec<String>,
    #[serde(rename = "check_valid_invalid")]
    pub check_valid_invalid_count: usize,
    #[serde(rename = "check_valid_valid")]
    pub check_valid_valid_count: usize,
    pub check_valid_timeout: usize,
    pub check_valid_invalid_model_size: Vec<usize>,
    pub eval_expr_results: Vec<Option<bool>>,
    pub binder_decls: Vec<String>,
    /// Count of `StmtX::Breakable` in lowered queries (loop encodings without isolation).
    /// Per discharged (Valid) query: how many labeled assertion ids it reported.
    pub valid_assert_id_counts: Vec<usize>,
    /// Per discharged query: number of named axioms in the unsat core, or None when usage
    /// reporting is not enabled.
    pub valid_used_axiom_counts: Vec<Option<usize>>,
    /// Per choose decl: name, then the Debug renderings of its binders, predicate, and body.
    pub choose_payloads: Vec<String>,
    /// Per lambda decl: name, then the Debug renderings of its binders and body.
    pub lambda_payloads: Vec<String>,
    /// Per binder decl: name, then the Debug renderings of its type and kind.
    pub binder_decl_payloads: Vec<String>,
    /// Debug rendering of each axiom expression delivered to `on_axiom_decl`.
    pub axiom_payloads: Vec<String>,
    /// Per query: Debug rendering of the versioned-constant declarations.
    pub query_local_var_payloads: Vec<String>,
    /// Per quantifier binder: Debug rendering of the quantified body.
    pub quantifier_body_payloads: Vec<String>,
    /// The crate id delivered to `on_krate`.
    pub krate_current_crate: String,
    pub breakable_count: usize,
    /// Count of `StmtX::Break` in lowered queries.
    pub break_count: usize,
    /// Number of `Switch` nodes across lowered queries (one per `if`/`match`).
    pub switch_count: usize,
    pub pre_body_binders: Vec<String>,
    pub post_body_binders: Vec<String>,
    pub body_lowering_started: bool,
    /// Ordered trace of every callback in fire order — enables sequencing
    /// assertions (L1–L5) that per-callback aggregates cannot express.
    pub events: Vec<String>,
    /// Count of `on_axiom_decl` (high-frequency; counted, not traced).
    pub axiom_decls: usize,
}

impl TestObserver {
    pub fn new() -> Self {
        TestObserver {
            krate_function_names: vec![],
            krate_datatype_names: vec![],
            havocs: vec![],
            assigns: vec![],
            variable_defs: vec![],
            for_loop_vars: vec![],
            reveal_strings: vec![],
            quantifier_binders: vec![],
            assert_id_kinds: vec![],
            function_lowered_count: 0,
            query_lowered_count: 0,
            query_snapshot_counts: vec![],
            version_correlations: vec![],
            correlator: vir::vir_observer::VersionCorrelator::new(),
            lambda_decls: vec![],
            choose_decls: vec![],
            check_valid_invalid_count: 0,
            check_valid_valid_count: 0,
            check_valid_timeout: 0,
            check_valid_invalid_model_size: vec![],
            eval_expr_results: vec![],
            binder_decls: vec![],
            valid_assert_id_counts: vec![],
            valid_used_axiom_counts: vec![],
            choose_payloads: vec![],
            lambda_payloads: vec![],
            binder_decl_payloads: vec![],
            axiom_payloads: vec![],
            query_local_var_payloads: vec![],
            quantifier_body_payloads: vec![],
            krate_current_crate: String::new(),
            breakable_count: 0,
            break_count: 0,
            switch_count: 0,
            pre_body_binders: vec![],
            post_body_binders: vec![],
            body_lowering_started: false,
            events: vec![],
            axiom_decls: 0,
        }
    }

    pub fn summary_json(&self) -> String {
        format!("OBSERVER:{}", serde_json::to_string(self).expect("observer summary serializes"))
    }
}

fn fun_name(f: &vir::ast::Function) -> String {
    f.x.name.path.segments.last().map(|s| s.to_string()).unwrap_or_default()
}
fn dt_name(d: &vir::ast::Datatype) -> String {
    match &d.x.name {
        vir::ast::Dt::Path(p) => p.segments.last().map(|s| s.to_string()).unwrap_or_default(),
        vir::ast::Dt::Tuple(n) => format!("tuple{}", n),
    }
}

impl air::air_observer::AirObserver for TestObserver {
    fn on_query_lowered(
        &mut self,
        query: &air::ast::Query,
        snapshots: &air::ast::Snapshots,
        local_vars: &[air::ast::Decl],
    ) {
        self.query_local_var_payloads.push(format!("{:?}", local_vars));
        self.query_lowered_count += 1;
        self.query_snapshot_counts.push(snapshots.len());
        let mut shapes = ShapeCounts::default();
        count_shapes(&query.assertion, &mut shapes);
        self.breakable_count += shapes.breakables;
        self.break_count += shapes.breaks;
        self.switch_count += shapes.switches;
        self.events.push("query_lowered".to_string());
    }
    fn on_wp_version_created(
        &mut self,
        versioned: &air::ast::Ident,
        kind: air::air_observer::VersionOrigin,
    ) {
        self.events.push(format!("wp_version:{:?}", kind));
        if let Some(stm) = self.correlator.resolve(versioned, kind) {
            if let Some(line) = vir::vir_observer::line_from_span(&stm.span) {
                let kind_str = format!("{:?}", kind);
                self.version_correlations.push((versioned.to_string(), line, kind_str));
            }
        }
    }
    fn on_lambda_decl(
        &mut self,
        name: &air::ast::Ident,
        binders: &air::ast::Binders<air::ast::Typ>,
        body: &air::ast::Expr,
    ) {
        self.lambda_decls.push(name.to_string());
        self.lambda_payloads.push(format!("{} {:?} {:?}", name, binders, body));
        self.events.push(format!("lambda_decl:{}", name));
    }
    fn on_choose_decl(
        &mut self,
        name: &air::ast::Ident,
        binders: &air::ast::Binders<air::ast::Typ>,
        _triggers: &air::ast::Triggers,
        predicate: &air::ast::Expr,
        body: &air::ast::Expr,
    ) {
        self.choose_decls.push(name.to_string());
        self.choose_payloads.push(format!("{} {:?} {:?} {:?}", name, binders, predicate, body));
        self.events.push(format!("choose_decl:{}", name));
    }
    fn on_axiom_decl(&mut self, expr: &air::ast::Expr) {
        self.axiom_decls += 1;
        self.axiom_payloads.push(format!("{:?}", expr));
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

impl air::query_result_observer::QueryResultObserver for TestObserver {
    fn on_check_valid_result(&mut self, result: &mut air::query_result_observer::CheckValidResult) {
        match result {
            air::query_result_observer::CheckValidResult::Invalid {
                model_defs,
                eval_bool_expr,
                ..
            } => {
                self.events.push("check_valid:Invalid".to_string());
                self.check_valid_invalid_count += 1;
                self.check_valid_invalid_model_size.push(model_defs.len());
                // Pin the evaluator's three-way contract: a true boolean, a false boolean,
                // and a non-boolean (unevaluable) expression.
                let true_expr =
                    std::sync::Arc::new(air::ast::ExprX::Const(air::ast::Constant::Bool(true)));
                self.eval_expr_results.push(eval_bool_expr(&true_expr));
                let false_expr =
                    std::sync::Arc::new(air::ast::ExprX::Const(air::ast::Constant::Bool(false)));
                self.eval_expr_results.push(eval_bool_expr(&false_expr));
                let non_bool = std::sync::Arc::new(air::ast::ExprX::Const(
                    air::ast::Constant::Nat(std::sync::Arc::new("42".to_string())),
                ));
                self.eval_expr_results.push(eval_bool_expr(&non_bool));
            }
            air::query_result_observer::CheckValidResult::Valid { assert_ids, usage_info } => {
                self.events.push("check_valid:Valid".to_string());
                self.check_valid_valid_count += 1;
                // A discharged query names the obligations it checked (ids may be None for
                // assertions the lowering left unlabeled).
                self.valid_assert_id_counts.push(assert_ids.iter().filter(|a| a.is_some()).count());
                // Usage data is opt-in: the count of used axioms when reporting is on, else None.
                self.valid_used_axiom_counts.push(match usage_info {
                    air::context::UsageInfo::UsedAxioms(names) => Some(names.len()),
                    air::context::UsageInfo::None => None,
                });
            }
            air::query_result_observer::CheckValidResult::Timeout { .. } => {
                self.events.push("check_valid:Timeout".to_string());
                self.check_valid_timeout += 1;
            }
        }
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

impl vir::vir_observer::VirObserver for TestObserver {
    fn on_krate(
        &mut self,
        krate: &vir::ast::Krate,
        _name_ctxt: &vir::def::NameCtxt,
        current_crate: &vir::ast::CrateId,
    ) {
        self.krate_current_crate = format!("{:?}", current_crate);
        self.krate_function_names = krate.functions.iter().map(fun_name).collect();
        self.krate_datatype_names = krate.datatypes.iter().map(dt_name).collect();
        self.events.push("krate".to_string());
    }
    fn on_havoc(&mut self, stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        let base = vir::def::suffix_local_unique_id(var);
        self.havocs.push(base.to_string());
        self.events.push(format!("havoc:{}", base));
        self.correlator.record_havoc_or_assign(&base, stm);
    }
    fn on_assign(&mut self, stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        let base = vir::def::suffix_local_unique_id(var);
        self.assigns.push(base.to_string());
        self.events.push(format!("assign:{}", base));
        self.correlator.record_havoc_or_assign(&base, stm);
    }
    fn on_variable_def(&mut self, _stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        self.variable_defs.push(vir::def::suffix_local_unique_id(var).to_string());
        self.events.push(format!("variable_def:{}", vir::def::suffix_local_unique_id(var)));
    }
    fn on_for_loop(&mut self, _stm: &vir::sst::Stm) {
        self.for_loop_vars.push(("for_loop".to_string(), "detected".to_string()));
        self.events.push("for_loop".to_string());
    }
    fn on_reveal_string(&mut self, lit: &std::sync::Arc<String>) {
        self.reveal_strings.push((**lit).clone());
        self.events.push("reveal".to_string());
    }
    fn on_quantifier_binder(
        &mut self,
        binder: &vir::ast::VarBinder<vir::ast::Typ>,
        exp: &vir::sst::Exp,
    ) {
        self.quantifier_body_payloads.push(format!("{:?}", exp));
        let name = binder.name.lower().to_string();
        self.quantifier_binders.push(name.clone());
        self.events.push(format!("quant_binder:{}", name));
        if self.body_lowering_started {
            self.post_body_binders.push(name);
        } else {
            self.pre_body_binders.push(name);
        }
    }
    fn on_body_lowering_start(&mut self) {
        self.body_lowering_started = true;
        self.events.push("body_start".to_string());
    }
    fn make_assert_id(
        &mut self,
        kind: vir::vir_observer::AssertIdKind,
        _index: usize,
        parent: &Option<air::ast::AssertId>,
    ) -> Option<air::ast::AssertId> {
        self.assert_id_kinds.push(format!("{:?}", kind));
        self.events.push(format!("assert_id:{:?}", kind));
        parent.clone()
    }
    fn on_binder_decl(&mut self, decl: &vir::sst::LocalDecl) {
        let name = vir::def::suffix_local_unique_id(&decl.ident);
        self.binder_decls.push(name.to_string());
        self.binder_decl_payloads.push(format!("{} {:?} {:?}", name, decl.typ, decl.kind));
        self.events.push(format!("binder_decl:{}", name));
    }
    fn on_function_lowered(&mut self) {
        self.function_lowered_count += 1;
        self.body_lowering_started = false;
        self.events.push("function_lowered".to_string());
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

// ---------------------------------------------------------------------------
// Dedicated single-trait observers.
//
// Each implements exactly ONE observer trait. They serve double duty:
//   (1) focused functional coverage of that trait's callbacks (payloads +
//       within-trait order), on inputs designed to elicit them; and
//   (2) a compile-time + runtime proof of decoupling — a single-trait `impl`
//       compiles and binds without requiring the other traits, and the
//       unrelated registry slots stay `None`.
// ---------------------------------------------------------------------------
//
// Single-trait observers. Each implements exactly one of the three traits and records only
// that its callbacks fired. Their rows prove decoupling: a consumer can implement one trait
// without the other two. Payload content is asserted by the `TestObserver` rows on the same
// programs, so these ignore their arguments by design.

/// Implements only `AirObserver`.
#[derive(Serialize)]
pub struct AirOnlyObserver {
    pub events: Vec<String>,
    pub lambda_decls: Vec<String>,
    pub choose_decls: Vec<String>,
    pub query_lowered: usize,
    pub axiom_decls: usize,
}
impl AirOnlyObserver {
    pub fn new() -> Self {
        AirOnlyObserver {
            events: vec![],
            lambda_decls: vec![],
            choose_decls: vec![],
            query_lowered: 0,
            axiom_decls: 0,
        }
    }
    pub fn summary_json(&self) -> String {
        format!("AIROBS:{}", serde_json::to_string(self).expect("observer summary serializes"))
    }
}
impl air::air_observer::AirObserver for AirOnlyObserver {
    fn on_query_lowered(
        &mut self,
        _: &air::ast::Query,
        _: &air::ast::Snapshots,
        _: &[air::ast::Decl],
    ) {
        self.query_lowered += 1;
        self.events.push("query_lowered".to_string());
    }
    fn on_wp_version_created(
        &mut self,
        _: &air::ast::Ident,
        kind: air::air_observer::VersionOrigin,
    ) {
        self.events.push(format!("wp_version:{:?}", kind));
    }
    fn on_lambda_decl(
        &mut self,
        name: &air::ast::Ident,
        _: &air::ast::Binders<air::ast::Typ>,
        _: &air::ast::Expr,
    ) {
        self.lambda_decls.push(name.to_string());
        self.events.push(format!("lambda_decl:{}", name));
    }
    fn on_choose_decl(
        &mut self,
        name: &air::ast::Ident,
        _: &air::ast::Binders<air::ast::Typ>,
        _: &air::ast::Triggers,
        _: &air::ast::Expr,
        _: &air::ast::Expr,
    ) {
        self.choose_decls.push(name.to_string());
        self.events.push(format!("choose_decl:{}", name));
    }
    fn on_axiom_decl(&mut self, _expr: &air::ast::Expr) {
        self.axiom_decls += 1;
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// Implements only `QueryResultObserver`. Also exercises the live `eval_bool_expr`
/// closure on `Invalid`, the one payload here that is only testable from a callback.
#[derive(Serialize)]
pub struct QueryResultOnlyObserver {
    pub events: Vec<String>,
    pub invalid: usize,
    pub valid: usize,
    pub timeout: usize,
    pub eval_expr_results: Vec<Option<bool>>,
}
impl QueryResultOnlyObserver {
    pub fn new() -> Self {
        QueryResultOnlyObserver {
            events: vec![],
            invalid: 0,
            valid: 0,
            timeout: 0,
            eval_expr_results: vec![],
        }
    }
    pub fn summary_json(&self) -> String {
        format!("QROBS:{}", serde_json::to_string(self).expect("observer summary serializes"))
    }
}
impl air::query_result_observer::QueryResultObserver for QueryResultOnlyObserver {
    fn on_check_valid_result(&mut self, result: &mut air::query_result_observer::CheckValidResult) {
        match result {
            air::query_result_observer::CheckValidResult::Invalid { eval_bool_expr, .. } => {
                self.invalid += 1;
                self.events.push("check_valid:Invalid".to_string());
                let true_expr =
                    std::sync::Arc::new(air::ast::ExprX::Const(air::ast::Constant::Bool(true)));
                self.eval_expr_results.push(eval_bool_expr(&true_expr));
            }
            air::query_result_observer::CheckValidResult::Valid { .. } => {
                self.valid += 1;
                self.events.push("check_valid:Valid".to_string());
            }
            air::query_result_observer::CheckValidResult::Timeout { .. } => {
                self.timeout += 1;
                self.events.push("check_valid:Timeout".to_string());
            }
        }
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// Implements only `VirObserver`.
#[derive(Serialize)]
pub struct VirOnlyObserver {
    pub events: Vec<String>,
    pub function_names: Vec<String>,
    pub havocs: Vec<String>,
    pub assigns: Vec<String>,
    pub function_lowered: usize,
}
impl VirOnlyObserver {
    pub fn new() -> Self {
        VirOnlyObserver {
            events: vec![],
            function_names: vec![],
            havocs: vec![],
            assigns: vec![],
            function_lowered: 0,
        }
    }
    pub fn summary_json(&self) -> String {
        format!("VIROBS:{}", serde_json::to_string(self).expect("observer summary serializes"))
    }
}
impl vir::vir_observer::VirObserver for VirOnlyObserver {
    fn on_krate(&mut self, krate: &vir::ast::Krate, _: &vir::def::NameCtxt, _: &vir::ast::CrateId) {
        self.function_names = krate.functions.iter().map(fun_name).collect();
        self.events.push("krate".to_string());
    }
    fn on_havoc(&mut self, _stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        let base = vir::def::suffix_local_unique_id(var);
        self.havocs.push(base.to_string());
        self.events.push(format!("havoc:{}", base));
    }
    fn on_assign(&mut self, _stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        let base = vir::def::suffix_local_unique_id(var);
        self.assigns.push(base.to_string());
        self.events.push(format!("assign:{}", base));
    }
    fn on_function_lowered(&mut self) {
        self.function_lowered += 1;
        self.events.push("function_lowered".to_string());
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
