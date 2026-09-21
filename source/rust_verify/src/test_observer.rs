//! Built-in test observer activated by `-V observers=test`.
//! Records callback data and emits JSON for test assertions.

use std::any::Any;
use vir::ast_util::LowerUniqueVar;

/// Counts `Breakable` / `Break` statements in a query assertion (present when loops are
/// lowered without isolation).
fn count_break_stmts(stmt: &air::ast::Stmt) -> (usize, usize) {
    use air::ast::StmtX;
    match &**stmt {
        StmtX::Breakable(_, body) => {
            let (b, k) = count_break_stmts(body);
            (b + 1, k)
        }
        StmtX::Break(_) => (0, 1),
        StmtX::DeadEnd(body) => count_break_stmts(body),
        StmtX::Block(stmts) | StmtX::Switch(stmts) => stmts.iter().fold((0, 0), |(b, k), s| {
            let (b2, k2) = count_break_stmts(s);
            (b + b2, k + k2)
        }),
        _ => (0, 0),
    }
}

pub struct TestObserver {
    pub krate_function_names: Vec<String>,
    pub krate_datatype_names: Vec<String>,
    pub havocs: Vec<String>,
    pub assigns: Vec<String>,
    pub branch_merges: usize,
    pub break_merges: usize,
    pub variable_defs: Vec<String>,
    pub for_loop_vars: Vec<(String, String)>,
    pub reveal_strings: Vec<String>,
    pub quantifier_binders: Vec<String>,
    pub assert_id_kinds: Vec<String>,
    pub function_lowered_count: usize,
    pub query_lowered_count: usize,
    pub query_snapshot_counts: Vec<usize>,
    pub version_correlations: Vec<(String, u32, String)>,
    pub correlator: vir::vir_observer::VersionCorrelator,
    pub lambda_decls: Vec<String>,
    pub choose_decls: Vec<String>,
    pub check_valid_invalid_count: usize,
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
    pub breakable_count: usize,
    /// Count of `StmtX::Break` in lowered queries.
    pub break_count: usize,
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
            branch_merges: 0,
            break_merges: 0,
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
            breakable_count: 0,
            break_count: 0,
            pre_body_binders: vec![],
            post_body_binders: vec![],
            body_lowering_started: false,
            events: vec![],
            axiom_decls: 0,
        }
    }

    fn json_strings(v: &[String]) -> String {
        let items: Vec<String> = v.iter().map(|s| format!("\"{}\"", s)).collect();
        format!("[{}]", items.join(","))
    }
    fn json_usizes(v: &[usize]) -> String {
        let items: Vec<String> = v.iter().map(|n| n.to_string()).collect();
        format!("[{}]", items.join(","))
    }
    fn json_opt_bools(v: &[Option<bool>]) -> String {
        let items: Vec<String> = v
            .iter()
            .map(|b| match b {
                Some(true) => "true".to_string(),
                Some(false) => "false".to_string(),
                None => "null".to_string(),
            })
            .collect();
        format!("[{}]", items.join(","))
    }
    fn json_opt_usizes(v: &[Option<usize>]) -> String {
        let items: Vec<String> = v
            .iter()
            .map(|n| match n {
                Some(n) => n.to_string(),
                None => "null".to_string(),
            })
            .collect();
        format!("[{}]", items.join(","))
    }
    fn json_version_correlations(v: &[(String, u32, String)]) -> String {
        let items: Vec<String> = v
            .iter()
            .map(|(name, line, kind)| format!("[\"{}\",{},\"{}\"]", name, line, kind))
            .collect();
        format!("[{}]", items.join(","))
    }
    fn json_string_pairs(v: &[(String, String)]) -> String {
        let items: Vec<String> = v.iter().map(|(a, b)| format!("[\"{}\",\"{}\"]", a, b)).collect();
        format!("[{}]", items.join(","))
    }

    pub fn summary_json(&self) -> String {
        format!(
            concat!(
                "OBSERVER:{{",
                "\"krate_function_names\":{},\"krate_datatype_names\":{},",
                "\"havocs\":{},\"assigns\":{},",
                "\"branch_merges\":{},\"break_merges\":{},",
                "\"variable_defs\":{},\"for_loop_vars\":{},",
                "\"reveal_strings\":{},",
                "\"quantifier_binders\":{},",
                "\"assert_id_kinds\":{},",
                "\"function_lowered\":{},\"query_lowered\":{},",
                "\"query_snapshot_counts\":{},",
                "\"version_correlations\":{},",
                "\"lambda_decls\":{},\"choose_decls\":{},",
                "\"check_valid_invalid\":{},\"check_valid_valid\":{},",
                "\"check_valid_timeout\":{},",
                "\"check_valid_invalid_model_size\":{},",
                "\"eval_expr_results\":{},",
                "\"binder_decls\":{},",
                "\"pre_body_binders\":{},",
                "\"post_body_binders\":{},",
                "\"events\":{},",
                "\"axiom_decls\":{},",
                "\"breakable_count\":{},\"break_count\":{},",
                "\"valid_assert_id_counts\":{},",
                "\"valid_used_axiom_counts\":{}",
                "}}"
            ),
            Self::json_strings(&self.krate_function_names),
            Self::json_strings(&self.krate_datatype_names),
            Self::json_strings(&self.havocs),
            Self::json_strings(&self.assigns),
            self.branch_merges,
            self.break_merges,
            Self::json_strings(&self.variable_defs),
            Self::json_string_pairs(&self.for_loop_vars),
            Self::json_strings(&self.reveal_strings),
            Self::json_strings(&self.quantifier_binders),
            Self::json_strings(&self.assert_id_kinds),
            self.function_lowered_count,
            self.query_lowered_count,
            Self::json_usizes(&self.query_snapshot_counts),
            Self::json_version_correlations(&self.version_correlations),
            Self::json_strings(&self.lambda_decls),
            Self::json_strings(&self.choose_decls),
            self.check_valid_invalid_count,
            self.check_valid_valid_count,
            self.check_valid_timeout,
            Self::json_usizes(&self.check_valid_invalid_model_size),
            Self::json_opt_bools(&self.eval_expr_results),
            Self::json_strings(&self.binder_decls),
            Self::json_strings(&self.pre_body_binders),
            Self::json_strings(&self.post_body_binders),
            Self::json_strings(&self.events),
            self.axiom_decls,
            self.breakable_count,
            self.break_count,
            Self::json_usizes(&self.valid_assert_id_counts),
            Self::json_opt_usizes(&self.valid_used_axiom_counts),
        )
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
        _: &[air::ast::Decl],
    ) {
        self.query_lowered_count += 1;
        self.query_snapshot_counts.push(snapshots.len());
        let (breakables, breaks) = count_break_stmts(&query.assertion);
        self.breakable_count += breakables;
        self.break_count += breaks;
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
        _: &[air::ast::Ident],
        _: &air::ast::Expr,
    ) {
        self.lambda_decls.push(name.to_string());
        self.events.push(format!("lambda_decl:{}", name));
    }
    fn on_choose_decl(&mut self, name: &air::ast::Ident, _: &air::ast::Ident) {
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
        _current_crate: &vir::ast::CrateId,
    ) {
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
    fn on_branch_merge(&mut self, stm: &vir::sst::Stm) {
        self.branch_merges += 1;
        self.events.push("branch_merge".to_string());
        self.correlator.record_branch_merge(stm);
    }
    fn on_break_merge(&mut self, stm: &vir::sst::Stm) {
        self.break_merges += 1;
        self.events.push("break_merge".to_string());
        self.correlator.record_break_merge(stm);
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
        _exp: &vir::sst::Exp,
    ) {
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
        kind: &vir::vir_observer::AssertIdKind,
        _index: usize,
        parent: &Option<air::ast::AssertId>,
    ) -> Option<air::ast::AssertId> {
        self.assert_id_kinds.push(format!("{:?}", kind));
        self.events.push(format!("assert_id:{:?}", kind));
        parent.clone()
    }
    fn on_quantifier_binder_decl(&mut self, var: &vir::ast::VarIdent) {
        self.binder_decls.push(vir::def::suffix_local_unique_id(var).to_string());
        self.events.push(format!("binder_decl:{}", vir::def::suffix_local_unique_id(var)));
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

/// Implements only `AirObserver`.
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
        format!(
            "AIROBS:{{\"events\":{},\"lambda_decls\":{},\"choose_decls\":{},\"query_lowered\":{},\"axiom_decls\":{}}}",
            TestObserver::json_strings(&self.events),
            TestObserver::json_strings(&self.lambda_decls),
            TestObserver::json_strings(&self.choose_decls),
            self.query_lowered,
            self.axiom_decls,
        )
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
        _: &[air::ast::Ident],
        _: &air::ast::Expr,
    ) {
        self.lambda_decls.push(name.to_string());
        self.events.push(format!("lambda_decl:{}", name));
    }
    fn on_choose_decl(&mut self, name: &air::ast::Ident, _: &air::ast::Ident) {
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

/// Implements only `QueryResultObserver` — receives `Invalid`/`Valid`/`Timeout`
/// and exercises the live `eval_bool_expr` closure on `Invalid`. Proves a
/// results-only consumer couples nothing else.
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
        format!(
            "QROBS:{{\"events\":{},\"invalid\":{},\"valid\":{},\"timeout\":{},\"eval_expr_results\":{}}}",
            TestObserver::json_strings(&self.events),
            self.invalid,
            self.valid,
            self.timeout,
            TestObserver::json_opt_bools(&self.eval_expr_results),
        )
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
        format!(
            "VIROBS:{{\"events\":{},\"function_names\":{},\"havocs\":{},\"assigns\":{},\"function_lowered\":{}}}",
            TestObserver::json_strings(&self.events),
            TestObserver::json_strings(&self.function_names),
            TestObserver::json_strings(&self.havocs),
            TestObserver::json_strings(&self.assigns),
            self.function_lowered,
        )
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
