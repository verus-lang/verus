//! This module implements a heuristic proof search strategy by using potentially-relevant broadcast lemmas,
//! inspired by Isabelle/HOL's Sledgehammer tool. If a proof is found, the proof is then optionally minimized
//! and displayed to the user.
use crate::{config::ArgsX, verifier::Diagnostics};
use rustc_span::source_map::SourceMap;
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast_util;
use vir::messages::ToAny;
use vir::{
    ast::{
        CallTarget, Expr, ExprX, Fun, Function, FunctionX, Krate, KrateX, Mode, Path, SpannedTyped,
        Stmt, VirErr,
    },
    ast_visitor,
    context::GlobalCtx,
    def::Spanned,
    messages::{Span, note, warning},
};

use crate::{buckets::BucketId, verifier::Verifier};

/// Sledgehammer might fail in two ways: either we called another Verus function that returned a `VirErr`, which
/// we may not be able to recover from if that function consumed the `GlobalCtx` or Sledgehammer itself produced
/// an error, in which case we can signal that to verify_bucket_outer and return back the original GlobalCtx.
pub(crate) enum SledgehammerErr {
    VirErr(VirErr),
    InternalError { msg: String, global_ctx: GlobalCtx },
}

impl SledgehammerErr {
    fn internal_err(global_ctx: GlobalCtx, msg: String) -> Self {
        SledgehammerErr::InternalError { msg, global_ctx }
    }
}

impl From<VirErr> for SledgehammerErr {
    fn from(err: VirErr) -> Self {
        SledgehammerErr::VirErr(err)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct VerificationOutcome {
    pub(crate) any_invalid: bool,
    pub(crate) any_timeout: bool,
    pub(crate) used_axioms: Option<Vec<air::ast::Ident>>,
}

impl VerificationOutcome {
    fn new() -> Self {
        VerificationOutcome { any_invalid: false, any_timeout: false, used_axioms: None }
    }

    #[allow(dead_code)]
    fn success(&self) -> bool {
        !self.any_invalid && !self.any_timeout
    }

    pub(crate) fn merge_axioms(&mut self, new_axioms: &Option<Vec<air::ast::Ident>>) {
        match self.used_axioms.as_mut() {
            Option::None => {
                self.used_axioms = new_axioms.clone();
            }
            Some(axioms) => {
                if let Some(new_axioms) = new_axioms {
                    axioms.extend(new_axioms.clone());
                }
            }
        }
    }
}

pub(crate) struct Sledgehammer<'a, R: Diagnostics> {
    verifier: &'a mut Verifier,
    reporter: &'a R,
    krate: &'a Krate,
    source_map: Option<&'a SourceMap>,
    bucket_id: BucketId,
    target_func: Function,
    fun_to_function: HashMap<Fun, Function>,
    do_minimize: bool,
}

pub(crate) fn sledgehammer<'a, R: Diagnostics + 'a>(
    verifier: &'a mut Verifier,
    reporter: &'a R,
    krate: &'a Krate,
    source_map: Option<&'a SourceMap>,
    bucket_id: &BucketId,
    gctx: GlobalCtx,
) -> Result<(Option<Krate>, GlobalCtx), VirErr> {
    let Some(mut sh) = Sledgehammer::<'a, R>::new(verifier, reporter, krate, source_map, bucket_id)
    else {
        // TODO: report error here
        return Ok((None, gctx));
    };
    match sh.find_proof(gctx) {
        Ok((result, new_ctx)) => Ok((result.map(|result| result.1), new_ctx)),
        Err(SledgehammerErr::VirErr(err)) => Err(err),
        Err(SledgehammerErr::InternalError { msg, global_ctx }) => {
            reporter.report(
                &warning(&global_ctx.no_span, format!("Sledgehammer internal error: {}", msg))
                    .to_any(),
            );
            Ok((None, global_ctx))
        }
    }
}

/// A silent reporter to avoid printing messages when rerunning a proof.
struct NoOpReporter {}

impl air::messages::Diagnostics for NoOpReporter {
    fn report(&self, _msg: &air::messages::ArcDynMessage) {}

    fn report_now(&self, _msg: &air::messages::ArcDynMessage) {}

    fn report_as(&self, _msg: &air::messages::ArcDynMessage, _msg_as: air::messages::MessageLevel) {
    }

    fn report_as_now(
        &self,
        _msg: &air::messages::ArcDynMessage,
        _msg_as: air::messages::MessageLevel,
    ) {
    }
}

impl Diagnostics for NoOpReporter {
    fn use_progress_bars(&self) -> bool {
        false
    }

    fn add_progress_bar(&self, _ctx: vir::def::CommandContext) {}

    fn complete_progress_bar(&self, _ctx: vir::def::CommandContext) {}
}

struct MinimizeState {
    // How often did we unsuccessfully try a guess without a given lemma?
    removal_attempts: HashMap<Fun, usize>,
}

impl From<&Guess> for MinimizeState {
    fn from(guess: &Guess) -> Self {
        let mut removal_attempts = HashMap::new();
        for fun in guess.broadcasts.iter() {
            removal_attempts.insert(fun.clone(), 0);
        }
        MinimizeState { removal_attempts }
    }
}

impl MinimizeState {
    fn unsuccessful_without(&mut self, f: &Fun) {
        *self.removal_attempts.get_mut(f).unwrap() += 1;
    }

    fn print_stats(&self) {
        let mut counts = HashMap::<usize, usize>::new();
        for (_, count) in self.removal_attempts.iter() {
            *(counts.entry(*count).or_insert(0)) += 1;
        }
        let mut count_vec = counts.into_iter().collect::<Vec<_>>();
        count_vec.sort_by_key(|(c, _)| *c);
        for (count, num) in count_vec {
            println!("{count} attempts: {num} functions");
        }
    }
}

impl<'a, R: Diagnostics> Sledgehammer<'a, R> {
    fn new(
        verifier: &'a mut Verifier,
        reporter: &'a R,
        krate: &'a Krate,
        source_map: Option<&'a SourceMap>,
        bucket_id: &BucketId,
    ) -> Option<Self> {
        let target_fun = match bucket_id {
            BucketId::Fun(_owning_mod, fun) => fun,
            _ => {
                return None;
            }
        };

        let fun_to_function = krate
            .functions
            .iter()
            .map(|f| (f.x.name.clone(), f.clone()))
            .collect::<HashMap<_, _>>();

        let target_func =
            fun_to_function.get(target_fun).expect("Target function must be in crate");
        let Some(minimize) = target_func.x.attrs.sledgehammer.as_ref() else {
            return None;
        };
        Some(Sledgehammer {
            verifier,
            reporter,
            krate,
            source_map,
            bucket_id: bucket_id.clone(),
            target_func: target_func.clone(),
            do_minimize: *minimize,
            fun_to_function,
        })
    }

    fn find_proof(
        &mut self,
        mut gctx: GlobalCtx,
    ) -> Result<(Option<(Guess, Krate)>, GlobalCtx), SledgehammerErr> {
        // TODO: this will eventually need to be generalized to allow for multiple strategies
        let relevant = self.try_all_relevant_lemmas()?;
        let mut guesses = VecDeque::from([relevant]);
        while let Some(mut guess) = guesses.pop_front() {
            match self.try_guess(&guess, gctx)? {
                (GuessOutcome::Success { .. }, mut new_ctx) => {
                    if self.do_minimize {
                        self.reporter.report(
                            &note(
                                &self.span(),
                                format!(
                                    "Sledgehammer found proof with {} lemmas, minimizing..",
                                    guess.broadcasts.len()
                                ),
                            )
                            .to_any(),
                        );
                        let (min_guess, ctx) = self.minimize(guess, new_ctx)?;
                        guess = min_guess;
                        new_ctx = ctx;
                    }
                    self.reporter.report(
                        &note(
                            &self.span(),
                            format!(
                                "Sledgehammer found proof with {} lemmas: \n{}",
                                guess.broadcasts.len(),
                                guess.pretty_print(&self.target_func.x.owning_module)
                            ),
                        )
                        .to_any(),
                    );
                    // This could be done more efficiently by returning the modified krate from minimize instead
                    let span = new_ctx.no_span.clone();
                    let (new_krate, new_ctx) = self.krate_for_guess(&guess, &span, new_ctx)?;
                    return Ok((Some((guess, new_krate)), new_ctx));
                }
                (GuessOutcome::Next { try_next }, new_ctx) => {
                    guesses.extend(try_next);
                    gctx = new_ctx;
                }
            }
        }
        self.reporter.report(
            &warning(&self.target_func.span, "Sledgehammer failed to find a proof").to_any(),
        );
        Ok((None, gctx))
    }

    fn try_all_relevant_lemmas(&self) -> Result<Guess, VirErr> {
        let mut all_broadcast_functions = Self::find_broadcast_fns(self.krate);
        all_broadcast_functions.retain(|func| &func.x.name != &self.target_func.x.name);
        let mut relevant = HashSet::new();
        let mut used_symbols =
            self.reachable_spec_functions_from_fun(&self.target_func, true, true);
        let mut changed = true;
        while changed {
            changed = false;
            let old_used_len = used_symbols.len();
            let old_relevant_len = relevant.len();
            for bc in &all_broadcast_functions {
                if relevant.contains(&bc.x.name) {
                    continue;
                }
                let syms_in_bc_ens = self.reachable_spec_functions_from_fun(bc, true, false);
                if used_symbols.intersection(&syms_in_bc_ens).next().is_some() {
                    relevant.insert(bc.x.name.clone());
                    used_symbols.extend(self.reachable_spec_functions_from_fun(bc, true, false));
                }
            }
            if old_used_len != used_symbols.len() || old_relevant_len != relevant.len() {
                changed = true;
            }
        }
        let mut relevant_vec = relevant.into_iter().collect::<Vec<_>>();
        relevant_vec.sort_by_key(|f| ast_util::path_as_friendly_rust_name(&f.path));
        Ok(Guess { priority: 0, broadcasts: relevant_vec })
    }

    fn try_guess(
        &mut self,
        guess: &Guess,
        global_ctx: GlobalCtx,
    ) -> Result<(GuessOutcome, GlobalCtx), SledgehammerErr> {
        let span = self.target_func.x.body.as_ref().expect("body").span.clone();
        let (new_krate, global_ctx) = self.insert_broadcasts(
            &self.target_func.clone(),
            &guess.broadcasts,
            &span,
            global_ctx,
        )?;
        let (result, global_ctx) = self.try_verify(&new_krate, &NoOpReporter {}, global_ctx)?;
        if result.any_timeout || result.any_invalid {
            Ok((GuessOutcome::give_up(), global_ctx))
        } else {
            Ok((GuessOutcome::Success { verification_outcome: result }, global_ctx))
        }
    }

    /// Attempt to minimize a successful guess as follows:
    /// - Re-run proof with axiom-usage-info enabled. This sometimes fails
    ///   to produce a valid proof due to unreliable unsat core production by SMT
    ///   solvers.
    /// - If axiom-usage-info produces a valid proof, report that to the user.
    /// - If not, fall back to a binary-search-inspired heuristic where we try
    /// to iteratively remove different subsets of the lemmas used originally.
    /// To improve performance, we track how many times we unsuccessfully tried
    /// removing a particular lemma.
    fn minimize(
        &mut self,
        guess: Guess,
        global_ctx: GlobalCtx,
    ) -> Result<(Guess, GlobalCtx), SledgehammerErr> {
        let mut min_state = MinimizeState::from(&guess);
        self.minimize_outer(guess, 2, &mut min_state, global_ctx)
    }

    fn minimize_outer(
        &mut self,
        guess: Guess,
        k: usize,
        min_state: &mut MinimizeState,
        global_ctx: GlobalCtx,
    ) -> Result<(Guess, GlobalCtx), SledgehammerErr> {
        if self.verifier.args.trace {
            self.reporter.report(
                &note(
                    self.span(),
                    format!(
                        "minimizing proof with {:?} lemmas [k = {k:?}]",
                        guess.broadcasts.len()
                    ),
                )
                .to_any(),
            );
        }

        match self.try_minimize_with_axiom_usage_info(guess.clone(), global_ctx)? {
            (Some(min_guess), new_ctx) => Ok((min_guess, new_ctx)),
            (Option::None, new_ctx) => {
                self.reporter.report(
                    &warning(&self.span(), "Failed to minimize proof using axiom-usage-info, using slower minimization")
                        .to_any(),
                );
                self.minimize_split(guess, k, min_state, new_ctx)
            }
        }
    }

    fn minimize_split(
        &mut self,
        mut guess: Guess,
        mut k: usize,
        min_state: &mut MinimizeState,
        mut global_ctx: GlobalCtx,
    ) -> Result<(Guess, GlobalCtx), SledgehammerErr> {
        assert!(k > 1);
        min_state.print_stats();
        let num_broadcasts = guess.broadcasts.len();
        let chunk_size_for =
            |j: usize| std::cmp::max(1, ((num_broadcasts as f64) / (j as f64)).ceil() as usize);
        let chunk_size = chunk_size_for(k);

        let mut i = 0;
        guess.broadcasts.sort_by_key(|fun| min_state.removal_attempts[fun]);
        while i < guess.broadcasts.len() {
            // drop i..upto-1 elements
            let range_to_drop = i..std::cmp::min(i + chunk_size, guess.broadcasts.len());
            let mut guess_without_chunk = guess.clone();
            guess_without_chunk.broadcasts.splice(range_to_drop.clone(), []);
            let (outcome, new_ctx) = self.try_guess(&guess_without_chunk, global_ctx)?;
            global_ctx = new_ctx;
            if outcome.is_success() {
                for j in range_to_drop {
                    min_state.removal_attempts.remove(&guess.broadcasts[j]);
                }
                return self.minimize_outer(guess_without_chunk, k, min_state, global_ctx);
            }
            for j in range_to_drop {
                min_state.unsuccessful_without(&guess.broadcasts[j]);
            }
            i += chunk_size;
        }

        if chunk_size > 1 {
            // make sure we actually try smaller chunks in next round:
            while chunk_size_for(k) == chunk_size {
                k = k + 1;
            }
            self.minimize_split(guess, k, min_state, global_ctx)
        } else {
            Ok((guess, global_ctx))
        }
    }

    // axiom-usage-map sometimes leaves out required lemmas; this function returns `None` in this case
    fn try_minimize_with_axiom_usage_info(
        &mut self,
        mut guess: Guess,
        mut global_ctx: GlobalCtx,
    ) -> Result<(Option<Guess>, GlobalCtx), SledgehammerErr> {
        let old_args = self.verifier.args.clone();
        let new_args = ArgsX { axiom_usage_info: true, ..old_args.as_ref().clone() };
        self.verifier.args = Arc::new(new_args);
        let old_axiom_setting = global_ctx.axiom_usage_info;
        global_ctx.axiom_usage_info = true;
        let (outcome, mut new_ctx) = self.try_guess(&guess, global_ctx)?;
        match outcome {
            GuessOutcome::Success {
                verification_outcome: VerificationOutcome { used_axioms: Some(used_axioms), .. },
                ..
            } => {
                guess
                    .broadcasts
                    .retain(|bc| used_axioms.contains(&vir::sst_to_air::fun_to_air_ident(bc)));
            }
            _ => {
                self.reporter
                    .report(&note(&self.span(), "Proof failed when running with -Vaxiom-usage-info, falling back to slow proof minimization").to_any());
                return Ok((None, new_ctx));
            }
        }

        self.verifier.args = old_args;
        new_ctx.axiom_usage_info = old_axiom_setting;

        // check whether this actually worked; unsat cores are sometimes incomplete and result in invalid proofs
        let (outcome, new_ctx) = self.try_guess(&guess, new_ctx)?;
        match outcome {
            GuessOutcome::Success { .. } => Ok((Some(guess), new_ctx)),
            _ => {
                self.reporter.report(
                    &warning(&self.span(), "axiom-usage-map produced an invalid proof, falling back to slow proof minimization").to_any(),
                );
                Ok((None, new_ctx))
            }
        }
    }

    fn try_verify(
        &mut self,
        krate: &Krate,
        reporter: &impl Diagnostics,
        mut global_ctx: GlobalCtx,
    ) -> Result<(VerificationOutcome, GlobalCtx), VirErr> {
        let mut outcome = VerificationOutcome::new();
        global_ctx = self.verifier.try_verify(
            reporter,
            krate,
            self.source_map,
            &self.bucket_id,
            global_ctx,
            Some(&mut outcome),
        )?;
        Ok((outcome, global_ctx))
    }

    fn krate_for_guess(
        &self,
        guess: &Guess,
        span: &Span,
        global_ctx: GlobalCtx,
    ) -> Result<(Krate, GlobalCtx), SledgehammerErr> {
        self.insert_broadcasts(&self.target_func.clone(), &guess.broadcasts, span, global_ctx)
    }

    fn insert_broadcasts(
        &self,
        fun: &Function,
        broadcasts: &[Fun],
        span: &Span,
        global_ctx: GlobalCtx,
    ) -> Result<(Krate, GlobalCtx), SledgehammerErr> {
        let mut cloned_krate: KrateX = self.krate.as_ref().clone();
        let mut fun_with_broadcasts: Spanned<FunctionX> = (**fun).clone();
        let Some(body) = &mut fun_with_broadcasts.x.body else {
            return Err(SledgehammerErr::internal_err(
                global_ctx,
                "Function must have a body".to_string(),
            ));
        };
        let mut cloned_body: SpannedTyped<ExprX> = (**body).clone();

        let mut with_broadcast_reveals: Vec<Stmt> = broadcasts
            .iter()
            .map(|broadcast| {
                let fuel_expr = SpannedTyped::new(
                    span,
                    &cloned_body.typ.clone(),
                    ExprX::Fuel(broadcast.clone(), 1, true),
                );
                Spanned::new(span.clone(), vir::ast::StmtX::Expr(fuel_expr))
            })
            .collect();
        match &mut cloned_body.x {
            ExprX::Block(stmts, ret) => {
                with_broadcast_reveals.extend((**stmts).clone());
                let stmts_arc = Arc::new(with_broadcast_reveals);
                cloned_body.x = ExprX::Block(stmts_arc, ret.clone());
            }
            ExprX::NeverToAny(inner_body) => match &inner_body.x {
                ExprX::Block(stmts, ret) => {
                    with_broadcast_reveals.extend((**stmts).clone());
                    let new_block = ExprX::Block(Arc::new(with_broadcast_reveals), ret.clone());
                    let new_never_to_any = ExprX::NeverToAny(Arc::new(SpannedTyped {
                        span: cloned_body.span.clone(),
                        typ: cloned_body.typ.clone(),
                        x: new_block,
                    }));
                    cloned_body.x = new_never_to_any
                }
                unhandled => {
                    return Err(SledgehammerErr::internal_err(
                        global_ctx,
                        format!(
                            "Unhandled expression kind when inserting broadcasts: {unhandled:#?}"
                        ),
                    ));
                }
            },
            unhandled => {
                return Err(SledgehammerErr::internal_err(
                    global_ctx,
                    format!("Unhandled expression kind when inserting broadcasts: {unhandled:#?}"),
                ));
            }
        };

        *body = Arc::new(cloned_body);
        let fun_with_broadcasts = Arc::new(fun_with_broadcasts);
        let new_funcs = self
            .krate
            .functions
            .iter()
            .map(move |krate_fun| {
                if &fun.x.name == &krate_fun.x.name {
                    fun_with_broadcasts.clone()
                } else {
                    krate_fun.clone()
                }
            })
            .collect::<Vec<_>>();
        cloned_krate.functions = new_funcs;
        // Since we inserted broadcasts that may not have been there before, the
        // call graph of the program may have changed. To guard against
        // introducing cyclic references in `proof fn`s, we recompute the call
        // graph by creating a new `GlobalCtx`.
        //
        // In addition to the soundness risk, not recomputing the call graph may
        // also result in spurious proof failures if a broadcasted lemma
        // previously occurred in a later SCC that the `proof fn` the broadcast
        // was inserted into. In that case, the lemma would not be defined in
        // the SMT query when verifying the `proof fn`.
        //
        // If this recomputation turns out to be too costly, we can instead
        // provide a graph update API that allows more fine-grained changes to
        // the call graph.
        let cloned_krate = Arc::new(cloned_krate);
        let global_ctx = GlobalCtx::new(
            &cloned_krate,
            global_ctx.crate_name,
            global_ctx.no_span,
            global_ctx.rlimit,
            global_ctx.interpreter_log,
            global_ctx.func_call_graph_log,
            global_ctx.solver,
            true,
            false,
            global_ctx.axiom_usage_info,
            global_ctx.new_mut_ref,
            global_ctx.no_bv_simplify,
            global_ctx.report_long_running,
        )
        .expect("global_ctx");

        Ok((cloned_krate, global_ctx))
    }

    fn find_broadcast_fns(krate: &Krate) -> Vec<Function> {
        let mut broadcast_fns = Vec::new();
        for func in krate.functions.iter() {
            if func.x.attrs.broadcast_forall {
                broadcast_fns.push(func.clone());
            }
        }
        broadcast_fns
    }

    fn reachable_spec_functions_from_fun(
        &self,
        function: &Function,
        include_requires: bool,
        include_body_if_proof: bool,
    ) -> HashSet<Fun> {
        let mut result = HashSet::new();
        let mode = function.x.mode;
        if include_body_if_proof || mode == Mode::Spec || mode == Mode::Exec {
            function
                .x
                .body
                .as_ref()
                .into_iter()
                .for_each(|e| self.reachable_spec_functions_from_expr(e, &mut result));
        }
        if mode == Mode::Proof || mode == Mode::Exec {
            let (regular_ensures, trait_ensures) = &function.x.ensure;
            regular_ensures
                .iter()
                .for_each(|e| self.reachable_spec_functions_from_expr(e, &mut result));
            trait_ensures
                .iter()
                .for_each(|e| self.reachable_spec_functions_from_expr(e, &mut result));
            if include_requires {
                function
                    .x
                    .require
                    .iter()
                    .for_each(|e| self.reachable_spec_functions_from_expr(e, &mut result));
            }
        }
        result
    }

    fn reachable_spec_functions_from_expr(&self, expr: &Expr, funcs: &mut HashSet<Fun>) {
        let mut exprs = VecDeque::new();
        let mut seen = HashSet::new();
        exprs.push_back(expr);
        while let Some(e) = exprs.pop_front() {
            ast_visitor::expr_visitor_check(e, &mut |_, e: &Expr| match &e.x {
                ExprX::Call(CallTarget::Fun(_, fun, ..), ..) => {
                    match self.fun_to_function.get(fun) {
                        Some(function) if function.x.mode == Mode::Spec => {
                            funcs.insert(fun.clone());
                            if !seen.contains(fun) {
                                let body = function.x.body.as_ref();
                                body.into_iter().for_each(|e| exprs.push_back(e));
                                seen.insert(fun.clone());
                            }
                            Result::<_, ()>::Ok(())
                        }
                        _ => Ok(()),
                    }
                }
                _ => Ok(()),
            })
            .expect("can't error");
        }
    }

    fn span(&self) -> &Span {
        &self.target_func.span
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Guess {
    priority: usize, // higher means more important (not used yet)
    broadcasts: Vec<Fun>,
}

impl Guess {
    fn pretty_print(&self, module_opt: &Option<Path>) -> String {
        let mut s = String::new();
        for bc in &self.broadcasts {
            if let Some(module) = module_opt {
                s.push_str(&format!(
                    "broadcast use {};\n",
                    ast_util::friendly_fun_name_crate_relative(module, &bc)
                ));
            } else {
                s.push_str(&format!(
                    "broadcast use {};\n",
                    ast_util::fun_as_friendly_rust_name(&bc)
                ));
            }
        }
        s
    }
}

#[derive(Clone, Debug)]
pub(crate) enum GuessOutcome {
    Success { verification_outcome: VerificationOutcome },
    Next { try_next: Vec<Guess> },
}

impl GuessOutcome {
    fn give_up() -> Self {
        GuessOutcome::Next { try_next: Vec::new() }
    }

    fn is_success(&self) -> bool {
        match self {
            GuessOutcome::Success { .. } => true,
            _ => false,
        }
    }
}

impl Verifier {
    fn try_verify(
        &mut self,
        reporter: &impl Diagnostics,
        krate: &Krate,
        source_map: Option<&SourceMap>,
        bucket_id: &BucketId,
        global_ctx: GlobalCtx,
        outcome: Option<&mut VerificationOutcome>,
    ) -> Result<GlobalCtx, VirErr> {
        let prev_errors = self.count_errors;
        let prev_verified = self.count_verified;
        // TODO: the following is copied from verify_bucket_outer; it would be nicer
        // to avoid duplicating that logic here:
        // copied from Verifier::verify_bucket_outer
        let (pruned_krate, prune_info) = vir::prune::prune_krate_for_module_or_krate(
            &krate,
            &Arc::new(self.crate_name.clone().expect("crate_name")),
            None,
            Some(bucket_id.module().clone()),
            bucket_id.function(),
            true,
            true,
        );
        let vir::prune::PruneInfo {
            mono_abstract_datatypes,
            spec_fn_types,
            used_builtins,
            fndef_types,
            resolved_typs,
            dyn_traits,
        } = prune_info;
        let mono_abstract_datatypes = mono_abstract_datatypes.unwrap();
        let module = pruned_krate
            .modules
            .iter()
            .find(|m| &m.x.path == bucket_id.module())
            .expect("module in krate")
            .clone();
        let mut ctx = vir::context::Ctx::new(
            &pruned_krate,
            global_ctx,
            module,
            mono_abstract_datatypes,
            spec_fn_types,
            dyn_traits,
            used_builtins,
            fndef_types,
            resolved_typs.unwrap(),
            self.args.debugger,
        )?;
        if self.args.log_all || self.args.log_args.log_vir_poly {
            let mut file = self.create_log_file(
                Some(&bucket_id),
                &format!("sledgehammer{}", crate::config::VIR_POLY_FILE_SUFFIX),
            )?;
            vir::printer::write_krate(&mut file, &pruned_krate, &self.args.log_args.vir_log_option);
        }

        let krate_sst = vir::ast_to_sst_crate::ast_to_sst_krate(
            &mut ctx,
            reporter,
            &self.get_bucket(bucket_id).funs,
            &pruned_krate,
        )?;
        if self.args.log_all || self.args.log_args.log_vir_sst {
            let mut file = self.create_log_file(
                Some(&bucket_id),
                &format!("sledgehammer-{}", crate::config::VIR_SST_FILE_SUFFIX),
            )?;
            vir::printer::write_krate_sst(
                &mut file,
                &krate_sst,
                &self.args.log_args.vir_log_option,
            );
        }
        let krate_sst = vir::poly::poly_krate_for_module(&mut ctx, &krate_sst);

        let result =
            self.verify_bucket(reporter, &krate_sst, source_map, bucket_id, &mut ctx, outcome);
        self.count_errors = prev_errors;
        self.count_verified = prev_verified;
        result?;

        Ok(ctx.free())
    }
}
