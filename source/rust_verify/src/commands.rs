use crate::buckets::Bucket;
use air::ast::Command;
use air::messages::Diagnostics;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::Visibility;
use vir::ast::{Fun, Function, Krate, Mode, VirErr};
use vir::ast_util::fun_as_friendly_rust_name;
use vir::ast_util::is_visible_to;
use vir::context::FunctionCtx;
use vir::def::{CommandsWithContext, CommandsWithContextX};
use vir::func_to_air::SstMap;
use vir::messages::Message;
use vir::recursion::Node;
use vir::update_cell::UpdateCell;

#[derive(Clone, Copy, Debug)]
pub enum ContextOp {
    SpecDefinition,
    ReqEns,
    Broadcast,
}

#[derive(Clone, Copy, Debug)]
pub enum Style {
    Normal,
    RecommendsFollowupFromError,
    RecommendsChecked,
    Expanded,
}

#[derive(Clone, Copy, Debug)]
pub enum QueryOp {
    /// Includes both with and without 'decreases_by'.
    /// The 'fun' associated with this is always the spec fun (even if it uses decreases_by)
    SpecTermination,
    /// Proof or exec. Also possible for spec, for recommends checking
    Body(Style),
}

#[derive(Clone)]
pub enum OpKind {
    /// Something that declares axioms, which will be in scope for later proof ops.
    /// Not skippable.
    Context(ContextOp, Arc<Vec<Command>>),
    /// Contains assertions that need to be proved. Doesn't introduce anything
    /// new into the context. Maybe be skipped if it's from a different module,
    /// or as a result of user options.
    /// The 'CommandsWithContext' allows for additional options like which prover to use
    Query(QueryOp, Arc<Vec<CommandsWithContext>>),
}

#[derive(Clone)]
pub struct Op {
    pub kind: OpKind,
    /// Function the op is associated with.
    pub function: Function,
}

pub struct OpGenerator<'a, D: Diagnostics> {
    pub ctx: &'a mut vir::context::Ctx,
    krate: Krate,
    bucket: Bucket,
    reporter: &'a D,

    sst_map: SstMap,
    func_map: HashMap<Fun, (Function, Visibility)>,

    current_queue: Vec<Op>,
    queue_idx: usize,
    scc_idx: usize,
    fun_idx: usize,
}

impl<'a, D: Diagnostics> OpGenerator<'a, D> {
    pub fn new(
        ctx: &'a mut vir::context::Ctx,
        krate: &Krate,
        reporter: &'a D,
        bucket: Bucket,
    ) -> Self {
        let mut func_map: HashMap<Fun, (Function, Visibility)> = HashMap::new();
        let module = ctx.module();
        for function in &krate.functions {
            assert!(!func_map.contains_key(&function.x.name));

            let vis = function.x.visibility.clone();
            if !is_visible_to(&vis, &module) || function.x.attrs.is_decrease_by {
                continue;
            }
            let restricted_to = if function.x.publish.is_none() {
                // private to owning_module
                function.x.owning_module.clone()
            } else {
                // public
                None
            };
            let vis_abs = Visibility { restricted_to, ..vis };

            func_map.insert(function.x.name.clone(), (function.clone(), vis_abs));
        }

        OpGenerator {
            ctx,
            krate: krate.clone(),
            func_map,
            bucket,
            reporter,
            sst_map: UpdateCell::new(HashMap::new()),
            current_queue: vec![],
            queue_idx: 0,
            scc_idx: 0,
            fun_idx: 0,
        }
    }

    pub fn next(&mut self) -> Result<Option<Op>, VirErr> {
        let op_opt = self._next()?;
        if let Some(op) = &op_opt {
            if matches!(op.kind, OpKind::Query(..)) {
                assert!(self.bucket.contains(&op.function.x.name));
            }
        }
        Ok(op_opt)
    }

    fn _next(&mut self) -> Result<Option<Op>, VirErr> {
        loop {
            if self.queue_idx < self.current_queue.len() {
                self.queue_idx += 1;
                return Ok(Some(self.current_queue[self.queue_idx - 1].clone()));
            } else {
                self.queue_idx = 0;

                // Iterate through each SCC and do spec stuff,
                // Then iterate through every function and prove its body
                // if necessary.
                // TODO this ordering needs a revisit
                if self.scc_idx < self.ctx.global.func_call_sccs.len() {
                    self.current_queue = self.handle_specs_scc_component(
                        self.ctx.global.func_call_sccs[self.scc_idx].clone(),
                    )?;
                    self.scc_idx += 1;
                } else if self.fun_idx < self.krate.functions.len() {
                    self.current_queue = self.handle_proof_body_normal_for_proof_and_exec(
                        self.krate.functions[self.fun_idx].clone(),
                    )?;
                    self.fun_idx += 1;
                } else {
                    return Ok(None);
                }
            }
        }
    }

    pub fn retry_with_recommends(&mut self, op: &Op, from_error: bool) -> Result<(), VirErr> {
        let ops = self.handle_proof_body_recommends(op.function.clone(), from_error)?;
        self.append_to_front_of_queue(ops);
        Ok(())
    }

    pub fn retry_with_expand_errors(
        &mut self,
        op: &Op,
        expand_targets: Vec<Message>,
    ) -> Result<(), VirErr> {
        let ops = self.handle_proof_body_expand(op.function.clone(), expand_targets)?;
        self.append_to_front_of_queue(ops);
        Ok(())
    }

    fn append_to_front_of_queue(&mut self, ops: Vec<Op>) {
        // Remove everything in self.current_queue up to queue_idx (already processed)
        // And prepend `ops`. Reset the queue_idx to 0.
        let mut ops = ops;
        std::mem::swap(&mut ops, &mut self.current_queue);
        self.current_queue.append(&mut ops[self.queue_idx..].to_vec());
        self.queue_idx = 0;
    }

    fn handle_specs_scc_component(&mut self, scc_rep: Node) -> Result<Vec<Op>, VirErr> {
        let scc_nodes = self.ctx.global.func_call_graph.get_scc_nodes(&scc_rep);
        let mut scc_fun_nodes: Vec<Fun> = Vec::new();
        for node in scc_nodes.into_iter() {
            match node {
                Node::Fun(f) => scc_fun_nodes.push(f),
                _ => {}
            }
        }
        let module = self.ctx.module();

        let mut pre_ops = vec![];
        let mut query_ops = vec![];
        let mut post_ops = vec![];

        for f in scc_fun_nodes.iter() {
            let (function, _vis_abs) = if let Some(f) = self.func_map.get(f) {
                f.clone()
            } else {
                continue;
            };

            self.ctx.fun = mk_fun_ctx(&function, false);
            let decl_commands = vir::func_to_air::func_decl_to_air(
                self.ctx,
                self.reporter,
                &self.sst_map,
                &function,
            )?;
            self.ctx.fun = None;

            pre_ops.push(Op::context(ContextOp::ReqEns, decl_commands, &function));
        }

        for f in scc_fun_nodes.iter() {
            let (function, vis_abs) = if let Some(f) = self.func_map.get(f) {
                f.clone()
            } else {
                continue;
            };

            self.ctx.fun = mk_fun_ctx(&function, false);
            let not_verifying_owning_bucket = !self.bucket.contains(&function.x.name);

            let mut sst_map = UpdateCell::new(HashMap::new());
            std::mem::swap(&mut sst_map, &mut self.sst_map);
            let (decl_commands, check_commands, mut new_sst_map) =
                vir::func_to_air::func_axioms_to_air(
                    self.ctx,
                    self.reporter,
                    sst_map,
                    &function,
                    is_visible_to(&vis_abs, &module),
                    not_verifying_owning_bucket,
                )?;
            std::mem::swap(&mut new_sst_map, &mut self.sst_map);
            self.ctx.fun = None;

            if !not_verifying_owning_bucket {
                // TODO this should be unnecessary; recursion.rs turns a
                // CommandsWithContextX into a Commands, only for us to turn it
                // back into CommandsWithContextX. We should pass the CommandsWithContextX
                // all the way through in order to e.g. support nonlinear_arith in decreases_by
                let commands = Arc::new(vec![Arc::new(CommandsWithContextX {
                    span: function.span.clone(),
                    desc: "termination proof".to_string(),
                    commands: check_commands,
                    prover_choice: vir::def::ProverChoice::DefaultProver,
                    skip_recommends: false,
                })]);
                query_ops.push(Op::query(QueryOp::SpecTermination, commands, &function));
            }

            let op_kind = if function.x.broadcast_forall.is_some() {
                ContextOp::Broadcast
            } else {
                ContextOp::SpecDefinition
            };
            post_ops.push(Op::context(op_kind, decl_commands, &function));
        }

        let mut ops = pre_ops;
        ops.append(&mut query_ops);
        ops.append(&mut post_ops);
        Ok(ops)
    }

    fn handle_proof_body_normal_for_proof_and_exec(
        &mut self,
        function: Function,
    ) -> Result<Vec<Op>, VirErr> {
        if function.x.mode == Mode::Spec && !function.x.is_const {
            Ok(vec![])
        } else {
            self.handle_proof_body(function, Style::Normal, None)
        }
    }

    fn handle_proof_body_expand(
        &mut self,
        function: Function,
        expand_targets: Vec<Message>,
    ) -> Result<Vec<Op>, VirErr> {
        self.handle_proof_body(function, Style::Expanded, Some(expand_targets))
    }

    fn handle_proof_body_recommends(
        &mut self,
        function: Function,
        from_error: bool,
    ) -> Result<Vec<Op>, VirErr> {
        self.handle_proof_body(
            function,
            if from_error { Style::RecommendsFollowupFromError } else { Style::RecommendsChecked },
            None,
        )
    }

    fn handle_proof_body(
        &mut self,
        function: Function,
        style: Style,
        expand_targets: Option<Vec<Message>>,
    ) -> Result<Vec<Op>, VirErr> {
        let fun = &function.x.name;

        if !self.bucket.contains(fun) {
            return Ok(vec![]);
        }

        let (recommend, expand) = match style {
            Style::Normal => (false, false),
            Style::RecommendsFollowupFromError | Style::RecommendsChecked => (true, false),
            Style::Expanded => (false, true),
        };

        if expand {
            self.ctx.debug_expand_targets = expand_targets.unwrap();
            self.ctx.expand_flag = true;
        }
        self.ctx.fun = mk_fun_ctx(&function, recommend);

        let mut sst_map = UpdateCell::new(HashMap::new());
        std::mem::swap(&mut sst_map, &mut self.sst_map);
        let (commands, snap_map, mut new_sst_map) = vir::func_to_air::func_def_to_air(
            self.ctx,
            self.reporter,
            sst_map,
            &function,
            // TODO revisit if we still need FuncDefPhase
            if function.x.mode == Mode::Spec && !function.x.is_const {
                vir::func_to_air::FuncDefPhase::CheckingSpecs
            } else {
                vir::func_to_air::FuncDefPhase::CheckingProofExec
            },
            recommend,
        )?;
        std::mem::swap(&mut new_sst_map, &mut self.sst_map);

        self.ctx.fun = None;
        self.ctx.expand_flag = false;

        Ok(vec![Op::query(QueryOp::Body(style), commands, &function)])
    }
}

pub fn mk_fun_ctx(f: &Function, checking_spec_preconditions: bool) -> Option<FunctionCtx> {
    Some(vir::context::FunctionCtx {
        checking_spec_preconditions,
        checking_spec_preconditions_for_non_spec: checking_spec_preconditions
            && f.x.mode != Mode::Spec,
        module_for_chosen_triggers: f.x.owning_module.clone(),
        current_fun: f.x.name.clone(),
    })
}

impl Op {
    pub fn to_air_comment(&self) -> String {
        let prefix = match &self.kind {
            OpKind::Context(ContextOp::SpecDefinition, _) => "Function-Axioms",
            OpKind::Context(ContextOp::ReqEns, _) => "Function-Specs",
            OpKind::Context(ContextOp::Broadcast, _) => "Broadcast",
            OpKind::Query(QueryOp::SpecTermination, _) => "Spec-Termination",
            OpKind::Query(QueryOp::Body(Style::Normal), _) => "Function-Def",
            OpKind::Query(
                QueryOp::Body(Style::RecommendsFollowupFromError | Style::RecommendsChecked),
                _,
            ) => "Function-Recommends",
            OpKind::Query(QueryOp::Body(Style::Expanded), _) => "Function-Expand-Errors",
        };
        format!("{:} {:}", prefix, fun_as_friendly_rust_name(&self.function.x.name))
    }

    /// Intended for Query ops, so the driver can describe queries to the user
    pub fn to_friendly_desc(&self) -> Option<&'static str> {
        match &self.kind {
            OpKind::Context(_, _) => None,
            OpKind::Query(QueryOp::SpecTermination, _) => Some("checking termination"),
            OpKind::Query(QueryOp::Body(Style::Normal), _) => None,
            OpKind::Query(
                QueryOp::Body(Style::RecommendsFollowupFromError | Style::RecommendsChecked),
                _,
            ) => Some("checking recommends"),
            OpKind::Query(QueryOp::Body(Style::Expanded), _) => Some("running expand-errors check"),
        }
    }

    pub fn context(context_op: ContextOp, commands: Arc<Vec<Command>>, f: &Function) -> Self {
        Op { kind: OpKind::Context(context_op, commands), function: f.clone() }
    }

    pub fn query(query_op: QueryOp, commands: Arc<Vec<CommandsWithContext>>, f: &Function) -> Self {
        Op { kind: OpKind::Query(query_op, commands), function: f.clone() }
    }
}

impl QueryOp {
    pub fn is_recommend(&self) -> bool {
        match self {
            QueryOp::SpecTermination => false,
            QueryOp::Body(Style::RecommendsFollowupFromError | Style::RecommendsChecked) => true,
            QueryOp::Body(Style::Normal) => false,
            QueryOp::Body(Style::Expanded) => false,
        }
    }

    pub fn is_expanded(&self) -> bool {
        match self {
            QueryOp::SpecTermination => false,
            QueryOp::Body(Style::RecommendsFollowupFromError | Style::RecommendsChecked) => false,
            QueryOp::Body(Style::Normal) => false,
            QueryOp::Body(Style::Expanded) => true,
        }
    }
}
