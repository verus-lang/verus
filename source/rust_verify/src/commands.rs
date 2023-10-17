use crate::buckets::Bucket;
use air::ast::Command;
use air::messages::Diagnostics;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Arc;
use vir::ast::Visibility;
use vir::ast::{Fun, Function, ItemKind, Krate, Mode, Path, TraitImpl, VirErr};
use vir::ast_util::fun_as_friendly_rust_name;
use vir::ast_util::is_visible_to;
use vir::context::FunctionCtx;
use vir::def::{CommandsWithContext, SnapPos};
use vir::func_to_air::SstMap;
use vir::messages::Message;
use vir::recursion::Node;
use vir::update_cell::UpdateCell;

#[derive(Clone, Copy, Debug)]
pub enum ContextOp {
    SpecDefinition,
    ReqEns,
    Broadcast,
    TraitImpl,
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
    Query {
        query_op: QueryOp,
        commands_with_context_list: Arc<Vec<CommandsWithContext>>,
        snap_map: Arc<Vec<(vir::messages::Span, SnapPos)>>,
        profile_rerun: bool,
    },
}

#[derive(Clone)]
pub struct Op {
    pub kind: OpKind,
    /// Function the op is associated with (always Some for Query kind).
    pub function: Option<Function>,
}

pub struct OpGenerator<'a, D: Diagnostics> {
    pub ctx: &'a mut vir::context::Ctx,
    bucket: Bucket,
    reporter: &'a D,

    sst_map: SstMap,
    func_map: HashMap<Fun, (Function, Visibility)>,
    trait_impl_map: HashMap<Path, TraitImpl>,

    current_queue: VecDeque<Op>,
    scc_idx: usize,
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

        let mut trait_impl_map: HashMap<Path, TraitImpl> = HashMap::new();
        for imp in &krate.trait_impls {
            assert!(!trait_impl_map.contains_key(&imp.x.impl_path));
            trait_impl_map.insert(imp.x.impl_path.clone(), imp.clone());
        }

        OpGenerator {
            ctx,
            func_map,
            trait_impl_map,
            bucket,
            reporter,
            sst_map: UpdateCell::new(HashMap::new()),
            current_queue: VecDeque::new(),
            scc_idx: 0,
        }
    }

    pub fn next(&mut self) -> Result<Option<Op>, VirErr> {
        let op_opt = self._next()?;
        if let Some(op) = &op_opt {
            if matches!(op.kind, OpKind::Query { .. }) {
                assert!(self.bucket.contains(&op.get_function().x.name));
            }
        }
        Ok(op_opt)
    }

    fn _next(&mut self) -> Result<Option<Op>, VirErr> {
        loop {
            if !self.current_queue.is_empty() {
                let op = self.current_queue.pop_front();
                return Ok(op);
            } else {
                // Iterate through each SCC
                if self.scc_idx < self.ctx.global.func_call_sccs.len() {
                    self.current_queue = VecDeque::from(self.handle_scc_component(
                        self.ctx.global.func_call_sccs[self.scc_idx].clone(),
                    )?);
                    self.scc_idx += 1;
                } else {
                    return Ok(None);
                }
            }
        }
    }

    pub fn retry_with_recommends(&mut self, op: &Op, from_error: bool) -> Result<(), VirErr> {
        let ops = self.handle_proof_body_recommends(op.get_function(), from_error)?;
        self.append_to_front_of_queue(ops);
        Ok(())
    }

    pub fn retry_with_expand_errors(
        &mut self,
        op: &Op,
        expand_targets: Vec<Message>,
    ) -> Result<(), VirErr> {
        let ops = self.handle_proof_body_expand(op.get_function(), expand_targets)?;
        self.append_to_front_of_queue(ops);
        Ok(())
    }

    pub fn retry_with_profile(
        &mut self,
        query_op: QueryOp,
        commands_with_context_list: Arc<Vec<CommandsWithContext>>,
        snap_map: Arc<Vec<(vir::messages::Span, SnapPos)>>,
        function: &Function,
    ) {
        let op = Op {
            kind: OpKind::Query {
                query_op,
                commands_with_context_list,
                snap_map,
                profile_rerun: true,
            },
            function: Some(function.clone()),
        };
        self.current_queue.push_back(op);
    }

    fn append_to_front_of_queue(&mut self, ops: Vec<Op>) {
        for op in ops.into_iter().rev() {
            self.current_queue.push_front(op);
        }
    }

    fn handle_scc_component(&mut self, scc_rep: Node) -> Result<Vec<Op>, VirErr> {
        let (mut ops, post_ops) = self.handle_specs_scc_component(&scc_rep)?;

        for node in self.ctx.global.func_call_graph.get_scc_nodes(&scc_rep) {
            if let Node::Fun(f) = node {
                if let Some((f, _)) = self.func_map.get(&f) {
                    let f_ops = self.handle_proof_body_normal_for_proof_and_exec(f.clone())?;
                    ops.extend(f_ops);
                }
            }
        }

        // Some axioms (broadcast_forall, spec definitions, trait implementations)
        // are only sound at the end of the SCC, after obligations have been satisfied:
        ops.extend(post_ops);
        for node in self.ctx.global.func_call_graph.get_scc_nodes(&scc_rep) {
            if let Node::TraitImpl(impl_path) = node {
                if let Some(imp) = self.trait_impl_map.get(&impl_path) {
                    let cmds = vir::traits::trait_impl_to_air(&self.ctx, imp);
                    ops.push(Op::context(ContextOp::TraitImpl, cmds, None));
                }
            }
        }

        Ok(ops)
    }

    fn handle_specs_scc_component(&mut self, scc_rep: &Node) -> Result<(Vec<Op>, Vec<Op>), VirErr> {
        let scc_nodes = self.ctx.global.func_call_graph.get_scc_nodes(scc_rep);
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

            pre_ops.push(Op::context(ContextOp::ReqEns, decl_commands, Some(function.clone())));
        }

        for f in scc_fun_nodes.iter() {
            let (function, vis_abs) = if let Some(f) = self.func_map.get(f) {
                f.clone()
            } else {
                continue;
            };

            self.ctx.fun = mk_fun_ctx_dec(&function, true, true);
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
                let snap_map = vec![];
                let commands = Arc::new(check_commands);
                query_ops.push(Op::query(QueryOp::SpecTermination, commands, snap_map, &function));
            }

            let op_kind = if function.x.broadcast_forall.is_some() {
                ContextOp::Broadcast
            } else {
                ContextOp::SpecDefinition
            };
            post_ops.push(Op::context(op_kind, decl_commands, Some(function.clone())));
        }

        let mut ops = pre_ops;
        ops.append(&mut query_ops);
        Ok((ops, post_ops))
    }

    fn handle_proof_body_normal_for_proof_and_exec(
        &mut self,
        function: Function,
    ) -> Result<Vec<Op>, VirErr> {
        if function.x.mode == Mode::Spec && !matches!(function.x.item_kind, ItemKind::Const) {
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
            if function.x.mode == Mode::Spec && !matches!(function.x.item_kind, ItemKind::Const) {
                vir::func_to_air::FuncDefPhase::CheckingSpecs
            } else {
                vir::func_to_air::FuncDefPhase::CheckingProofExec
            },
            recommend,
        )?;
        std::mem::swap(&mut new_sst_map, &mut self.sst_map);

        self.ctx.fun = None;
        self.ctx.expand_flag = false;

        Ok(vec![Op::query(QueryOp::Body(style), commands, snap_map, &function)])
    }
}

pub fn mk_fun_ctx_dec(
    f: &Function,
    checking_spec_preconditions: bool,
    checking_spec_decreases: bool,
) -> Option<FunctionCtx> {
    Some(vir::context::FunctionCtx {
        checking_spec_preconditions,
        checking_spec_preconditions_for_non_spec: checking_spec_preconditions
            && f.x.mode != Mode::Spec,
        checking_spec_decreases,
        module_for_chosen_triggers: f.x.owning_module.clone(),
        current_fun: f.x.name.clone(),
    })
}

pub fn mk_fun_ctx(f: &Function, checking_spec_preconditions: bool) -> Option<FunctionCtx> {
    mk_fun_ctx_dec(f, checking_spec_preconditions, false)
}

impl Op {
    pub fn to_air_comment(&self) -> String {
        fn append_profile_rerun(s: &str, profile: bool) -> String {
            if !profile { s.to_owned() } else { format!("{s}-Profile-Rerun") }
        }
        let prefix = match &self.kind {
            OpKind::Context(ContextOp::SpecDefinition, _) => "Function-Axioms".into(),
            OpKind::Context(ContextOp::ReqEns, _) => "Function-Specs".into(),
            OpKind::Context(ContextOp::Broadcast, _) => "Broadcast".into(),
            OpKind::Context(ContextOp::TraitImpl, _) => return "Trait-Impl-Axiom".to_string(),
            OpKind::Query { query_op: QueryOp::SpecTermination, profile_rerun, .. } => {
                append_profile_rerun("Spec-Termination", *profile_rerun)
            }
            OpKind::Query { query_op: QueryOp::Body(Style::Normal), profile_rerun, .. } => {
                append_profile_rerun("Function-Def", *profile_rerun)
            }
            OpKind::Query {
                query_op:
                    QueryOp::Body(Style::RecommendsFollowupFromError | Style::RecommendsChecked),
                profile_rerun,
                ..
            } => append_profile_rerun("Function-Recommends", *profile_rerun),
            OpKind::Query { query_op: QueryOp::Body(Style::Expanded), profile_rerun, .. } => {
                append_profile_rerun("Function-Expand-Errors", *profile_rerun)
            }
        };
        format!("{:} {:}", prefix, fun_as_friendly_rust_name(&self.get_function().x.name))
    }

    /// Intended for Query ops, so the driver can describe queries to the user
    pub fn to_friendly_desc(&self) -> Option<String> {
        fn append_profile_rerun(s: &str, profile: bool) -> String {
            if !profile { s.to_owned() } else { format!("{s} (profile rerun)") }
        }
        match &self.kind {
            OpKind::Context(_, _) => None,
            OpKind::Query { query_op: QueryOp::SpecTermination, profile_rerun, .. } => {
                Some(append_profile_rerun("checking termination", *profile_rerun))
            }
            OpKind::Query { query_op: QueryOp::Body(Style::Normal), profile_rerun, .. } => {
                profile_rerun.then(|| "(profile rerun)".into())
            }
            OpKind::Query {
                query_op:
                    QueryOp::Body(Style::RecommendsFollowupFromError | Style::RecommendsChecked),
                profile_rerun,
                ..
            } => Some(append_profile_rerun("checking recommends", *profile_rerun)),
            OpKind::Query { query_op: QueryOp::Body(Style::Expanded), profile_rerun, .. } => {
                Some(append_profile_rerun("running expand-errors check", *profile_rerun))
            }
        }
    }

    pub fn get_function(&self) -> Function {
        self.function.clone().expect("function")
    }

    pub fn context(
        context_op: ContextOp,
        commands: Arc<Vec<Command>>,
        f: Option<Function>,
    ) -> Self {
        Op { kind: OpKind::Context(context_op, commands), function: f }
    }

    pub fn query(
        query_op: QueryOp,
        commands: Arc<Vec<CommandsWithContext>>,
        snap_map: Vec<(vir::messages::Span, SnapPos)>,
        f: &Function,
    ) -> Self {
        Op {
            kind: OpKind::Query {
                query_op,
                commands_with_context_list: commands,
                snap_map: Arc::new(snap_map),
                profile_rerun: false,
            },
            function: Some(f.clone()),
        }
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
