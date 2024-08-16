use crate::ast::{
    ArchWordBits, Datatype, Fun, Function, FunctionAttrs, GenericBounds, Ident, ImplPath, IntRange,
    Krate, Mode, Module, Path, Primitive, Trait, TypPositives, TypX, Variants, VirErr,
};
use crate::ast_util::path_as_friendly_rust_name_raw;
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::FUEL_ID;
use crate::messages::{error, Span};
use crate::poly::MonoTyp;
use crate::recursion::Node;
use crate::scc::Graph;
use crate::sst::BndInfo;
use crate::sst_to_air::fun_to_air_ident;
use air::ast::{Command, CommandX, Commands, DeclX, MultiOp};
use air::ast_util::{mk_unnamed_axiom, str_typ};
use air::context::SmtSolver;
use num_bigint::BigUint;
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::sync::Arc;

// Use decorated types in addition to undecorated types (see sst_to_air::typ_to_ids)
pub(crate) const DECORATE: bool = true;

pub type ChosenTrigger = Vec<(Span, String)>;
#[derive(Debug, Clone)]
pub struct ChosenTriggers {
    pub module: Path,
    pub span: Span,
    pub triggers: Vec<ChosenTrigger>,
    pub low_confidence: bool,
}

/// Context for across all modules
pub struct GlobalCtx {
    pub(crate) chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>>, // diagnostics
    pub(crate) datatypes: Arc<HashMap<Path, (TypPositives, Variants)>>,
    pub(crate) fun_bounds: Arc<HashMap<Fun, GenericBounds>>,
    pub(crate) fun_attrs: Arc<HashMap<Fun, FunctionAttrs>>,
    /// Used for synthesized AST nodes that have no relation to any location in the original code:
    pub(crate) no_span: Span,
    pub func_call_graph: Arc<Graph<Node>>,
    pub func_call_sccs: Arc<Vec<Node>>,
    pub(crate) datatype_graph: Arc<Graph<crate::recursive_types::TypNode>>,
    pub(crate) datatype_graph_span_infos: Vec<Span>,
    /// Connects quantifier identifiers to the original expression
    pub qid_map: RefCell<HashMap<String, BndInfo>>,
    pub(crate) rlimit: f32,
    pub(crate) interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
    pub(crate) func_call_graph_log: Arc<std::sync::Mutex<Option<FuncCallGraphLogFiles>>>,
    pub arch: crate::ast::ArchWordBits,
    pub crate_name: Ident,
    pub vstd_crate_name: Ident,
    pub solver: SmtSolver,
}

// Context for verifying one function
#[derive(Debug)]
pub struct FunctionCtx {
    // false normally, true if we're just checking spec preconditions
    pub checking_spec_preconditions: bool,
    // false normally, true if we're just checking spec preconditions for a non-spec function
    pub checking_spec_preconditions_for_non_spec: bool,
    // false normally, true if we're just checking decreases of recursive spec function
    pub checking_spec_decreases: bool,
    // used to print diagnostics for triggers
    pub module_for_chosen_triggers: Option<Path>,
    // used to create quantifier identifiers and for checking_spec_preconditions
    pub current_fun: Fun,
}

// Context for verifying one module
pub struct Ctx {
    pub(crate) module: Module,
    pub(crate) datatype_is_transparent: HashMap<Path, bool>,
    pub(crate) datatypes_with_invariant: HashSet<Path>,
    pub(crate) mono_types: Vec<MonoTyp>,
    pub(crate) spec_fn_types: Vec<usize>,
    pub(crate) uses_array: bool,
    pub(crate) fndef_types: Vec<Fun>,
    pub(crate) fndef_type_set: HashSet<Fun>,
    pub functions: Vec<Function>,
    pub func_map: HashMap<Fun, Function>,
    pub func_sst_map: HashMap<Fun, crate::sst::FunctionSst>,
    pub fun_ident_map: HashMap<Ident, Fun>,
    pub(crate) reveal_groups: Vec<crate::ast::RevealGroup>,
    pub(crate) reveal_group_set: HashSet<Fun>,
    // Ensure a unique identifier for each quantifier in a given function
    pub quantifier_count: Cell<u64>,
    pub(crate) funcs_with_ensure_predicate: HashMap<Fun, bool>,
    pub(crate) datatype_map: HashMap<Path, Datatype>,
    pub(crate) trait_map: HashMap<Path, Trait>,
    pub fun: Option<FunctionCtx>,
    pub global: GlobalCtx,
    // In the very unlikely case where we get sha512 collisions
    // we use this to panic rather than introduce unsoundness.
    // Of course it can be argued that accounting for sha512 collisions
    // is overkill, perhaps this should be revisited.
    pub(crate) string_hashes: RefCell<HashMap<BigUint, Arc<String>>>,
    // proof debug purposes
    pub debug: bool,
    pub arch_word_bits: ArchWordBits,
}

impl Ctx {
    pub fn checking_spec_preconditions(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_spec_preconditions: true, .. }) => true,
            _ => false,
        }
    }

    pub fn checking_spec_preconditions_for_non_spec(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_spec_preconditions_for_non_spec: true, .. }) => true,
            _ => false,
        }
    }

    pub fn checking_spec_decreases(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_spec_decreases: true, .. }) => true,
            _ => false,
        }
    }
}

fn datatypes_inv_visit(
    back_pointers: &HashMap<Path, HashSet<Path>>,
    has_inv: &mut HashSet<Path>,
    root: &Path,
) {
    if has_inv.contains(root) {
        return;
    }
    has_inv.insert(root.clone());
    for container_path in &back_pointers[root] {
        datatypes_inv_visit(back_pointers, has_inv, container_path);
    }
}

// If a datatype's fields have invariants, the datatype needs an invariant
fn datatypes_invs(
    module: &Path,
    datatype_is_transparent: &HashMap<Path, bool>,
    datatypes: &Vec<Datatype>,
) -> HashSet<Path> {
    let mut back_pointers: HashMap<Path, HashSet<Path>> =
        datatypes.iter().map(|d| (d.x.path.clone(), HashSet::new())).collect();
    let mut has_inv: HashSet<Path> = HashSet::new();
    let mut roots: HashSet<Path> = HashSet::new();
    for datatype in datatypes {
        if is_datatype_transparent(module, datatype) {
            let container_path = &datatype.x.path;
            for variant in datatype.x.variants.iter() {
                for field in variant.fields.iter() {
                    match &*crate::ast_util::undecorate_typ(&field.a.0) {
                        // Should be kept in sync with vir::sst_to_air::typ_invariant
                        TypX::Int(IntRange::Int) => {}
                        TypX::Int(_) | TypX::TypParam(_) | TypX::Projection { .. } => {
                            roots.insert(container_path.clone());
                        }
                        TypX::SpecFn(..) => {
                            roots.insert(container_path.clone());
                        }
                        TypX::Datatype(field_path, _, _) => {
                            if datatype_is_transparent[field_path] {
                                back_pointers
                                    .get_mut(field_path)
                                    .expect("datatypes_invs")
                                    .insert(container_path.clone());
                            } else {
                                if crate::poly::typ_as_mono(&field.a.0).is_none() {
                                    roots.insert(container_path.clone());
                                }
                            }
                        }
                        TypX::FnDef(..) => {}
                        TypX::Decorate(..) => unreachable!("TypX::Decorate"),
                        TypX::Boxed(_) => {}
                        TypX::TypeId => {}
                        TypX::Bool | TypX::AnonymousClosure(..) => {}
                        TypX::Tuple(_) | TypX::Air(_) => panic!("datatypes_invs"),
                        TypX::ConstInt(_) => {}
                        TypX::Primitive(
                            Primitive::Array | Primitive::Slice | Primitive::Ptr,
                            _,
                        ) => {
                            // Each of these is like an abstract Datatype
                            if crate::poly::typ_as_mono(&field.a.0).is_none() {
                                roots.insert(container_path.clone());
                            }
                        }
                        TypX::Primitive(Primitive::StrSlice, _) => {}
                        TypX::Primitive(Primitive::Global, _) => {}
                    }
                }
            }
        }
    }
    for root in &roots {
        datatypes_inv_visit(&back_pointers, &mut has_inv, root);
    }
    has_inv
}

pub struct FuncCallGraphLogFiles {
    pub all_initial: File,
    pub all_simplified: File,
    pub nostd_initial: File,
    pub nostd_simplified: File,
}

impl GlobalCtx {
    pub fn new(
        krate: &Krate,
        crate_name: Ident,
        no_span: Span,
        rlimit: f32,
        interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
        func_call_graph_log: Arc<std::sync::Mutex<Option<FuncCallGraphLogFiles>>>,
        solver: SmtSolver,
        after_simplify: bool,
    ) -> Result<Self, VirErr> {
        let chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>> =
            std::cell::RefCell::new(Vec::new());

        let datatypes: HashMap<Path, (TypPositives, Variants)> = krate
            .datatypes
            .iter()
            .map(|d| (d.x.path.clone(), (d.x.typ_params.clone(), d.x.variants.clone())))
            .collect();
        let mut func_map: HashMap<Fun, Function> = HashMap::new();
        for function in krate.functions.iter() {
            assert!(!func_map.contains_key(&function.x.name));
            func_map.insert(function.x.name.clone(), function.clone());
        }
        let mut fun_bounds: HashMap<Fun, GenericBounds> = HashMap::new();
        let mut fun_attrs: HashMap<Fun, FunctionAttrs> = HashMap::new();
        let reveal_group_set: HashSet<Fun> =
            krate.reveal_groups.iter().map(|g| g.x.name.clone()).collect();

        let mut func_call_graph: Graph<Node> = Graph::new();

        for t in &krate.traits {
            crate::recursive_types::add_trait_to_graph(&mut func_call_graph, t);
        }
        for f in &krate.functions {
            // Heuristic: add all external_body functions first.
            // This is currently needed because external_body broadcast_forall functions
            // are currently implicitly imported.
            // In the future, this might become less important; we could remove this heuristic.
            if f.x.body.is_none() && f.x.extra_dependencies.len() == 0 {
                func_call_graph.add_node(Node::Fun(f.x.name.clone()));
            }
        }
        for f in &krate.functions {
            // HACK: put spec functions early, because the call graph is currently missing some
            // dependencies that should explicitly force these functions to appear early.
            // TODO: add these dependencies to the call graph.
            if f.x.mode == Mode::Spec {
                func_call_graph.add_node(Node::Fun(f.x.name.clone()));
            }
        }
        for t in &krate.trait_impls {
            // Heuristic: put trait impls first, because functions don't necessarily have
            // explicit dependencies on all the trait impls when they are implicitly
            // used to satisfy broadcast_forall trait bounds.
            // (This arises because unlike in Coq or F*, Rust programs don't define a
            // total ordering on declarations, and the call graph only provides a partial order.)
            // test_broadcast_forall2 in rust_verify_test/tests/traits.rs is one (contrived) example
            // that would fail without this heuristic.
            // A simpler example would be a broadcast_forall function with a type parameter
            // "A: View", and someone might rely on this broadcast_forall, instantiating A with
            // some struct S that implements View, but without actually calling any View methods
            // on S:
            //   trait View { spec fn view(...) -> ...; }
            //   struct S;
            //   impl View for S { ... }
            //   #[verus::internal(broadcast_forall)] fn b<A: View>(a: A) ensures foo(a) { ... }
            //   fn test(s: S) { assert(foo(s)); }
            // Here, there are no explicit dependencies in the call graph that force
            // TraitImpl for S: View to appear before "test" in the generated AIR code.
            // If the TraitImpl axiom for S: View appeared after test,
            // then test might fail because the broadcast_forall b for s isn't enabled
            // without S: View.  The programmer would have to provide some explicit ordering,
            // such as using s.view() in test so that test depends on S: View, to fix this.
            func_call_graph
                .add_node(Node::TraitImpl(ImplPath::TraitImplPath(t.x.impl_path.clone())));
        }

        let mut span_infos: Vec<Span> = Vec::new();
        for t in &krate.trait_impls {
            crate::recursive_types::add_trait_impl_to_graph(
                &mut span_infos,
                &mut func_call_graph,
                t,
            );
        }

        // map (method, impl) to impl Fun
        let mut trait_impl_map: HashMap<(Fun, Path), Fun> = HashMap::new();
        for f in &krate.functions {
            if let crate::ast::FunctionKind::TraitMethodImpl { method, impl_path, .. } = &f.x.kind {
                let key = (method.clone(), impl_path.clone());
                assert!(!trait_impl_map.contains_key(&key));
                trait_impl_map.insert(key, f.x.name.clone());
            }
        }

        for f in &krate.functions {
            fun_bounds.insert(f.x.name.clone(), f.x.typ_bounds.clone());
            let fun_node = Node::Fun(f.x.name.clone());
            let fndef_impl_node = Node::TraitImpl(ImplPath::FnDefImplPath(f.x.name.clone()));
            func_call_graph.add_node(fun_node.clone());
            func_call_graph.add_node(fndef_impl_node.clone());
            func_call_graph.add_edge(fndef_impl_node, fun_node);

            fun_attrs.insert(f.x.name.clone(), f.x.attrs.clone());

            crate::recursion::expand_call_graph(
                &func_map,
                &trait_impl_map,
                &reveal_group_set,
                &mut func_call_graph,
                &mut span_infos,
                f,
            )?;
        }
        for group in &krate.reveal_groups {
            let group_node = Node::Fun(group.x.name.clone());
            func_call_graph.add_node(group_node.clone());
            for member in group.x.members.iter() {
                let target = Node::Fun(member.clone());
                func_call_graph.add_node(target.clone());
                func_call_graph.add_edge(group_node.clone(), target);
            }
        }
        for module in &krate.modules {
            if let Some(ref reveals) = module.x.reveals {
                let module_reveal_node = Node::ModuleReveal(module.x.path.clone());
                func_call_graph.add_node(module_reveal_node.clone());
                for fun in reveals.x.iter() {
                    let target = Node::Fun(fun.clone());
                    func_call_graph.add_node(target.clone());
                    func_call_graph.add_edge(module_reveal_node.clone(), target);
                }

                for f in krate
                    .functions
                    .iter()
                    .filter(|f| f.x.owning_module.as_ref() == Some(&module.x.path))
                {
                    let source = Node::Fun(f.x.name.clone());
                    func_call_graph.add_node(source.clone());
                    func_call_graph.add_edge(source, module_reveal_node.clone());
                }
            }
        }

        func_call_graph.compute_sccs();
        let func_call_sccs = func_call_graph.sort_sccs();

        if let Some(FuncCallGraphLogFiles {
            all_initial,
            all_simplified,
            nostd_initial,
            nostd_simplified,
        }) = &mut *func_call_graph_log.lock().expect("cannot lock call graph log file")
        {
            fn node_options(n: &Node) -> String {
                fn labelize(name: &str, s: String) -> String {
                    let label = s.replace("\"", "\\\"");
                    format!("margin=0.1, label=\"{}\\n{}\"", name, label)
                }
                #[rustfmt::skip] // v to work around attributes being experimental on expressions
                let v = match n {
                    Node::Fun(fun) =>                         labelize("Fun", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"cds\"",
                    Node::Datatype(path) =>                   labelize("Datatype", path_as_friendly_rust_name_raw(path)) + ", shape=\"folder\"",
                    Node::Trait(path) =>                      labelize("Trait", path_as_friendly_rust_name_raw(path)) + ", shape=\"tab\"",
                    Node::TraitImpl(impl_path) => {
                        match impl_path {
                            ImplPath::TraitImplPath(path) =>  labelize("TraitImplPath", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                            ImplPath::FnDefImplPath(fun) =>   labelize("FnDefImplPath", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"component\"",
                        }
                    }
                    Node::TraitReqEns(impl_path, true) => {
                        match impl_path {
                            ImplPath::TraitImplPath(path) =>  labelize("ReqEns?TraitImplPath", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                            ImplPath::FnDefImplPath(fun) =>   labelize("ReqEns?FnDefImplPath", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"component\"",
                        }
                    }
                    Node::TraitReqEns(impl_path, false) => {
                        match impl_path {
                            ImplPath::TraitImplPath(path) =>  labelize("ReqEns!TraitImplPath", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                            ImplPath::FnDefImplPath(fun) =>   labelize("ReqEns!FnDefImplPath", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"component\"",
                        }
                    }
                    Node::ModuleReveal(path) =>               labelize("ModuleReveal", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                    Node::SpanInfo { span_infos_index: _, text: _ } => {
                        format!("shape=\"point\"")
                    }
                };
                v
            }

            fn nostd_filter(n: &Node) -> (bool, bool) {
                fn is_not_std(path: &Path) -> bool {
                    match path.krate.as_ref().map(|x| x.as_str()) {
                        Some("vstd") | Some("core") | Some("alloc") => false,
                        _ => true,
                    }
                }
                let render = match n {
                    Node::Fun(fun) => is_not_std(&fun.path),
                    Node::Datatype(path) => is_not_std(path),
                    Node::Trait(path) => is_not_std(path),
                    Node::TraitImpl(ImplPath::TraitImplPath(path)) => is_not_std(path),
                    Node::TraitImpl(ImplPath::FnDefImplPath(fun)) => is_not_std(&fun.path),
                    Node::TraitReqEns(ImplPath::TraitImplPath(path), _) => is_not_std(path),
                    Node::TraitReqEns(ImplPath::FnDefImplPath(fun), _) => is_not_std(&fun.path),
                    Node::ModuleReveal(path) => is_not_std(path),
                    Node::SpanInfo { .. } => true,
                };
                (render, render && !matches!(n, Node::SpanInfo { .. }))
            }

            if !after_simplify {
                func_call_graph.to_dot(all_initial, |_| (true, true), node_options);
                func_call_graph.to_dot(nostd_initial, nostd_filter, node_options);
            } else {
                func_call_graph.to_dot(all_simplified, |_| (true, true), node_options);
                func_call_graph.to_dot(nostd_simplified, nostd_filter, node_options);
            }
        }

        for f in &krate.functions {
            let f_node = Node::Fun(f.x.name.clone());
            if f.x.attrs.is_decrease_by {
                for g_node in func_call_graph.get_scc_nodes(&f_node) {
                    if f_node != g_node {
                        let g_opt =
                            krate.functions.iter().find(|g| Node::Fun(g.x.name.clone()) == g_node);
                        let mut error = crate::messages::error(
                            &f.span,
                            "found cyclic dependency in decreases_by function",
                        );
                        if let Some(g) = g_opt {
                            error = error.secondary_span(&g.span);
                        }
                        return Err(error);
                    }
                }
            }
            if f.x.attrs.atomic {
                let fun_node = Node::Fun(f.x.name.clone());
                if func_call_graph.node_is_in_cycle(&fun_node) {
                    return Err(error(&f.span, "'atomic' cannot be used on a recursive function"));
                }
            }
        }
        let qid_map = RefCell::new(HashMap::new());

        let datatype_graph = crate::recursive_types::build_datatype_graph(krate, &mut span_infos);
        let vstd_crate_name = Arc::new(crate::def::VERUSLIB.to_string());

        Ok(GlobalCtx {
            chosen_triggers,
            datatypes: Arc::new(datatypes),
            fun_bounds: Arc::new(fun_bounds),
            fun_attrs: Arc::new(fun_attrs),
            no_span,
            func_call_graph: Arc::new(func_call_graph),
            func_call_sccs: Arc::new(func_call_sccs),
            datatype_graph: Arc::new(datatype_graph),
            datatype_graph_span_infos: span_infos,
            qid_map,
            rlimit,
            interpreter_log,
            arch: krate.arch.word_bits,
            crate_name,
            vstd_crate_name,
            func_call_graph_log,
            solver,
        })
    }

    pub fn from_self_with_log(&self, interpreter_log: Arc<std::sync::Mutex<Option<File>>>) -> Self {
        let chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>> =
            std::cell::RefCell::new(Vec::new());
        let qid_map = RefCell::new(HashMap::new());

        GlobalCtx {
            chosen_triggers,
            datatypes: self.datatypes.clone(),
            fun_bounds: self.fun_bounds.clone(),
            fun_attrs: self.fun_attrs.clone(),
            no_span: self.no_span.clone(),
            func_call_graph: self.func_call_graph.clone(),
            datatype_graph: self.datatype_graph.clone(),
            datatype_graph_span_infos: self.datatype_graph_span_infos.clone(),
            func_call_sccs: self.func_call_sccs.clone(),
            qid_map,
            rlimit: self.rlimit,
            interpreter_log,
            arch: self.arch,
            crate_name: self.crate_name.clone(),
            vstd_crate_name: self.vstd_crate_name.clone(),
            func_call_graph_log: self.func_call_graph_log.clone(),
            solver: self.solver.clone(),
        }
    }

    pub fn merge(&mut self, other: Self) {
        self.qid_map.borrow_mut().extend(other.qid_map.into_inner());
        self.chosen_triggers.borrow_mut().extend(other.chosen_triggers.into_inner());
    }

    // Report chosen triggers as strings for printing diagnostics
    pub fn get_chosen_triggers(&self) -> Vec<ChosenTriggers> {
        self.chosen_triggers.borrow().clone()
    }

    pub fn set_interpreter_log_file(
        &mut self,
        interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
    ) {
        self.interpreter_log = interpreter_log;
    }
}

impl Ctx {
    pub fn new(
        krate: &Krate,
        global: GlobalCtx,
        module: Module,
        mono_types: Vec<MonoTyp>,
        spec_fn_types: Vec<usize>,
        uses_array: bool,
        fndef_types: Vec<Fun>,
        debug: bool,
    ) -> Result<Self, VirErr> {
        let mut datatype_is_transparent: HashMap<Path, bool> = HashMap::new();
        for datatype in krate.datatypes.iter() {
            datatype_is_transparent
                .insert(datatype.x.path.clone(), is_datatype_transparent(&module.x.path, datatype));
        }
        let datatypes_with_invariant =
            datatypes_invs(&module.x.path, &datatype_is_transparent, &krate.datatypes);
        let mut functions: Vec<Function> = Vec::new();
        let mut func_map: HashMap<Fun, Function> = HashMap::new();
        let mut fun_ident_map: HashMap<Ident, Fun> = HashMap::new();
        let funcs_with_ensure_predicate: HashMap<Fun, bool> = HashMap::new();
        for function in krate.functions.iter() {
            func_map.insert(function.x.name.clone(), function.clone());
            fun_ident_map.insert(fun_to_air_ident(&function.x.name), function.x.name.clone());
            functions.push(function.clone());
        }
        let mut datatype_map: HashMap<Path, Datatype> = HashMap::new();
        for datatype in krate.datatypes.iter() {
            datatype_map.insert(datatype.x.path.clone(), datatype.clone());
        }
        let mut trait_map: HashMap<Path, Trait> = HashMap::new();
        for tr in krate.traits.iter() {
            trait_map.insert(tr.x.name.clone(), tr.clone());
        }
        let reveal_group_set: HashSet<Fun> =
            krate.reveal_groups.iter().map(|g| g.x.name.clone()).collect();
        fun_ident_map.extend(reveal_group_set.iter().map(|g| (fun_to_air_ident(&g), g.clone())));
        let quantifier_count = Cell::new(0);
        let string_hashes = RefCell::new(HashMap::new());

        let mut fndef_type_set = HashSet::new();
        for fndef_type in fndef_types.iter() {
            fndef_type_set.insert(fndef_type.clone());
        }

        Ok(Ctx {
            module,
            datatype_is_transparent,
            datatypes_with_invariant,
            mono_types,
            spec_fn_types,
            uses_array,
            fndef_types,
            fndef_type_set,
            functions,
            func_map,
            func_sst_map: HashMap::new(),
            fun_ident_map,
            reveal_groups: krate.reveal_groups.clone(),
            reveal_group_set,
            quantifier_count,
            funcs_with_ensure_predicate,
            datatype_map,
            trait_map,
            fun: None,
            global,
            string_hashes,
            debug,
            arch_word_bits: krate.arch.word_bits,
        })
    }

    pub fn free(self) -> GlobalCtx {
        self.global
    }

    pub fn prelude(prelude_config: crate::prelude::PreludeConfig) -> Commands {
        let nodes = crate::prelude::prelude_nodes(prelude_config);
        air::parser::Parser::new(Arc::new(crate::messages::VirMessageInterface {}))
            .nodes_to_commands(&nodes)
            .expect("internal error: malformed prelude")
    }

    pub fn module_path(&self) -> Path {
        self.module.x.path.clone()
    }

    pub fn fuel(&self) -> Commands {
        let mut ids: Vec<air::ast::Expr> = Vec::new();
        let mut commands: Vec<Command> = Vec::new();
        let mut names: Vec<Fun> = Vec::new();
        for function in &self.functions {
            match (function.x.mode, function.x.body.as_ref(), function.x.attrs.broadcast_forall) {
                (Mode::Spec, Some(_), false) | (Mode::Proof, _, true) => {
                    names.push(function.x.name.clone());
                }
                _ => {}
            }
        }
        for group in &self.reveal_groups {
            names.push(group.x.name.clone());
        }
        for name in names {
            let id = crate::def::prefix_fuel_id(&fun_to_air_ident(&name));
            ids.push(air::ast_util::ident_var(&id));
            let decl = Arc::new(DeclX::Const(id, str_typ(&FUEL_ID)));
            commands.push(Arc::new(CommandX::Global(decl)));
        }
        let distinct = Arc::new(air::ast::ExprX::Multi(MultiOp::Distinct, Arc::new(ids)));
        let decl = mk_unnamed_axiom(distinct);
        commands.push(Arc::new(CommandX::Global(decl)));
        for group in &self.reveal_groups {
            crate::sst_to_air_func::broadcast_forall_group_axioms(
                self,
                &mut commands,
                group,
                &self.global.crate_name,
            );
        }
        crate::sst_to_air_func::module_reveal_axioms(self, &mut commands, &self.module.x.reveals);
        Arc::new(commands)
    }
}
