use crate::ast::{
    ArchWordBits, Datatype, Fun, Function, GenericBounds, Ident, ImplPath, IntRange, Krate, Mode,
    Path, Primitive, Trait, TypPositives, TypX, Variants, VirErr,
};
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::FUEL_ID;
use crate::messages::{error, Span};
use crate::poly::MonoTyp;
use crate::recursion::Node;
use crate::scc::Graph;
use crate::sst::BndInfo;
use crate::sst_to_air::fun_to_air_ident;
use air::ast::{Command, CommandX, Commands, DeclX, MultiOp};
use air::ast_util::str_typ;
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
    pub arch: crate::ast::ArchWordBits,
    pub crate_name: Ident,
    pub vstd_crate_name: Ident,
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
    pub(crate) module: Path,
    pub(crate) datatype_is_transparent: HashMap<Path, bool>,
    pub(crate) datatypes_with_invariant: HashSet<Path>,
    pub(crate) mono_types: Vec<MonoTyp>,
    pub(crate) lambda_types: Vec<usize>,
    pub(crate) bound_traits: HashSet<Path>,
    pub(crate) fndef_types: Vec<Fun>,
    pub(crate) fndef_type_set: HashSet<Fun>,
    pub functions: Vec<Function>,
    pub func_map: HashMap<Fun, Function>,
    pub(crate) reveal_groups: Vec<crate::ast::RevealGroup>,
    pub(crate) reveal_group_set: HashSet<Fun>,
    // Ensure a unique identifier for each quantifier in a given function
    pub quantifier_count: Cell<u64>,
    pub(crate) funcs_with_ensure_predicate: HashSet<Fun>,
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
    pub expand_flag: bool,
    pub debug_expand_targets: Vec<crate::messages::Message>,
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
                        TypX::Lambda(..) => {
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
                        TypX::Bool | TypX::StrSlice | TypX::Char | TypX::AnonymousClosure(..) => {}
                        TypX::Tuple(_) | TypX::Air(_) => panic!("datatypes_invs"),
                        TypX::ConstInt(_) => {}
                        TypX::Primitive(Primitive::Array, _) => {
                            roots.insert(container_path.clone());
                        }
                        TypX::Primitive(Primitive::Slice, _) => {}
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

impl GlobalCtx {
    pub fn new(
        krate: &Krate,
        crate_name: Ident,
        no_span: Span,
        rlimit: f32,
        interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
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
            //   #[verifier::broadcast_forall] fn b<A: View>(a: A) ensures foo(a) { ... }
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

        for f in &krate.functions {
            fun_bounds.insert(f.x.name.clone(), f.x.typ_bounds.clone());
            let fun_node = Node::Fun(f.x.name.clone());
            let fndef_impl_node = Node::TraitImpl(ImplPath::FnDefImplPath(f.x.name.clone()));
            func_call_graph.add_node(fun_node.clone());
            func_call_graph.add_node(fndef_impl_node.clone());
            func_call_graph.add_edge(fndef_impl_node, fun_node);
            crate::recursion::expand_call_graph(
                &func_map,
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

        func_call_graph.compute_sccs();
        let func_call_sccs = func_call_graph.sort_sccs();
        for f in &krate.functions {
            let f_node = Node::Fun(f.x.name.clone());
            if f.x.attrs.is_decrease_by {
                for g_node in func_call_graph.get_scc_nodes(&f_node) {
                    if f_node != g_node {
                        let g =
                            krate.functions.iter().find(|g| Node::Fun(g.x.name.clone()) == g_node);
                        return Err(crate::messages::error(
                            &f.span,
                            "found cyclic dependency in decreases_by function",
                        )
                        .secondary_span(&g.unwrap().span));
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
        module: Path,
        mono_types: Vec<MonoTyp>,
        lambda_types: Vec<usize>,
        bound_traits: HashSet<Path>,
        fndef_types: Vec<Fun>,
        debug: bool,
    ) -> Result<Self, VirErr> {
        let mut datatype_is_transparent: HashMap<Path, bool> = HashMap::new();
        for datatype in krate.datatypes.iter() {
            datatype_is_transparent
                .insert(datatype.x.path.clone(), is_datatype_transparent(&module, datatype));
        }
        let datatypes_with_invariant =
            datatypes_invs(&module, &datatype_is_transparent, &krate.datatypes);
        let mut functions: Vec<Function> = Vec::new();
        let mut func_map: HashMap<Fun, Function> = HashMap::new();
        let funcs_with_ensure_predicate: HashSet<Fun> = HashSet::new();
        for function in krate.functions.iter() {
            func_map.insert(function.x.name.clone(), function.clone());
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
            lambda_types,
            bound_traits,
            fndef_types,
            fndef_type_set,
            functions,
            func_map,
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
            expand_flag: false,
            debug_expand_targets: vec![],
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

    pub fn module(&self) -> Path {
        self.module.clone()
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
        let decl = Arc::new(DeclX::Axiom(distinct));
        commands.push(Arc::new(CommandX::Global(decl)));
        for group in &self.reveal_groups {
            crate::func_to_air::broadcast_forall_group_axioms(
                self,
                &mut commands,
                group,
                &self.global.crate_name,
            );
        }
        Arc::new(commands)
    }
}
