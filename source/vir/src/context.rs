use crate::ast::{
    Datatype, Fun, Function, GenericBounds, Ident, InferMode, IntRange, Krate, Mode, Path, Trait,
    TypX, Variants, VirErr,
};
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::FUEL_ID;
use crate::messages::{error, Span};
use crate::poly::MonoTyp;
use crate::prelude::ArchWordBits;
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
    pub(crate) datatypes: Arc<HashMap<Path, Variants>>,
    pub(crate) fun_bounds: Arc<HashMap<Fun, GenericBounds>>,
    /// Used for synthesized AST nodes that have no relation to any location in the original code:
    pub(crate) no_span: Span,
    pub func_call_graph: Arc<Graph<Node>>,
    pub func_call_sccs: Arc<Vec<Node>>,
    pub(crate) datatype_graph: Arc<Graph<crate::recursive_types::TypNode>>,
    /// Connects quantifier identifiers to the original expression
    pub qid_map: RefCell<HashMap<String, BndInfo>>,
    pub(crate) inferred_modes: Arc<HashMap<InferMode, Mode>>,
    pub(crate) rlimit: u32,
    pub(crate) interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
    pub(crate) vstd_crate_name: Option<Ident>, // already an arc
    pub arch: ArchWordBits,
}

// Context for verifying one function
pub struct FunctionCtx {
    // false normally, true if we're just checking recommends
    pub checking_recommends: bool,
    // false normally, true if we're just checking recommends for a non-spec function
    pub checking_recommends_for_non_spec: bool,
    // used to print diagnostics for triggers
    pub module_for_chosen_triggers: Option<Path>,
    // used to create quantifier identifiers and for checking_recommends
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
    pub functions: Vec<Function>,
    pub func_map: HashMap<Fun, Function>,
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
}

impl Ctx {
    pub fn checking_recommends(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_recommends: true, .. }) => true,
            _ => false,
        }
    }

    pub fn checking_recommends_for_non_spec(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_recommends_for_non_spec: true, .. }) => true,
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
                for field in variant.a.iter() {
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
                        TypX::Decorate(..) => unreachable!("TypX::Decorate"),
                        TypX::Boxed(_) => {}
                        TypX::TypeId => {}
                        TypX::Bool | TypX::StrSlice | TypX::Char | TypX::AnonymousClosure(..) => {}
                        TypX::Tuple(_) | TypX::Air(_) => panic!("datatypes_invs"),
                        TypX::ConstInt(_) => {}
                        TypX::Primitive(_, _) => {}
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
        no_span: Span,
        inferred_modes: HashMap<InferMode, Mode>,
        rlimit: u32,
        interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
        vstd_crate_name: Option<Ident>,
        arch: ArchWordBits,
    ) -> Result<Self, VirErr> {
        let chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>> =
            std::cell::RefCell::new(Vec::new());

        let datatypes: HashMap<Path, Variants> =
            krate.datatypes.iter().map(|d| (d.x.path.clone(), d.x.variants.clone())).collect();
        let mut func_map: HashMap<Fun, Function> = HashMap::new();
        for function in krate.functions.iter() {
            assert!(!func_map.contains_key(&function.x.name));
            func_map.insert(function.x.name.clone(), function.clone());
        }
        let mut fun_bounds: HashMap<Fun, GenericBounds> = HashMap::new();
        let mut func_call_graph: Graph<Node> = Graph::new();
        for t in &krate.traits {
            crate::recursive_types::add_trait_to_graph(&mut func_call_graph, t);
        }
        for f in &krate.functions {
            fun_bounds.insert(f.x.name.clone(), f.x.typ_bounds.clone());
            func_call_graph.add_node(Node::Fun(f.x.name.clone()));
            crate::recursion::expand_call_graph(&func_map, &mut func_call_graph, f)?;
        }

        func_call_graph.compute_sccs();
        let func_call_sccs = func_call_graph.sort_sccs();
        for f in &krate.functions {
            if f.x.attrs.is_decrease_by {
                let f_node = Node::Fun(f.x.name.clone());
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
                let f_node = Node::Fun(f.x.name.clone());
                if func_call_graph.node_is_in_cycle(&f_node) {
                    return Err(error(&f.span, "'atomic' cannot be used on a recursive function"));
                }
            }
        }
        let qid_map = RefCell::new(HashMap::new());

        let datatype_graph = crate::recursive_types::build_datatype_graph(krate);

        Ok(GlobalCtx {
            chosen_triggers,
            datatypes: Arc::new(datatypes),
            fun_bounds: Arc::new(fun_bounds),
            no_span,
            func_call_graph: Arc::new(func_call_graph),
            func_call_sccs: Arc::new(func_call_sccs),
            datatype_graph: Arc::new(datatype_graph),
            qid_map,
            inferred_modes: Arc::new(inferred_modes),
            rlimit,
            interpreter_log,
            vstd_crate_name,
            arch,
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
            func_call_sccs: self.func_call_sccs.clone(),
            qid_map,
            inferred_modes: self.inferred_modes.clone(),
            rlimit: self.rlimit,
            interpreter_log,
            vstd_crate_name: self.vstd_crate_name.clone(),
            arch: self.arch,
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
}

impl Ctx {
    pub fn new(
        krate: &Krate,
        global: GlobalCtx,
        module: Path,
        mono_types: Vec<MonoTyp>,
        lambda_types: Vec<usize>,
        bound_traits: HashSet<Path>,
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
        let quantifier_count = Cell::new(0);
        let string_hashes = RefCell::new(HashMap::new());
        Ok(Ctx {
            module,
            datatype_is_transparent,
            datatypes_with_invariant,
            mono_types,
            lambda_types,
            bound_traits,
            functions,
            func_map,
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
        for function in &self.functions {
            match (function.x.mode, function.x.body.as_ref()) {
                (Mode::Spec, Some(_)) => {
                    let id = crate::def::prefix_fuel_id(&fun_to_air_ident(&function.x.name));
                    ids.push(air::ast_util::ident_var(&id));
                    let typ_fuel_id = str_typ(&FUEL_ID);
                    let decl = Arc::new(DeclX::Const(id, typ_fuel_id));
                    commands.push(Arc::new(CommandX::Global(decl)));
                }
                _ => {}
            }
        }
        let distinct = Arc::new(air::ast::ExprX::Multi(MultiOp::Distinct, Arc::new(ids)));
        let decl = Arc::new(DeclX::Axiom(distinct));
        commands.push(Arc::new(CommandX::Global(decl)));
        Arc::new(commands)
    }
}
