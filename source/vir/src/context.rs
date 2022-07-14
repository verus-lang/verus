use crate::ast::{
    Datatype, Fun, Function, FunctionKind, GenericBound, InferMode, IntRange, Krate, Mode, Path,
    Trait, TypX, Variants, VirErr,
};
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::FUEL_ID;
use crate::poly::MonoTyp;
use crate::recursion::Node;
use crate::scc::Graph;
use crate::sst::BndInfo;
use crate::sst_to_air::fun_to_air_ident;
use crate::util::vec_map;
use air::ast::{Command, CommandX, Commands, DeclX, MultiOp, Span};
use air::ast_util::str_typ;
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub type ChosenTrigger = Vec<(Span, String)>;
#[derive(Debug, Clone)]
pub struct ChosenTriggers {
    pub module: Path,
    pub span: Span,
    pub triggers: Vec<ChosenTrigger>,
    pub low_confidence: bool,
}

// Context for across all modules
pub struct GlobalCtx {
    pub(crate) chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>>, // diagnostics
    pub(crate) datatypes: HashMap<Path, Variants>,
    pub(crate) fun_bounds: HashMap<Fun, Vec<GenericBound>>,
    // Used for synthesized AST nodes that have no relation to any location in the original code:
    pub(crate) no_span: Span,
    pub func_call_graph: Graph<Node>,
    pub func_call_sccs: Vec<Node>,
    // Connects quantifier identifiers to the original expression
    pub qid_map: RefCell<HashMap<String, BndInfo>>,
    pub method_map: HashMap<(Fun, Path), Fun>,
    pub(crate) inferred_modes: HashMap<InferMode, Mode>,
}

// Context for verifying one function
pub struct FunctionCtx {
    // false normally, true if we're just checking recommends
    pub checking_recommends: bool,
    // used to print diagnostics for triggers
    pub module_for_chosen_triggers: Option<Path>,
    // used to create quantifier identifiers
    pub current_fun: Fun,
}

// Context for verifying one module
pub struct Ctx {
    pub(crate) module: Path,
    pub(crate) datatype_is_transparent: HashMap<Path, bool>,
    pub(crate) datatypes_with_invariant: HashSet<Path>,
    pub(crate) mono_abstract_datatypes: Vec<MonoTyp>,
    pub(crate) lambda_types: Vec<usize>,
    pub functions: Vec<Function>,
    pub func_map: HashMap<Fun, Function>,
    // Ensure a unique identifier for each quantifier in a given function
    pub quantifier_count: Cell<u64>,
    pub(crate) funcs_with_ensure_predicate: HashSet<Fun>,
    pub(crate) datatype_map: HashMap<Path, Datatype>,
    pub(crate) trait_map: HashMap<Path, Trait>,
    pub global: GlobalCtx,
    pub fun: Option<FunctionCtx>,
    // proof debug purposes
    pub debug: bool,
    pub expand_flag: bool,
    pub debug_expand_targets: Vec<air::errors::Error>,
}

impl Ctx {
    pub fn checking_recommends(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_recommends: true, .. }) => true,
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

// If a datatype's fields have invariants, the datatype need an invariant
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
                    match &*field.a.0 {
                        // Should be kept in sync with vir::sst_to_air::typ_invariant
                        TypX::Int(IntRange::Int) => {}
                        TypX::Int(_) | TypX::TypParam(_) => {
                            roots.insert(container_path.clone());
                        }
                        TypX::Lambda(..) => {
                            panic!(
                                "not supported: function types in datatype fields (use Map instead)"
                            )
                        }
                        TypX::Datatype(field_path, _) => {
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
                        _ => {}
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
        let mut method_map: HashMap<(Fun, Path), Fun> = HashMap::new();
        for function in krate.functions.iter() {
            if let FunctionKind::TraitMethodImpl { method, datatype, .. } = &function.x.kind {
                let key = (method.clone(), datatype.clone());
                assert!(!method_map.contains_key(&key));
                method_map.insert(key, function.x.name.clone());
            }
        }
        let mut fun_bounds: HashMap<Fun, Vec<GenericBound>> = HashMap::new();
        let mut func_call_graph: Graph<Node> = Graph::new();
        for f in &krate.functions {
            let bounds = vec_map(&f.x.typ_bounds, |(_, bound)| bound.clone());
            fun_bounds.insert(f.x.name.clone(), bounds);
            func_call_graph.add_node(Node::Fun(f.x.name.clone()));
            crate::recursion::expand_call_graph(&func_map, &method_map, &mut func_call_graph, f)?;
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
                        return Err(air::errors::error(
                            "found cyclic dependency in decreases_by function",
                            &f.span,
                        )
                        .secondary_span(&g.unwrap().span));
                    }
                }
            }
        }
        let qid_map = RefCell::new(HashMap::new());

        Ok(GlobalCtx {
            chosen_triggers,
            datatypes,
            fun_bounds,
            no_span,
            func_call_graph,
            func_call_sccs,
            qid_map,
            method_map,
            inferred_modes,
        })
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
        mono_abstract_datatypes: Vec<MonoTyp>,
        lambda_types: Vec<usize>,
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
        Ok(Ctx {
            module,
            datatype_is_transparent,
            datatypes_with_invariant,
            mono_abstract_datatypes,
            lambda_types,
            functions,
            func_map,
            quantifier_count,
            funcs_with_ensure_predicate,
            datatype_map,
            trait_map,
            fun: None,
            global,
            debug,
            expand_flag: false,
            debug_expand_targets: vec![],
        })
    }

    pub fn free(self) -> GlobalCtx {
        self.global
    }

    pub fn prelude() -> Commands {
        let nodes = crate::prelude::prelude_nodes();
        air::parser::Parser::new()
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
