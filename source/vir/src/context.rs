use crate::ast::{Datatype, Function, IntRange, Krate, Mode, Path, TypX, Variants, VirErr};
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::FUEL_ID;
use crate::scc::Graph;
use crate::sst_to_air::path_to_air_ident;
use air::ast::{Command, CommandX, Commands, DeclX, MultiOp, Span};
use air::ast_util::str_typ;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// Context for across all modules
pub struct GlobalCtx {
    pub(crate) chosen_triggers: std::cell::RefCell<Vec<(Span, Vec<Vec<String>>)>>, // diagnostics
    pub(crate) datatypes: HashMap<Path, Variants>,
    // Used for synthesized AST nodes that have no relation to any location in the original code:
    pub(crate) no_span: Span,
}

// Context for verifying one module
pub struct Ctx {
    pub(crate) module: Path,
    pub(crate) datatypes_with_invariant: HashSet<Path>,
    pub(crate) functions: Vec<Function>,
    pub(crate) func_map: HashMap<Path, Function>,
    pub(crate) func_call_graph: Graph<Path>,
    pub(crate) funcs_with_ensure_predicate: HashSet<Path>,
    pub(crate) debug: bool,
    pub(crate) global: GlobalCtx,
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
fn datatypes_invs(module: &Path, datatypes: &Vec<Datatype>) -> HashSet<Path> {
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
                        TypX::Datatype(field_path, _) => {
                            back_pointers
                                .get_mut(field_path)
                                .expect("datatypes_invs")
                                .insert(container_path.clone());
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
    pub fn new(krate: &Krate, no_span: Span) -> Self {
        let chosen_triggers: std::cell::RefCell<Vec<(Span, Vec<Vec<String>>)>> =
            std::cell::RefCell::new(Vec::new());
        let datatypes: HashMap<Path, Variants> =
            krate.datatypes.iter().map(|d| (d.x.path.clone(), d.x.variants.clone())).collect();
        GlobalCtx { chosen_triggers, datatypes, no_span }
    }

    // Report chosen triggers as strings for printing diagnostics
    pub fn get_chosen_triggers(&self) -> Vec<(Span, Vec<Vec<String>>)> {
        self.chosen_triggers.borrow().clone()
    }
}

impl Ctx {
    pub fn new(
        krate: &Krate,
        global: GlobalCtx,
        module: Path,
        debug: bool,
    ) -> Result<Self, VirErr> {
        let datatypes_with_invariant = datatypes_invs(&module, &krate.datatypes);
        let mut functions: Vec<Function> = Vec::new();
        let mut func_map: HashMap<Path, Function> = HashMap::new();
        let mut func_call_graph: Graph<Path> = Graph::new();
        let funcs_with_ensure_predicate: HashSet<Path> = HashSet::new();
        for function in krate.functions.iter() {
            func_map.insert(function.x.path.clone(), function.clone());
            crate::recursion::expand_call_graph(&mut func_call_graph, function)?;
            functions.push(function.clone());
        }
        func_call_graph.compute_sccs();
        Ok(Ctx {
            module,
            datatypes_with_invariant,
            functions,
            func_map,
            func_call_graph,
            funcs_with_ensure_predicate,
            debug,
            global,
        })
    }

    pub fn free(self) -> GlobalCtx {
        self.global
    }

    pub fn prelude() -> Commands {
        let nodes = crate::prelude::prelude_nodes();
        air::parser::nodes_to_commands(&nodes).expect("internal error: malformed prelude")
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
                    let id = crate::def::prefix_fuel_id(&path_to_air_ident(&function.x.path));
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
