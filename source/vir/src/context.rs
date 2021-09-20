use crate::ast::{Function, Krate, Mode, Path, Variants, VirErr};
use crate::def::FUEL_ID;
use crate::scc::Graph;
use crate::sst_to_air::path_to_air_ident;
use air::ast::{Command, CommandX, Commands, DeclX, MultiOp, Span};
use air::ast_util::str_typ;
use std::collections::HashMap;
use std::sync::Arc;

pub struct Ctx {
    pub(crate) datatypes: HashMap<Path, Variants>,
    pub(crate) functions: Vec<Function>,
    pub(crate) func_map: HashMap<Path, Function>,
    pub(crate) func_call_graph: Graph<Path>,
    pub(crate) chosen_triggers: std::cell::RefCell<Vec<(Span, Vec<Vec<String>>)>>, // diagnostics
    pub(crate) debug: bool,
}

impl Ctx {
    pub fn new(krate: &Krate, debug: bool) -> Result<Self, VirErr> {
        let datatypes = krate
            .datatypes
            .iter()
            .map(|d| (d.x.path.clone(), d.x.variants.clone()))
            .collect::<HashMap<_, _>>();
        let mut functions: Vec<Function> = Vec::new();
        let mut func_map: HashMap<Path, Function> = HashMap::new();
        let mut func_call_graph: Graph<Path> = Graph::new();
        for function in krate.functions.iter() {
            func_map.insert(function.x.path.clone(), function.clone());
            crate::recursion::expand_call_graph(&mut func_call_graph, function)?;
            functions.push(function.clone());
        }
        func_call_graph.compute_sccs();
        let chosen_triggers: std::cell::RefCell<Vec<(Span, Vec<Vec<String>>)>> =
            std::cell::RefCell::new(Vec::new());
        Ok(Ctx { datatypes, functions, func_map, func_call_graph, chosen_triggers, debug })
    }

    pub fn prelude(&self) -> Commands {
        let nodes = crate::prelude::prelude_nodes();
        air::parser::nodes_to_commands(&nodes).expect("internal error: malformed prelude")
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

    // Report chosen triggers as strings for printing diagnostics
    pub fn get_chosen_triggers(&self) -> Vec<(Span, Vec<Vec<String>>)> {
        self.chosen_triggers.borrow().clone()
    }
}
