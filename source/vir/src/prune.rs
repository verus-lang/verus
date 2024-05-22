/// 1) Optimize generated SMT by pruning unreachable declarations and definitions.
///    This is strictly an optimization; it should not affect the SMT validity.
/// 2) Also remove any broadcast_forall from any modules that are unreachable
///    from this module.  This could, in principle, result in incompleteness.
/// 3) Also compute names for abstract datatype sorts for the module,
///    since we're traversing the module-visible datatypes anyway.
use crate::ast::{
    AssocTypeImpl, AssocTypeImplX, AutospecUsage, CallTarget, Datatype, Expr, ExprX, Fun, Function,
    FunctionKind, Ident, Krate, KrateX, Mode, Module, ModuleX, Path, RevealGroup, Stmt, Trait,
    TraitX, Typ, TypX,
};
use crate::ast_util::{is_visible_to, is_visible_to_of_owner};
use crate::ast_visitor::VisitorScopeMap;
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::{array_index_fun, fn_inv_name, fn_namespace_name, Spanned};
use crate::poly::MonoTyp;
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
// Overapproximation of TypX, used to overapproximate the reached types
// (it's ok if we fail to prune away some types)
// For example, if we reach Datatype("D"), and D is generic,
// we reach D applied to all possible type arguments.
enum ReachedType {
    None,
    Bool,
    Int(crate::ast::IntRange),
    Lambda(usize),
    Datatype(Path),
    StrSlice,
    Primitive,
}

// Group all AssocTypeImpls with the same (ReachedType(self_typ), (trait_path, name)):
type AssocTypeGroup = (ReachedType, (Path, Ident));

type TraitName = Path;
type ImplName = Path;

#[derive(Debug)]
struct TraitImpl {
    // For an impl "...T'(...t'...)... ==> trait T(...t...)",
    // list all traits T' and types t' in the bounds:
    bound_traits: Vec<TraitName>,
    bound_types: Vec<ReachedType>,
    // list T and all t:
    trait_name: TraitName,
    trait_typ_args: Vec<ReachedType>,
}

struct Ctxt {
    module: Path,
    function_map: HashMap<Fun, Function>,
    reveal_group_map: HashMap<Fun, RevealGroup>,
    datatype_map: HashMap<Path, Datatype>,
    // For an impl "bounds ==> trait T(...t...)", point T to impl:
    trait_to_trait_impls: HashMap<TraitName, Vec<ImplName>>,
    // For an impl "bounds ==> trait T(...t...)", point t to impl:
    typ_to_trait_impls: HashMap<ReachedType, Vec<ImplName>>,
    trait_impl_map: HashMap<ImplName, TraitImpl>,
    assoc_type_impl_map: HashMap<AssocTypeGroup, Vec<AssocTypeImpl>>,
    // Map (D, T.f) -> D.f if D implements T.f:
    method_map: HashMap<(ReachedType, Fun), Vec<Fun>>,
    all_functions_in_each_module: HashMap<Path, Vec<Fun>>,
    all_reveal_groups_in_each_module: HashMap<Path, Vec<Fun>>,
    vstd_crate_name: Ident,
}

#[derive(Default)]
struct State {
    reached_functions: HashSet<Fun>,
    reached_types: HashSet<ReachedType>,
    reached_bound_traits: HashSet<TraitName>,
    reached_trait_impls: HashSet<ImplName>,
    reached_assoc_type_decls: HashSet<(Path, Ident)>,
    reached_assoc_type_impls: HashSet<AssocTypeGroup>,
    reached_modules: HashSet<Path>,
    worklist_functions: Vec<Fun>,
    worklist_reveal_groups: Vec<Fun>,
    worklist_types: Vec<ReachedType>,
    worklist_bound_traits: Vec<TraitName>,
    worklist_trait_impls: Vec<ImplName>,
    worklist_assoc_type_decls: Vec<(Path, Ident)>,
    worklist_assoc_type_impls: Vec<AssocTypeGroup>,
    worklist_modules: Vec<Path>,
    mono_abstract_datatypes: HashSet<MonoTyp>,
    lambda_types: HashSet<usize>,
    fndef_types: HashSet<Fun>,
}

fn typ_to_reached_type(typ: &Typ) -> ReachedType {
    match &**typ {
        TypX::Bool => ReachedType::Bool,
        TypX::Int(range) => ReachedType::Int(*range),
        TypX::Tuple(_) => panic!("unexpected TypX::Tuple"),
        TypX::Lambda(ts, _) => ReachedType::Lambda(ts.len()),
        TypX::AnonymousClosure(..) => panic!("unexpected TypX::AnonymousClosure"),
        TypX::Datatype(path, _, _) => ReachedType::Datatype(path.clone()),
        TypX::FnDef(..) => ReachedType::None,
        TypX::Decorate(_, t) => typ_to_reached_type(t),
        TypX::Boxed(t) => typ_to_reached_type(t),
        TypX::TypParam(_) => ReachedType::None,
        TypX::Projection { trait_typ_args, .. } => typ_to_reached_type(&trait_typ_args[0]),
        TypX::TypeId => ReachedType::None,
        TypX::ConstInt(_) => ReachedType::None,
        TypX::Air(_) => panic!("unexpected TypX::Air"),
        TypX::StrSlice => ReachedType::StrSlice,
        TypX::Primitive(_, _) => ReachedType::Primitive,
    }
}

fn record_datatype(ctxt: &Ctxt, state: &mut State, typ: &Typ, path: &Path) {
    if let Some(d) = ctxt.datatype_map.get(path) {
        let is_vis = is_visible_to(&d.x.visibility, &ctxt.module);
        let is_transparent = is_datatype_transparent(&ctxt.module, &d);
        if is_vis && !is_transparent {
            if let Some(monotyp) = crate::poly::typ_as_mono(typ) {
                state.mono_abstract_datatypes.insert(monotyp);
            }
        }
    }
}

fn reach<A: std::hash::Hash + std::cmp::Eq + Clone>(
    reached: &mut HashSet<A>,
    worklist: &mut Vec<A>,
    id: &A,
) {
    if !reached.contains(id) {
        reached.insert(id.clone());
        worklist.push(id.clone());
    }
}

fn reach_function(ctxt: &Ctxt, state: &mut State, name: &Fun) {
    if ctxt.function_map.contains_key(name) {
        reach(&mut state.reached_functions, &mut state.worklist_functions, name);
    }
    if ctxt.reveal_group_map.contains_key(name) {
        reach(&mut state.reached_functions, &mut state.worklist_reveal_groups, name);
    }
}

fn reach_reveal_group(ctxt: &Ctxt, state: &mut State, name: &Fun) {
    let group = &ctxt.reveal_group_map[name];
    if let Some(module_path) = &group.x.owning_module {
        if group.x.prune_unless_this_module_is_used {
            // We only reach into a prune_unless_this_module_is_used group when its module is reached
            if !state.reached_modules.contains(module_path) {
                return;
            }
        } else {
            reach(&mut state.reached_modules, &mut state.worklist_modules, module_path);
        }
    }
    for member in group.x.members.iter() {
        reach_function(ctxt, state, member);
    }
}

fn reach_bound_trait(_ctxt: &Ctxt, state: &mut State, name: &TraitName) {
    reach(&mut state.reached_bound_traits, &mut state.worklist_bound_traits, name);
}

fn reach_trait_impl(ctxt: &Ctxt, state: &mut State, imp: &ImplName) {
    if let Some(trait_impl) = ctxt.trait_impl_map.get(imp) {
        // We only reach the impl "bounds ==> trait T(...t...)" when all of T and t have been reached.
        // Otherwise, we consider the impl irrelevant.
        for t in &trait_impl.trait_typ_args {
            if *t != ReachedType::None && !state.reached_types.contains(t) {
                return;
            }
        }
        if state.reached_bound_traits.contains(&trait_impl.trait_name) {
            reach(&mut state.reached_trait_impls, &mut state.worklist_trait_impls, imp);
        }
    }
}

fn reach_assoc_type_decl(_ctxt: &Ctxt, state: &mut State, name: &(Path, Ident)) {
    reach(&mut state.reached_assoc_type_decls, &mut state.worklist_assoc_type_decls, name);
}

fn reach_assoc_type_impl(ctxt: &Ctxt, state: &mut State, name: &AssocTypeGroup) {
    if ctxt.assoc_type_impl_map.contains_key(name) {
        reach(&mut state.reached_assoc_type_impls, &mut state.worklist_assoc_type_impls, name);
    }
}

fn reach_type(ctxt: &Ctxt, state: &mut State, typ: &ReachedType) {
    match typ {
        ReachedType::Datatype(path) => {
            if ctxt.datatype_map.contains_key(path) {
                reach(&mut state.reached_types, &mut state.worklist_types, typ);
            }
        }
        _ => {
            reach(&mut state.reached_types, &mut state.worklist_types, typ);
        }
    }
}

// shallowly reach typ (the AST visitor takes care of recursing through typ)
fn reach_typ(ctxt: &Ctxt, state: &mut State, typ: &Typ) {
    match &**typ {
        TypX::Bool
        | TypX::Int(_)
        | TypX::Lambda(..)
        | TypX::Datatype(..)
        | TypX::StrSlice
        | TypX::Primitive(..) => {
            reach_type(ctxt, state, &typ_to_reached_type(typ));
        }
        TypX::Tuple(_) | TypX::AnonymousClosure(..) | TypX::Air(_) => {
            panic!("unexpected TypX")
        }
        TypX::Decorate(_, _t) | TypX::Boxed(_t) => {} // let visitor handle _t
        TypX::TypParam(_) | TypX::TypeId | TypX::ConstInt(_) => {}
        TypX::Projection { trait_typ_args: _, trait_path, name, .. } => {
            reach_assoc_type_decl(ctxt, state, &(trait_path.clone(), name.clone()));
            // let visitor handle self_typ, trait_typ_args
        }
        TypX::FnDef(fun, _typs, res_fun_opt) => {
            state.fndef_types.insert(fun.clone());
            reach_function(ctxt, state, fun);

            if let Some(res_fun) = res_fun_opt {
                state.fndef_types.insert(res_fun.clone());
                reach_function(ctxt, state, res_fun);
            }
        }
    }
}

fn reached_methods<'a, 'b, I>(ctxt: &Ctxt, iter: I) -> Vec<Fun>
where
    I: Iterator<Item = (&'a ReachedType, &'b Fun)>,
{
    // If:
    // - we reach both D and T.f
    // - and D implements T.f with D.f
    // add D.f
    let mut method_impls: Vec<Fun> = Vec::new();
    for (self_typ, function) in iter {
        if let Some(ms) = ctxt.method_map.get(&(self_typ.clone(), function.clone())) {
            for method_impl in ms {
                method_impls.push(method_impl.clone());
            }
        }
    }
    method_impls
}

fn reach_methods(ctxt: &Ctxt, state: &mut State, method_impls: Vec<Fun>) {
    for method_impl in &method_impls {
        reach_function(ctxt, state, method_impl);
    }
}

fn traverse_reachable(ctxt: &Ctxt, state: &mut State) {
    loop {
        let ft = |state: &mut State, t: &Typ| {
            reach_typ(ctxt, state, t);
            match &**t {
                TypX::Datatype(path, _, _) => record_datatype(ctxt, state, t, path),
                TypX::Primitive(_, _) => {
                    if let Some(monotyp) = crate::poly::typ_as_mono(t) {
                        state.mono_abstract_datatypes.insert(monotyp);
                    }
                }
                _ => {}
            }
            Ok(t.clone())
        };
        if let Some(f) = state.worklist_functions.pop() {
            let function = &ctxt.function_map[&f];
            if let Some(module_path) = &function.x.owning_module {
                reach(&mut state.reached_modules, &mut state.worklist_modules, module_path);
            }
            if let FunctionKind::TraitMethodImpl { method, .. } = &function.x.kind {
                reach_function(ctxt, state, method);
            }
            for bound in function.x.typ_bounds.iter() {
                // note: the types in the bounds are handled below by map_function_visitor_env
                let path = match &**bound {
                    crate::ast::GenericBoundX::Trait(path, _) => path,
                    crate::ast::GenericBoundX::TypEquality(path, _, name, _) => {
                        reach_assoc_type_decl(ctxt, state, &(path.clone(), name.clone()));
                        path
                    }
                    crate::ast::GenericBoundX::ConstTyp(_, _) => {
                        continue;
                    }
                };
                if function.x.mode == crate::ast::Mode::Spec || function.x.attrs.broadcast_forall {
                    reach_bound_trait(ctxt, state, path);
                }
            }
            let fe = |state: &mut State, _: &mut VisitorScopeMap, e: &Expr| {
                // note: the visitor automatically reaches e.typ
                match &e.x {
                    ExprX::Call(CallTarget::Fun(kind, name, _, _impl_paths, autospec), _) => {
                        // REVIEW: maybe we can be more precise if we use impl_paths here
                        assert!(*autospec == AutospecUsage::Final);
                        reach_function(ctxt, state, name);
                        if let crate::ast::CallTargetKind::DynamicResolved { resolved, .. } = kind {
                            reach_function(ctxt, state, resolved);
                        }
                    }
                    ExprX::ArrayLiteral(..) => {
                        reach_function(ctxt, state, &array_index_fun(&ctxt.vstd_crate_name));
                    }
                    ExprX::OpenInvariant(_, _, _, atomicity) => {
                        // SST -> AIR conversion for OpenInvariant may introduce
                        // references to these particular names.
                        reach_function(
                            ctxt,
                            state,
                            &fn_inv_name(&ctxt.vstd_crate_name, *atomicity),
                        );
                        reach_function(
                            ctxt,
                            state,
                            &fn_namespace_name(&ctxt.vstd_crate_name, *atomicity),
                        );
                    }
                    ExprX::Unary(crate::ast::UnaryOp::InferSpecForLoopIter { .. }, _) => {
                        let t = ReachedType::Datatype(crate::def::option_type_path());
                        reach_type(ctxt, state, &t);
                    }
                    _ => {}
                }
                Ok(e.clone())
            };
            let fs = |_: &mut State, _: &mut VisitorScopeMap, s: &Stmt| Ok(vec![s.clone()]);
            let mut map: VisitorScopeMap = ScopeMap::new();
            crate::ast_visitor::map_function_visitor_env(&function, &mut map, state, &fe, &fs, &ft)
                .unwrap();
            let methods = reached_methods(ctxt, state.reached_types.iter().map(|t| (t, &f)));
            reach_methods(ctxt, state, methods);
            continue;
        }
        if let Some(f) = state.worklist_reveal_groups.pop() {
            reach_reveal_group(ctxt, state, &f);
            continue;
        }
        if let Some(t) = state.worklist_types.pop() {
            match &t {
                ReachedType::Datatype(path) => {
                    let datatype = &ctxt.datatype_map[path];
                    if let Some(module_path) = &datatype.x.owning_module {
                        reach(&mut state.reached_modules, &mut state.worklist_modules, module_path);
                    }
                    crate::ast_visitor::map_datatype_visitor_env(&datatype, state, &ft).unwrap();
                }
                ReachedType::Lambda(arity) => {
                    state.lambda_types.insert(*arity);
                }
                ReachedType::StrSlice => {
                    let path = crate::def::strslice_defn_path(&ctxt.vstd_crate_name);
                    let module_path = path.pop_segment();
                    reach(&mut state.reached_modules, &mut state.worklist_modules, &module_path);
                }
                _ => {}
            }
            if let Some(imps) = ctxt.typ_to_trait_impls.get(&t) {
                for imp in imps {
                    reach_trait_impl(ctxt, state, imp);
                }
            }
            let methods = reached_methods(ctxt, state.reached_functions.iter().map(|f| (&t, f)));
            reach_methods(ctxt, state, methods);
            let assoc_decls: Vec<(Path, Ident)> =
                state.reached_assoc_type_decls.iter().cloned().collect();
            for a in assoc_decls {
                reach_assoc_type_impl(ctxt, state, &(t.clone(), a.clone()));
            }
            continue;
        }
        if let Some(b) = state.worklist_bound_traits.pop() {
            if let Some(impls) = ctxt.trait_to_trait_impls.get(&b) {
                for imp in impls {
                    reach_trait_impl(ctxt, state, imp);
                }
            }
        }
        if let Some(i) = state.worklist_trait_impls.pop() {
            if let Some(trait_impl) = ctxt.trait_impl_map.get(&i) {
                for bound_trait in &trait_impl.bound_traits {
                    reach_bound_trait(ctxt, state, bound_trait);
                }
                for bound_type in &trait_impl.bound_types {
                    reach_type(ctxt, state, bound_type);
                }
            }
        }
        if let Some(a) = state.worklist_assoc_type_decls.pop() {
            let typs: Vec<ReachedType> = state.reached_types.iter().cloned().collect();
            for t in typs {
                reach_assoc_type_impl(ctxt, state, &(t.clone(), a.clone()));
            }
            continue;
        }
        if let Some(assoc_group) = state.worklist_assoc_type_impls.pop() {
            if let Some(assoc_impls) = ctxt.assoc_type_impl_map.get(&assoc_group) {
                for assoc_impl in assoc_impls {
                    crate::ast_visitor::map_assoc_type_impl_visitor_env(&assoc_impl, state, &ft)
                        .unwrap();
                }
            }
            continue;
        }
        if let Some(m) = state.worklist_modules.pop() {
            if let Some(fs) = ctxt.all_functions_in_each_module.get(&m) {
                for f in fs {
                    let function = &ctxt.function_map[f];
                    if function.x.attrs.broadcast_forall && function.x.body.is_none() {
                        // If we reach m, we reach all broadcast_forall functions in m
                        // TODO: remove this and rely on explicit reaching of broadcast_forall
                        // (also remove all_functions_in_each_module)
                        reach_function(ctxt, state, f);
                    }
                }
            }
            if let Some(fs) = ctxt.all_reveal_groups_in_each_module.get(&m) {
                for f in fs {
                    if state.reached_functions.contains(f) {
                        // revisit group to handle prune_unless_this_module_is_used
                        reach_reveal_group(ctxt, state, f);
                    }
                }
            }
            continue;
        }
        break;
    }
}

impl TraitX {
    fn prune_name(&self, name: &Ident) -> (Path, Ident) {
        (self.name.clone(), name.clone())
    }
}

impl AssocTypeImplX {
    fn prune_name(&self) -> AssocTypeGroup {
        let self_typ = &self.trait_typ_args[0];
        (typ_to_reached_type(self_typ), (self.trait_path.clone(), self.name.clone()))
    }
}

fn overapproximate_revealed_functions(
    revealed_functions: &mut HashSet<Fun>,
    reveal_groups: &Vec<RevealGroup>,
) {
    // REVIEW: this is an unnecessary overapproximation;
    // we could be more precise in handling whether reveal_groups recursively reach and reveal
    // opaque functions (depending on prune_unless_this_module_is_used),
    // but it would require refactoring the way we decide to keep or erase opaque function bodies,
    // which doesn't seem worth it now to optimize a feature that isn't really used yet.
    // So we just make an overapproximation that ignores prune_unless_this_module_is_used.
    // (As a result, we might unnecessarily include the body of an opaque function even if
    // we only need the opaque function's signature.)
    let mut reveal_group_map: HashMap<Fun, RevealGroup> = HashMap::new();
    for f in reveal_groups {
        reveal_group_map.insert(f.x.name.clone(), f.clone());
    }
    let mut worklist: Vec<Fun> =
        revealed_functions.iter().filter(|f| reveal_group_map.contains_key(*f)).cloned().collect();
    while let Some(f) = worklist.pop() {
        let group = &reveal_group_map[&f];
        for member in group.x.members.iter() {
            if !revealed_functions.contains(member) {
                revealed_functions.insert(member.clone());
                if reveal_group_map.contains_key(member) {
                    worklist.push(member.clone());
                }
            }
        }
    }
}

pub fn prune_krate_for_module(
    krate: &Krate,
    crate_name: &Ident,
    module: &Path,
    fun: Option<&Fun>,
) -> (Krate, Vec<MonoTyp>, Vec<usize>, HashSet<Path>, Vec<Fun>) {
    let is_root = |function: &Function| match fun {
        Some(f) => &function.x.name == f,
        None => match &function.x.owning_module {
            Some(m) => m == module,
            None => false,
        },
    };

    let mut state: State = Default::default();
    state.reached_modules.insert(module.clone());
    state.worklist_modules.push(module.clone());

    // Collect all functions that our module reveals:
    let this_module_reveals = krate
        .modules
        .iter()
        .find(|m| &m.x.path == module)
        .map(|m| m.x.reveals.clone())
        .expect("module declaration for current module");
    let mut revealed_functions: HashSet<Fun> = HashSet::new();
    for f in &krate.functions {
        if is_root(f) {
            if let Some(body) = &f.x.body {
                crate::ast_visitor::expr_visitor_check::<(), _>(
                    body,
                    &mut |_scope_map, e: &Expr| {
                        match &e.x {
                            ExprX::Fuel(path, fuel, _is_broadcast_use) if *fuel > 0 => {
                                revealed_functions.insert(path.clone());
                            }
                            _ => {}
                        }
                        Ok(())
                    },
                )
                .expect("expr_visitor_check failed unexpectedly");
            }
        }
    }
    for f in this_module_reveals.iter().flat_map(|o| o.x.iter()) {
        revealed_functions.insert(f.clone());
        state.reached_functions.insert(f.clone());
    }
    for group in &krate.reveal_groups {
        if let Some(group_crate) = &group.x.broadcast_use_by_default_when_this_crate_is_imported {
            let is_imported = crate_name != group_crate;
            if is_imported {
                revealed_functions.insert(group.x.name.clone());
            }
        }
    }

    // Collect functions and datatypes,
    // pruning all bodies and variants that are not visible to our module
    let mut functions: Vec<Function> = Vec::new();
    let mut reveal_groups: Vec<RevealGroup> = Vec::new();
    let mut datatypes: Vec<Datatype> = Vec::new();
    let mut traits: Vec<Trait> = Vec::new();
    for f in &krate.reveal_groups {
        if is_visible_to(&f.x.visibility, module) {
            reveal_groups.push(f.clone());
            if revealed_functions.contains(&f.x.name) {
                state.reached_functions.insert(f.x.name.clone());
                state.worklist_reveal_groups.push(f.x.name.clone());
            }
        }
    }
    overapproximate_revealed_functions(&mut revealed_functions, &reveal_groups);
    for f in &krate.functions {
        if is_root(f) {
            // our function
            functions.push(f.clone());
            state.reached_functions.insert(f.x.name.clone());
            state.worklist_functions.push(f.x.name.clone());
            continue;
        }
        // Remove body if any of the following are true:
        // - function is not visible
        // - function is abstract
        // - function is opaque and not revealed
        // - function is exec or proof
        let vis = f.x.visibility.clone();
        let is_vis = is_visible_to(&vis, module);
        let within_module = is_visible_to_of_owner(&f.x.owning_module, module);
        let is_non_opaque =
            if within_module { f.x.fuel > 0 } else { f.x.fuel > 0 && f.x.publish == Some(true) };
        let is_revealed = is_non_opaque || revealed_functions.contains(&f.x.name);
        let is_spec = f.x.mode == Mode::Spec;
        if is_vis && is_revealed && is_spec {
            if !within_module && f.x.publish == Some(false) {
                let mut function = f.x.clone();
                function.fuel = 0;
                functions.push(Spanned::new(f.span.clone(), function));
            } else {
                functions.push(f.clone());
            }
        } else if f.x.body.is_none() {
            functions.push(f.clone());
        } else {
            let mut function = f.x.clone();
            function.body = None;
            functions.push(Spanned::new(f.span.clone(), function));
        }
    }
    for d in &krate.datatypes {
        match &d.x.owning_module {
            Some(path) if path == module => {
                // our datatype
                let t = ReachedType::Datatype(d.x.path.clone());
                state.reached_types.insert(t.clone());
                state.worklist_types.push(t);
            }
            _ => {}
        }
        let is_vis = is_visible_to(&d.x.visibility, module);
        let is_transparent = is_datatype_transparent(module, &d);
        if is_vis {
            if is_transparent {
                datatypes.push(d.clone());
            } else {
                let mut datatype = d.x.clone();
                datatype.variants = Arc::new(vec![]);
                datatypes.push(Spanned::new(d.span.clone(), datatype));
            }
        }
    }

    let mut function_map: HashMap<Fun, Function> = HashMap::new();
    let mut reveal_group_map: HashMap<Fun, RevealGroup> = HashMap::new();
    let mut datatype_map: HashMap<Path, Datatype> = HashMap::new();
    let mut assoc_type_impl_map: HashMap<AssocTypeGroup, Vec<AssocTypeImpl>> = HashMap::new();
    let mut trait_to_trait_impls: HashMap<TraitName, Vec<ImplName>> = HashMap::new();
    let mut typ_to_trait_impls: HashMap<ReachedType, Vec<ImplName>> = HashMap::new();
    let mut trait_impl_map: HashMap<ImplName, TraitImpl> = HashMap::new();
    let mut method_map: HashMap<(ReachedType, Fun), Vec<Fun>> = HashMap::new();
    let mut all_functions_in_each_module: HashMap<Path, Vec<Fun>> = HashMap::new();
    let mut all_reveal_groups_in_each_module: HashMap<Path, Vec<Fun>> = HashMap::new();
    for f in &functions {
        function_map.insert(f.x.name.clone(), f.clone());
        if let FunctionKind::TraitMethodImpl { method, trait_typ_args, .. } = &f.x.kind {
            let self_typ = &trait_typ_args[0];
            let key = (typ_to_reached_type(self_typ), method.clone());
            if !method_map.contains_key(&key) {
                method_map.insert(key.clone(), Vec::new());
            }
            method_map.get_mut(&key).unwrap().push(f.x.name.clone());
        }
        let module = f.x.owning_module.clone().expect("owning_module");
        if !all_functions_in_each_module.contains_key(&module) {
            all_functions_in_each_module.insert(module.clone(), Vec::new());
        }
        all_functions_in_each_module.get_mut(&module).unwrap().push(f.x.name.clone());
    }
    for f in &reveal_groups {
        reveal_group_map.insert(f.x.name.clone(), f.clone());
        let module = f.x.owning_module.clone().expect("owning_module");
        all_reveal_groups_in_each_module
            .entry(module)
            .or_insert_with(|| Vec::new())
            .push(f.x.name.clone());
    }
    for d in &datatypes {
        datatype_map.insert(d.x.path.clone(), d.clone());
    }

    for imp in krate.trait_impls.iter() {
        let mut bound_traits: Vec<TraitName> = Vec::new();
        let mut bound_types: Vec<ReachedType> = Vec::new();
        for bound in imp.x.typ_bounds.iter() {
            match &**bound {
                crate::ast::GenericBoundX::Trait(path, typ_args) => {
                    bound_traits.push(path.clone());
                    for t in typ_args.iter() {
                        bound_types.push(typ_to_reached_type(t));
                    }
                }
                crate::ast::GenericBoundX::TypEquality(path, typ_args, _name, typ) => {
                    bound_traits.push(path.clone());
                    for t in typ_args.iter() {
                        bound_types.push(typ_to_reached_type(t));
                    }
                    bound_types.push(typ_to_reached_type(typ));
                }
                crate::ast::GenericBoundX::ConstTyp(t, s) => {
                    bound_types.push(typ_to_reached_type(t));
                    bound_types.push(typ_to_reached_type(s));
                }
            }
        }
        let trait_impl = TraitImpl {
            bound_traits,
            bound_types,
            trait_name: imp.x.trait_path.clone(),
            trait_typ_args: imp.x.trait_typ_args.iter().map(typ_to_reached_type).collect(),
        };
        if !trait_to_trait_impls.contains_key(&imp.x.trait_path) {
            trait_to_trait_impls.insert(imp.x.trait_path.clone(), Vec::new());
        }
        trait_to_trait_impls.get_mut(&imp.x.trait_path).unwrap().push(imp.x.impl_path.clone());
        for t in &trait_impl.trait_typ_args {
            if !typ_to_trait_impls.contains_key(t) {
                typ_to_trait_impls.insert(t.clone(), Vec::new());
            }
            typ_to_trait_impls.get_mut(&t).unwrap().push(imp.x.impl_path.clone());
        }
        assert!(!trait_impl_map.contains_key(&imp.x.impl_path));
        trait_impl_map.insert(imp.x.impl_path.clone(), trait_impl);
    }

    for a in &krate.assoc_type_impls {
        let key = a.x.prune_name();
        if !assoc_type_impl_map.contains_key(&key) {
            assoc_type_impl_map.insert(key.clone(), Vec::new());
        }
        assoc_type_impl_map.get_mut(&key).unwrap().push(a.clone());
    }
    let vstd_crate_name = Arc::new(crate::def::VERUSLIB.to_string());
    let ctxt = Ctxt {
        module: module.clone(),
        function_map,
        reveal_group_map,
        datatype_map,
        trait_to_trait_impls,
        typ_to_trait_impls,
        trait_impl_map,
        assoc_type_impl_map,
        method_map,
        all_functions_in_each_module,
        all_reveal_groups_in_each_module,
        vstd_crate_name,
    };
    traverse_reachable(&ctxt, &mut state);

    for tr in krate.traits.iter() {
        let traitx = tr.x.clone();
        let assoc_typs = traitx
            .assoc_typs
            .iter()
            .filter(|a| state.reached_assoc_type_decls.contains(&traitx.prune_name(a)))
            .cloned()
            .collect();
        let assoc_typs = Arc::new(assoc_typs);
        traits.push(Spanned::new(tr.span.clone(), TraitX { assoc_typs, ..traitx }));
    }

    let modules: Vec<Module> = krate
        .modules
        .iter()
        .map(|mm| {
            mm.map_x(|m| ModuleX {
                path: m.path.clone(),
                reveals: if &m.path == module { m.reveals.clone() } else { None },
            })
        })
        .collect();

    debug_assert!(modules.iter().filter(|m| m.x.reveals.is_some()).count() <= 1);

    let kratex = KrateX {
        functions: functions
            .into_iter()
            .filter(|f| state.reached_functions.contains(&f.x.name))
            .collect(),
        reveal_groups: reveal_groups
            .into_iter()
            .filter(|f| state.reached_functions.contains(&f.x.name))
            .collect(),
        datatypes: datatypes
            .into_iter()
            .filter(|d| state.reached_types.contains(&ReachedType::Datatype(d.x.path.clone())))
            .collect(),
        assoc_type_impls: krate
            .assoc_type_impls
            .iter()
            .filter(|a| state.reached_assoc_type_impls.contains(&a.x.prune_name()))
            .cloned()
            .collect(),
        traits,
        trait_impls: krate
            .trait_impls
            .iter()
            .filter(|i| state.reached_trait_impls.contains(&i.x.impl_path))
            .cloned()
            .collect(),
        modules,
        external_fns: krate.external_fns.clone(),
        external_types: krate.external_types.clone(),
        path_as_rust_names: krate.path_as_rust_names.clone(),
        arch: krate.arch.clone(),
    };
    let mut lambda_types: Vec<usize> = state.lambda_types.into_iter().collect();
    lambda_types.sort();
    let mut fndef_types: Vec<Fun> = state.fndef_types.into_iter().collect();
    fndef_types.sort();
    let mut mono_abstract_datatypes: Vec<MonoTyp> =
        state.mono_abstract_datatypes.into_iter().collect();
    mono_abstract_datatypes.sort();
    let State { reached_bound_traits, .. } = state;
    (Arc::new(kratex), mono_abstract_datatypes, lambda_types, reached_bound_traits, fndef_types)
}
