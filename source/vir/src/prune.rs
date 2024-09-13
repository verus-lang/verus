/// 1) Optimize generated SMT by pruning unreachable declarations and definitions.
///    This is strictly an optimization; it should not affect the SMT validity.
/// 2) Also compute names for abstract datatype sorts for the module,
///    since we're traversing the module-visible datatypes anyway.
use crate::ast::{
    AssocTypeImpl, AssocTypeImplX, AutospecUsage, CallTarget, Datatype, Expr, ExprX, Fun, Function,
    FunctionKind, Ident, Krate, KrateX, Mode, Module, ModuleX, Path, RevealGroup, Stmt, Trait,
    TraitX, Typ, TypX,
};
use crate::ast_util::{is_visible_to, is_visible_to_of_owner, is_visible_to_or_true};
use crate::ast_visitor::{VisitorControlFlow, VisitorScopeMap};
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::{fn_inv_name, fn_namespace_name, Spanned};
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
    SpecFn(usize),
    Datatype(Path),
    StrSlice,
    Array,
    Primitive,
}

// Group all AssocTypeImpls with the same (ReachedType(self_typ), (trait_path, name)):
type AssocTypeGroup = (ReachedType, (Path, Ident));

type TraitName = Path;
type ImplName = Path;

#[derive(Debug)]
struct ReachTraitImpl {
    trait_impl: crate::ast::TraitImpl,
    // For an impl "...T'(...t'...)... ==> trait T(...t...)",
    // list all traits T' and types t' in the bounds:
    bound_traits: Vec<TraitName>,
    bound_types: Vec<ReachedType>,
    // list all t:
    trait_typ_args: Vec<ReachedType>,
}

#[derive(Debug)]
struct ReachBroadcastFunction {
    // For each trigger, keep a Vec<Fun> that contains every Fun that must be reached to
    // activate the trigger:
    reach_triggers: Vec<(Vec<Fun>, Vec<ReachedType>)>,
}

struct Ctxt {
    module: Option<Path>,
    function_map: HashMap<Fun, Function>,
    reveal_group_map: HashMap<Fun, RevealGroup>,
    datatype_map: HashMap<Path, Datatype>,
    trait_map: HashMap<Path, Trait>,
    // For an impl "bounds ==> trait T(...t...)", point T to impl:
    trait_to_trait_impls: HashMap<TraitName, Vec<ImplName>>,
    // For an impl "bounds ==> trait T(...t...)", point t to impl:
    typ_to_trait_impls: HashMap<ReachedType, Vec<ImplName>>,
    trait_impl_map: HashMap<ImplName, ReachTraitImpl>,
    assoc_type_impl_map: HashMap<AssocTypeGroup, Vec<AssocTypeImpl>>,
    // Map (D, T.f) -> D.f if D implements T.f:
    method_map: HashMap<(ReachedType, Fun), Vec<Fun>>,
    // For a broadcast function f with triggers containing functions f0..fn, point f0..fn to f:
    fun_to_trigger_broadcasts: HashMap<Fun, Vec<Fun>>,
    typ_to_trigger_broadcasts: HashMap<ReachedType, Vec<Fun>>,
    // Map each revealed broadcast function f to its ReachBroadcastFunction
    fun_revealed_broadcast_map: HashMap<Fun, ReachBroadcastFunction>,
    vstd_crate_name: Ident,
    assert_by_compute: bool,
    assert_by_compute_seq_funs: Vec<Fun>,
}

#[derive(Default)]
struct State {
    reached_functions: HashSet<Fun>,
    reached_types: HashSet<ReachedType>,
    reached_bound_traits: HashSet<TraitName>,
    reached_trait_impls: HashSet<ImplName>,
    reached_assoc_type_decls: HashSet<(Path, Ident)>,
    reached_assoc_type_impls: HashSet<AssocTypeGroup>,
    worklist_functions: Vec<Fun>,
    worklist_reveal_groups: Vec<Fun>,
    worklist_types: Vec<ReachedType>,
    worklist_bound_traits: Vec<TraitName>,
    worklist_trait_impls: Vec<ImplName>,
    worklist_assoc_type_decls: Vec<(Path, Ident)>,
    worklist_assoc_type_impls: Vec<AssocTypeGroup>,
    mono_abstract_datatypes: Option<HashSet<MonoTyp>>,
    spec_fn_types: HashSet<usize>,
    uses_array: bool,
    fndef_types: HashSet<Fun>,
    // broadcast functions that are also defined or called normally
    // (not just used for the broadcast)
    broadcast_functions_fully_reached: HashSet<Fun>,
}

fn typ_to_reached_type(typ: &Typ) -> ReachedType {
    use crate::ast::Primitive;
    match &**typ {
        TypX::Bool => ReachedType::Bool,
        TypX::Int(range) => ReachedType::Int(*range),
        TypX::Tuple(_) => ReachedType::None,
        TypX::SpecFn(ts, _) => ReachedType::SpecFn(ts.len()),
        TypX::AnonymousClosure(..) => ReachedType::None,
        TypX::Datatype(path, _, _) => ReachedType::Datatype(path.clone()),
        TypX::FnDef(..) => ReachedType::None,
        TypX::Decorate(_, _, t) => typ_to_reached_type(t),
        TypX::Boxed(t) => typ_to_reached_type(t),
        TypX::TypParam(_) => ReachedType::None,
        TypX::Projection { trait_typ_args, .. } => typ_to_reached_type(&trait_typ_args[0]),
        TypX::TypeId => ReachedType::None,
        TypX::ConstInt(_) => ReachedType::None,
        TypX::Air(_) => panic!("unexpected TypX::Air"),
        TypX::Primitive(Primitive::StrSlice, _) => ReachedType::StrSlice,
        TypX::Primitive(Primitive::Array, _) => ReachedType::Array,
        TypX::Primitive(Primitive::Slice | Primitive::Ptr | Primitive::Global, _) => {
            ReachedType::Primitive
        }
    }
}

fn record_datatype(ctxt: &Ctxt, state: &mut State, typ: &Typ, path: &Path) {
    let module = if let Some(module) = &ctxt.module {
        module
    } else {
        return;
    };
    if let Some(mono_abstract_datatypes) = &mut state.mono_abstract_datatypes {
        if let Some(d) = ctxt.datatype_map.get(path) {
            let is_vis = is_visible_to(&d.x.visibility, module);
            let is_transparent = is_datatype_transparent(module, &d);
            if is_vis && !is_transparent {
                if let Some(monotyp) = crate::poly::typ_as_mono(typ) {
                    mono_abstract_datatypes.insert(monotyp);
                }
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

fn reach_function_inner(ctxt: &Ctxt, state: &mut State, name: &Fun, fully_reach: bool) {
    if fully_reach {
        state.broadcast_functions_fully_reached.insert(name.clone());
    }
    if ctxt.function_map.contains_key(name) {
        reach(&mut state.reached_functions, &mut state.worklist_functions, name);
    }
    if ctxt.reveal_group_map.contains_key(name) {
        reach(&mut state.reached_functions, &mut state.worklist_reveal_groups, name);
    }
}

fn reach_function(ctxt: &Ctxt, state: &mut State, name: &Fun) {
    reach_function_inner(ctxt, state, name, true);
}

fn reach_function_via_reveal(ctxt: &Ctxt, state: &mut State, name: &Fun) {
    if let Some(broadcast) = ctxt.fun_revealed_broadcast_map.get(name) {
        // "name" is a revealed broadcast function
        // If any triggers are reachable, reach the function
        if broadcast.reach_triggers.len() == 0 {
            // No triggers, so there's nothing to base pruning on, so we can't prune
            reach_function_inner(ctxt, state, name, false);
        }
        'try_next_trigger: for (trig_funs, trig_typs) in &broadcast.reach_triggers {
            for f in trig_funs {
                if !state.reached_functions.contains(f) {
                    continue 'try_next_trigger;
                }
            }
            for t in trig_typs {
                if !state.reached_types.contains(t) {
                    continue 'try_next_trigger;
                }
            }
            // We found a reachable trigger, so reach the whole broadcast function:
            reach_function_inner(ctxt, state, name, false);
            break;
        }
    } else {
        reach_function(ctxt, state, name);
    }
}

fn reach_reveal_group(ctxt: &Ctxt, state: &mut State, name: &Fun) {
    let group = &ctxt.reveal_group_map[name];
    for member in group.x.members.iter() {
        reach_function_via_reveal(ctxt, state, member);
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
        if state.reached_bound_traits.contains(&trait_impl.trait_impl.x.trait_path) {
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
        TypX::Bool | TypX::Int(_) | TypX::SpecFn(..) | TypX::Datatype(..) | TypX::Primitive(..) => {
            reach_type(ctxt, state, &typ_to_reached_type(typ));
        }
        TypX::Tuple(_) | TypX::AnonymousClosure(..) => {}
        TypX::Air(_) => {
            panic!("unexpected TypX")
        }
        TypX::Decorate(_, _, _t) | TypX::Boxed(_t) => {} // let visitor handle _t
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

fn reach_seq_funs(ctxt: &Ctxt, state: &mut State) {
    assert!(ctxt.assert_by_compute);
    for f in ctxt.assert_by_compute_seq_funs.iter() {
        reach_function(ctxt, state, f);
    }
}

fn traverse_typ(ctxt: &Ctxt, state: &mut State, t: &Typ) {
    reach_typ(ctxt, state, t);
    match &**t {
        TypX::Datatype(path, _, _) => record_datatype(ctxt, state, t, path),
        TypX::Primitive(_, _) => {
            if let Some(mono_abstract_datatypes) = &mut state.mono_abstract_datatypes {
                if let Some(monotyp) = crate::poly::typ_as_mono(t) {
                    mono_abstract_datatypes.insert(monotyp);
                }
            }
        }
        _ => {}
    }
}

fn traverse_generic_bounds(
    ctxt: &Ctxt,
    state: &mut State,
    bounds: &crate::ast::GenericBounds,
    traverse_typs: bool,
) {
    for bound in bounds.iter() {
        // note: the types in the bounds are handled below in traverse_typs
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
        reach_bound_trait(ctxt, state, path);
    }
    if traverse_typs {
        let ft = |state: &mut State, t: &Typ| {
            traverse_typ(ctxt, state, t);
            Ok(t.clone())
        };
        let _ = crate::ast_visitor::map_generic_bounds_visitor(bounds, state, &ft)
            .expect("traverse_typs");
    }
}

fn traverse_reachable(ctxt: &Ctxt, state: &mut State) {
    loop {
        let ft = |state: &mut State, t: &Typ| {
            traverse_typ(ctxt, state, t);
            Ok(t.clone())
        };
        if let Some(f) = state.worklist_functions.pop() {
            let function = &ctxt.function_map[&f];
            if ctxt.module.is_none() {
                if let Some(autospec) = &function.x.attrs.autospec {
                    reach_function(ctxt, state, autospec);
                }
            }
            if let FunctionKind::TraitMethodImpl { method, .. } = &function.x.kind {
                reach_function(ctxt, state, method);
            }
            if let Some(f_trigs) = ctxt.fun_to_trigger_broadcasts.get(&f) {
                for f_trig in f_trigs {
                    reach_function_via_reveal(ctxt, state, f_trig);
                }
            }
            if ctxt.assert_by_compute && crate::interpreter::is_sequence_fn(&f).is_some() {
                reach_seq_funs(ctxt, state);
            }
            // note: the types in typ_bounds are handled below by map_function_visitor_env
            traverse_generic_bounds(ctxt, state, &function.x.typ_bounds, false);
            let fe = |state: &mut State, _: &mut VisitorScopeMap, e: &Expr| {
                // note: the visitor automatically reaches e.typ
                match &e.x {
                    ExprX::ConstVar(name, _) => {
                        assert!(ctxt.module.is_none());
                        reach_function(ctxt, state, name);
                    }
                    ExprX::Call(CallTarget::Fun(kind, name, _, _impl_paths, autospec), _) => {
                        // REVIEW: maybe we can be more precise if we use impl_paths here
                        assert!(ctxt.module.is_none() || *autospec == AutospecUsage::Final);
                        reach_function(ctxt, state, name);
                        if let crate::ast::CallTargetKind::DynamicResolved { resolved, .. } = kind {
                            reach_function(ctxt, state, resolved);
                        }
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
                    ExprX::Fuel(fueled_f, _, is_broadcast_use) if *is_broadcast_use => {
                        reach_function(ctxt, state, fueled_f);
                    }
                    ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: _, expr: _, fun } => {
                        reach_function(ctxt, state, fun);
                    }
                    ExprX::ArrayLiteral(..) if ctxt.assert_by_compute => {
                        reach_seq_funs(ctxt, state);
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
            if let Some(f_trigs) = ctxt.typ_to_trigger_broadcasts.get(&t) {
                for f_trig in f_trigs {
                    reach_function_via_reveal(ctxt, state, f_trig);
                }
            }
            match &t {
                ReachedType::Datatype(path) => {
                    let datatype = &ctxt.datatype_map[path];
                    traverse_generic_bounds(ctxt, state, &datatype.x.typ_bounds, false);
                    crate::ast_visitor::map_datatype_visitor_env(&datatype, state, &ft).unwrap();
                }
                ReachedType::SpecFn(arity) => {
                    state.spec_fn_types.insert(*arity);
                }
                ReachedType::Array => {
                    state.uses_array = true;
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
            if let Some(tr) = ctxt.trait_map.get(&b) {
                // For assoc_type_trait_bounds_to_air, reach typ_bounds and assoc_typs_bounds
                traverse_generic_bounds(ctxt, state, &tr.x.typ_bounds, true);
                traverse_generic_bounds(ctxt, state, &tr.x.assoc_typs_bounds, true);
            }
            continue;
        }
        if let Some(i) = state.worklist_trait_impls.pop() {
            if let Some(trait_impl) = ctxt.trait_impl_map.get(&i) {
                for bound_trait in &trait_impl.bound_traits {
                    reach_bound_trait(ctxt, state, bound_trait);
                }
                for bound_type in &trait_impl.bound_types {
                    reach_type(ctxt, state, bound_type);
                }
                let ti = &trait_impl.trait_impl;
                traverse_generic_bounds(ctxt, state, &ti.x.typ_bounds, false);
                crate::ast_visitor::map_trait_impl_visitor_env(&ti, state, &ft).unwrap();
            }
            continue;
        }
        if let Some(a) = state.worklist_assoc_type_decls.pop() {
            let typs: Vec<ReachedType> = state.reached_types.iter().cloned().collect();
            for t in typs {
                reach_assoc_type_impl(ctxt, state, &(t.clone(), a.clone()));
            }
            // assoc_type_trait_bounds_to_air needs typ_bounds and assoc_typs_bounds, so reach them.
            // We could be more precise and reach only the bounds relevant to a,
            // but this is probably not worth the complexity.
            // Instead, just have reach_bound_trait reach all of typ_bounds and assoc_typs_bounds.
            reach_bound_trait(ctxt, state, &a.0);
            continue;
        }
        if let Some(assoc_group) = state.worklist_assoc_type_impls.pop() {
            if let Some(assoc_impls) = ctxt.assoc_type_impl_map.get(&assoc_group) {
                for assoc_impl in assoc_impls {
                    traverse_generic_bounds(ctxt, state, &assoc_impl.x.typ_bounds, false);
                    crate::ast_visitor::map_assoc_type_impl_visitor_env(&assoc_impl, state, &ft)
                        .unwrap();
                }
            }
            continue;
        }
        break;
    }
    assert!(state.worklist_functions.len() == 0);
    assert!(state.worklist_reveal_groups.len() == 0);
    assert!(state.worklist_types.len() == 0);
    assert!(state.worklist_bound_traits.len() == 0);
    assert!(state.worklist_trait_impls.len() == 0);
    assert!(state.worklist_assoc_type_decls.len() == 0);
    assert!(state.worklist_assoc_type_impls.len() == 0);
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
    // opaque functions,
    // but it would require refactoring the way we decide to keep or erase opaque function bodies,
    // which doesn't seem worth it now to optimize a feature that isn't really used yet.
    // So we just make an overapproximation.
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

fn collect_broadcast_triggers(f: &Function) -> Vec<(Vec<Fun>, Vec<ReachedType>)> {
    use crate::ast::{Exprs, TriggerAnnotation, UnaryOp};
    let mut unary_trigs: Vec<Expr> = Vec::new();
    let mut with_triggers: Vec<Exprs> = Vec::new();
    let mut map: VisitorScopeMap = ScopeMap::new();
    let mut f_get_triggers = |_: &mut VisitorScopeMap, expr: &Expr| {
        match &expr.x {
            ExprX::WithTriggers { triggers, body: _ } => {
                with_triggers.extend((**triggers).clone());
                VisitorControlFlow::Recurse
            }
            ExprX::Unary(UnaryOp::Trigger(TriggerAnnotation::Trigger(..)), e) => {
                unary_trigs.push(e.clone());
                VisitorControlFlow::Recurse
            }
            ExprX::Unary(UnaryOp::Trigger(..), _) => {
                // TODO: we should probably make this an error
                VisitorControlFlow::Stop(())
            }
            ExprX::Quant(..) => VisitorControlFlow::Return,
            _ => VisitorControlFlow::Recurse,
        }
    };

    // Collect all triggers
    for expr in f.x.require.iter().chain(f.x.ensure.iter()) {
        let control = crate::ast_visitor::expr_visitor_dfs(expr, &mut map, &mut f_get_triggers);
        if control == VisitorControlFlow::Stop(()) {
            return vec![];
        }
    }
    if unary_trigs.len() > 0 {
        with_triggers.push(Arc::new(unary_trigs));
    }

    // Collect function calls and types in each trigger
    // (Note: it's ok to err on the side of missing some function calls and types)
    let mut trigs: Vec<(Vec<Fun>, Vec<ReachedType>)> = Vec::new();
    for trig in &with_triggers {
        let mut call_set: HashSet<Fun> = HashSet::new();
        let mut calls: Vec<Fun> = Vec::new();
        let mut typ_set: HashSet<ReachedType> = HashSet::new();
        let mut typs: Vec<ReachedType> = Vec::new();
        typ_set.insert(ReachedType::None);
        let mut ft = |typ: &Typ| {
            let t = typ_to_reached_type(typ);
            if !typ_set.contains(&t) {
                typ_set.insert(t.clone());
                typs.push(t.clone());
            }
        };
        let mut f_get_calls = |_: &mut VisitorScopeMap, expr: &Expr| {
            ft(&expr.typ);
            match &expr.x {
                ExprX::Call(CallTarget::Fun(_, name, ts, _, _), _) => {
                    for typ in ts.iter() {
                        ft(typ);
                    }
                    if !call_set.contains(name) {
                        call_set.insert(name.clone());
                        calls.push(name.clone());
                    }
                    VisitorControlFlow::Recurse
                }
                _ => VisitorControlFlow::Recurse,
            }
        };
        for term in trig.iter() {
            let control =
                crate::ast_visitor::expr_visitor_dfs(term, &mut ScopeMap::new(), &mut f_get_calls);
            if control == VisitorControlFlow::Stop(()) {
                return vec![];
            }
        }
        if calls.len() == 0 && typs.len() == 0 {
            // For the case of a trigger with no function calls (e.g. a trigger on an
            // arithmetic op), we don't prune.
            return vec![];
        }
        trigs.push((calls, typs));
    }
    trigs
}

//  - module is none: prune to keep what's reachable from current_crate
//    module is some and fun is none: prune to keep what's reachable from module
//    module is some and fun is some: prune to keep what's reachable from fun
//  - collect_monotyps: if true, return a Vec<MonoTyp>; otherwise, return None
//    this should only be done post-simplification

pub fn prune_krate_for_module_or_krate(
    krate: &Krate,
    crate_name: &Ident,
    current_crate: Option<&Krate>,
    module: Option<Path>,
    fun: Option<&Fun>,
    collect_monotyps: bool,
) -> (Krate, Option<Vec<MonoTyp>>, Vec<usize>, bool, Vec<Fun>) {
    assert!(module.is_some() != current_crate.is_some());

    let mut root_modules: HashSet<Path> = HashSet::new();
    let mut root_functions: HashSet<Fun> = HashSet::new();
    if let Some(module) = &module {
        root_modules.insert(module.clone());
        if let Some(fun) = fun {
            root_functions.insert(fun.clone());
        } else {
            for f in &krate.functions {
                match &f.x.owning_module {
                    Some(m) if m == module => {
                        root_functions.insert(f.x.name.clone());
                    }
                    _ => {}
                }
            }
        }
    } else if let Some(current_crate) = current_crate {
        for m in &current_crate.modules {
            root_modules.insert(m.x.path.clone());
        }
        for f in &current_crate.functions {
            root_functions.insert(f.x.name.clone());
        }
    } else {
        unreachable!();
    }
    let is_root_module = |module_path: &Path| root_modules.contains(module_path);
    let is_root_function = |function: &Function| root_functions.contains(&function.x.name);

    let mut state: State = Default::default();
    if collect_monotyps {
        state.mono_abstract_datatypes = Some(HashSet::new());
    }
    if let Some(current_crate) = current_crate {
        // Make sure we keep all of current_crate,
        // so that all of current_crate is sent to the well-formedness checks.
        let KrateX {
            functions,
            reveal_groups,
            datatypes,
            assoc_type_impls,
            traits,
            trait_impls,
            modules: _,
            external_fns: _no_pruning_of_external_fns,
            external_types: _no_pruning_of_external_types,
            path_as_rust_names: _no_pruning_of_past_as_rust_names,
            arch: _no_pruning_of_arch,
        } = &**current_crate;
        for f in functions {
            reach(&mut state.reached_functions, &mut state.worklist_functions, &f.x.name);
        }
        for f in reveal_groups {
            reach(&mut state.reached_functions, &mut state.worklist_reveal_groups, &f.x.name);
        }
        for d in datatypes {
            let t = ReachedType::Datatype(d.x.path.clone());
            reach(&mut state.reached_types, &mut state.worklist_types, &t);
        }
        for a in assoc_type_impls {
            reach(
                &mut state.reached_assoc_type_impls,
                &mut state.worklist_assoc_type_impls,
                &a.x.prune_name(),
            );
        }
        for tr in traits {
            reach(&mut state.reached_bound_traits, &mut state.worklist_bound_traits, &tr.x.name);
        }
        for i in trait_impls {
            reach(&mut state.reached_trait_impls, &mut state.worklist_trait_impls, &i.x.impl_path);
        }
    }

    let mut root_modules_reveal: Vec<Fun> = Vec::new();
    for m in &krate.modules {
        if is_root_module(&m.x.path) {
            if let Some(reveals) = &m.x.reveals {
                root_modules_reveal.extend(reveals.x.clone());
            }
        }
    }

    // Collect all functions that our module reveals:
    let mut revealed_functions: HashSet<Fun> = HashSet::new();
    let mut assert_by_compute = false;
    for f in &krate.functions {
        if is_root_function(f) {
            if let Some(body) = &f.x.body {
                crate::ast_visitor::expr_visitor_check::<(), _>(
                    body,
                    &mut |_scope_map, e: &Expr| {
                        match &e.x {
                            ExprX::Fuel(path, fuel, _is_broadcast_use) if *fuel > 0 => {
                                revealed_functions.insert(path.clone());
                            }
                            ExprX::AssertCompute(..) => {
                                assert_by_compute = true;
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
    let reveal_group_set: HashSet<Fun> =
        krate.reveal_groups.iter().map(|g| g.x.name.clone()).collect();
    for f in &root_modules_reveal {
        revealed_functions.insert(f.clone());
        if reveal_group_set.contains(f) {
            reach(&mut state.reached_functions, &mut state.worklist_reveal_groups, f);
        } else {
            reach(&mut state.reached_functions, &mut state.worklist_functions, f);
        }
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
        if is_visible_to_or_true(&f.x.visibility, &module) {
            reveal_groups.push(f.clone());
            if revealed_functions.contains(&f.x.name) {
                reach(&mut state.reached_functions, &mut state.worklist_reveal_groups, &f.x.name);
            }
        }
    }
    overapproximate_revealed_functions(&mut revealed_functions, &reveal_groups);
    for f in &krate.functions {
        if module.is_none() || is_root_function(f) {
            functions.push(f.clone());
            if is_root_function(f) {
                // our function
                reach(&mut state.reached_functions, &mut state.worklist_functions, &f.x.name);
            }
            continue;
        }
        // Remove body if any of the following are true:
        // - function is not visible
        // - function is abstract
        // - function is opaque and not revealed
        // - function is exec or proof
        // (when optimizing for modules, after well-formedness checks)
        let vis = f.x.visibility.clone();
        let is_vis = is_visible_to_or_true(&vis, &module);
        let within_module = if let Some(module) = &module {
            is_visible_to_of_owner(&f.x.owning_module, module)
        } else {
            true
        };
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
            Some(path) if is_root_module(path) => {
                // our datatype
                let t = ReachedType::Datatype(d.x.path.clone());
                reach(&mut state.reached_types, &mut state.worklist_types, &t);
            }
            _ => {}
        }
        let is_vis = is_visible_to_or_true(&d.x.visibility, &module);
        let is_transparent =
            if let Some(module) = &module { is_datatype_transparent(module, &d) } else { true };
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
    let mut trait_map: HashMap<Path, Trait> = HashMap::new();
    let mut assoc_type_impl_map: HashMap<AssocTypeGroup, Vec<AssocTypeImpl>> = HashMap::new();
    let mut trait_to_trait_impls: HashMap<TraitName, Vec<ImplName>> = HashMap::new();
    let mut typ_to_trait_impls: HashMap<ReachedType, Vec<ImplName>> = HashMap::new();
    let mut trait_impl_map: HashMap<ImplName, ReachTraitImpl> = HashMap::new();
    let mut method_map: HashMap<(ReachedType, Fun), Vec<Fun>> = HashMap::new();
    let mut fun_to_trigger_broadcasts: HashMap<Fun, Vec<Fun>> = HashMap::new();
    let mut typ_to_trigger_broadcasts: HashMap<ReachedType, Vec<Fun>> = HashMap::new();
    let mut fun_revealed_broadcast_map: HashMap<Fun, ReachBroadcastFunction> = HashMap::new();
    let mut assert_by_compute_seq_funs: Vec<Fun> = Vec::new();
    for f in &functions {
        function_map.insert(f.x.name.clone(), f.clone());
        if let FunctionKind::TraitMethodImpl { method, trait_typ_args, .. }
        | FunctionKind::ForeignTraitMethodImpl { method, trait_typ_args, .. } = &f.x.kind
        {
            let self_typ = &trait_typ_args[0];
            let key = (typ_to_reached_type(self_typ), method.clone());
            if !method_map.contains_key(&key) {
                method_map.insert(key.clone(), Vec::new());
            }
            method_map.get_mut(&key).unwrap().push(f.x.name.clone());
        }
        if revealed_functions.contains(&f.x.name) {
            let reach_triggers = collect_broadcast_triggers(f);
            for (trig_funs, trig_typs) in &reach_triggers {
                for term in trig_funs {
                    fun_to_trigger_broadcasts
                        .entry(term.clone())
                        .or_insert_with(|| Vec::new())
                        .push(f.x.name.clone());
                }
                for typ in trig_typs {
                    typ_to_trigger_broadcasts
                        .entry(typ.clone())
                        .or_insert_with(|| Vec::new())
                        .push(f.x.name.clone());
                }
            }
            let reach_broadcast = ReachBroadcastFunction { reach_triggers };
            fun_revealed_broadcast_map.insert(f.x.name.clone(), reach_broadcast);
        }
        if assert_by_compute && crate::interpreter::is_seq_to_sst_fun(&f.x.name) {
            assert_by_compute_seq_funs.push(f.x.name.clone());
        }
    }
    for f in &reveal_groups {
        reveal_group_map.insert(f.x.name.clone(), f.clone());
    }
    for d in &datatypes {
        datatype_map.insert(d.x.path.clone(), d.clone());
    }
    for tr in krate.traits.iter() {
        trait_map.insert(tr.x.name.clone(), tr.clone());
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
        let trait_impl = ReachTraitImpl {
            trait_impl: imp.clone(),
            bound_traits,
            bound_types,
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
        assert!(module.is_none() || !trait_impl_map.contains_key(&imp.x.impl_path));
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
        trait_map,
        trait_to_trait_impls,
        typ_to_trait_impls,
        trait_impl_map,
        assoc_type_impl_map,
        method_map,
        fun_to_trigger_broadcasts,
        typ_to_trigger_broadcasts,
        fun_revealed_broadcast_map,
        vstd_crate_name,
        assert_by_compute,
        assert_by_compute_seq_funs,
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
        let assoc_typs_bounds = if state.reached_bound_traits.contains(&tr.x.name) {
            traitx.assoc_typs_bounds
        } else {
            Arc::new(vec![])
        };
        traits.push(Spanned::new(
            tr.span.clone(),
            TraitX { assoc_typs, assoc_typs_bounds, ..traitx },
        ));
    }

    let modules: Vec<Module> = krate
        .modules
        .iter()
        .map(|mm| {
            mm.map_x(|m| ModuleX {
                path: m.path.clone(),
                reveals: if is_root_module(&m.path) { m.reveals.clone() } else { None },
            })
        })
        .collect();

    debug_assert!(
        module.is_none() || modules.iter().filter(|m| m.x.reveals.is_some()).count() <= 1
    );

    let set_broadcast_only = |mut f: Function| {
        if f.x.attrs.broadcast_forall
            && !state.broadcast_functions_fully_reached.contains(&f.x.name)
        {
            Arc::make_mut(&mut Arc::make_mut(&mut f).x.attrs).broadcast_forall_only = true;
        }
        f
    };

    let kratex = KrateX {
        functions: functions
            .into_iter()
            .filter(|f| state.reached_functions.contains(&f.x.name))
            .map(set_broadcast_only)
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
        traits: traits
            .into_iter()
            .filter(|t| state.reached_bound_traits.contains(&t.x.name))
            .collect(),
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
    let mut spec_fn_types: Vec<usize> = state.spec_fn_types.into_iter().collect();
    spec_fn_types.sort();
    let mut fndef_types: Vec<Fun> = state.fndef_types.into_iter().collect();
    fndef_types.sort();
    let mono_abstract_datatypes = match state.mono_abstract_datatypes {
        Some(mono) => {
            let mut mono: Vec<MonoTyp> = mono.into_iter().collect();
            mono.sort();
            Some(mono)
        }
        _ => None,
    };
    (Arc::new(kratex), mono_abstract_datatypes, spec_fn_types, state.uses_array, fndef_types)
}
