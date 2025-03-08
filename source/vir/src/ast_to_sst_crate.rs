use crate::ast::{Fun, Krate, VirErr};
use crate::ast_to_sst_func::function_to_sst;
use crate::context::Ctx;
use crate::sst::{FunctionSst, KrateSst, KrateSstX};
use crate::sst_elaborate::{elaborate_function1, elaborate_function2};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub fn ast_to_sst_krate(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    bucket_funs: &HashSet<Fun>,
    krate: &Krate,
) -> Result<KrateSst, VirErr> {
    let mut func_workmap: HashMap<Fun, FunctionSst> = HashMap::new();
    for function in krate.functions.iter() {
        let vis = function.x.visibility.clone();
        let module = ctx.module_path();
        if !crate::ast_util::is_visible_to(&vis, &module) || function.x.attrs.is_decrease_by {
            continue;
        }

        let function_sst = function_to_sst(ctx, diagnostics, bucket_funs, function)?;

        assert!(!func_workmap.contains_key(&function.x.name));
        func_workmap.insert(function.x.name.clone(), function_sst);
    }

    let mut sst_infos: HashMap<Fun, FunctionSst> = HashMap::new();
    let mut functions: Vec<FunctionSst> = Vec::new();
    for scc_rep in ctx.global.func_call_sccs.iter() {
        let mut scc_functions: Vec<FunctionSst> = Vec::new();
        for node in ctx.global.func_call_graph.get_scc_nodes(&scc_rep) {
            if let crate::recursion::Node::Fun(f) = &node {
                if let Some(mut func_sst) = func_workmap.remove(f) {
                    elaborate_function1(ctx, diagnostics, &sst_infos, &mut func_sst)?;
                    scc_functions.push(func_sst);
                }
            }
        }
        for func_sst in scc_functions.into_iter() {
            if func_sst.x.axioms.spec_axioms.is_some() {
                assert!(!sst_infos.contains_key(&func_sst.x.name));
                sst_infos.insert(func_sst.x.name.clone(), func_sst.clone());
            }
            functions.push(func_sst.clone());
        }
    }
    assert!(func_workmap.len() == 0);

    let sst_map = Arc::new(sst_infos);
    for func_sst in &mut functions {
        elaborate_function2(ctx, diagnostics, sst_map.clone(), func_sst)?;

        assert!(!ctx.func_sst_map.contains_key(&func_sst.x.name));
        ctx.func_sst_map.insert(func_sst.x.name.clone(), func_sst.clone());
    }

    let krate_sst = Arc::new(KrateSstX {
        functions,
        datatypes: krate.datatypes.clone(),
        traits: krate.traits.clone(),
        trait_impls: krate.trait_impls.clone(),
        assoc_type_impls: krate.assoc_type_impls.clone(),
        reveal_groups: krate.reveal_groups.clone(),
    });
    Ok(krate_sst)
}
