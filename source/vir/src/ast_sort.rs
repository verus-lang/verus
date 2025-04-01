use crate::ast::{Krate, KrateX, Path};
use std::collections::HashMap;
use std::sync::Arc;

pub fn sort_krate(krate: &Krate) -> Krate {
    // REVIEW:
    // In principle, the ordering of items within a crate is irrelevant.
    // In practice, it currently matters for two reasons:
    // - we don't yet have an ordering for broadcast_forall (this is TODO),
    //   so these show up in the order they appear in the crate
    // - error messages for the user are printed in the order that the errant items appear in the crate
    // Unfortunately, macros that act on items dump the items out of order,
    // scattering them across modules.
    // We try to put the items back in some intuitive order here.
    // The ordering we choose is:
    // - child modules appear before parent modules
    // - otherwise, modules are ordered as they appear in the crate
    // - all items from a module are grouped together

    let KrateX {
        functions,
        reveal_groups,
        datatypes,
        traits,
        trait_impls,
        assoc_type_impls,
        modules,
        external_fns,
        external_types,
        path_as_rust_names,
        arch,
    } = &**krate;
    let mut functions = functions.clone();
    let mut datatypes = datatypes.clone();
    let traits = traits.clone();
    let assoc_type_impls = assoc_type_impls.clone();
    let mut modules = modules.clone();
    let external_fns = external_fns.clone();
    let external_types = external_types.clone();

    // Stable sort to move children before parents, but otherwise leave children in order
    modules.sort_by(|p1, p2| p2.x.path.segments.len().cmp(&p1.x.path.segments.len()));

    // Remember the module order:
    let mut module_order: HashMap<Option<Path>, usize> = HashMap::new();
    module_order.insert(None, 0);
    for (i, m) in modules.iter().enumerate() {
        module_order.insert(Some(m.x.path.clone()), i + 1);
    }

    // Sort the items by owning module:
    functions.sort_by(|i1, i2| {
        module_order.get(&i1.x.owning_module).cmp(&module_order.get(&i2.x.owning_module))
    });
    datatypes.sort_by(|i1, i2| {
        module_order.get(&i1.x.owning_module).cmp(&module_order.get(&i2.x.owning_module))
    });

    Arc::new(KrateX {
        functions,
        reveal_groups: reveal_groups.clone(),
        datatypes,
        traits,
        trait_impls: trait_impls.clone(),
        assoc_type_impls,
        modules,
        external_fns,
        external_types,
        path_as_rust_names: path_as_rust_names.clone(),
        arch: arch.clone(),
    })
}
