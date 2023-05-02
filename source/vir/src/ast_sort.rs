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

    let KrateX { functions, datatypes, traits, module_ids, external_fns, external_types } =
        &**krate;
    let mut functions = functions.clone();
    let mut datatypes = datatypes.clone();
    let traits = traits.clone();
    let mut module_ids = module_ids.clone();
    let external_fns = external_fns.clone();
    let external_types = external_types.clone();

    // Stable sort to move children before parents, but otherwise leave children in order
    module_ids.sort_by(|p1, p2| p2.segments.len().cmp(&p1.segments.len()));

    // Remember the module order:
    let mut module_order: HashMap<Option<Path>, usize> = HashMap::new();
    module_order.insert(None, 0);
    for (i, path) in module_ids.iter().enumerate() {
        module_order.insert(Some(path.clone()), i + 1);
    }

    // Sort the items by owning module:
    functions.sort_by(|i1, i2| {
        module_order.get(&i1.x.owning_module).cmp(&module_order.get(&i2.x.owning_module))
    });
    datatypes.sort_by(|i1, i2| {
        module_order.get(&i1.x.owning_module).cmp(&module_order.get(&i2.x.owning_module))
    });

    Arc::new(KrateX { functions, datatypes, traits, module_ids, external_fns, external_types })
}
