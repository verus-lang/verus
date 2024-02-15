use std::sync::Arc;
use vir::ast::{KrateX, TraitX, Visibility};
use vir::def::Spanned;
use vir::{fun, path};

pub(crate) fn add_std_traits(krate: &mut KrateX, no_span: vir::messages::Span) {
    /*krate.traits.push(Arc::new(TraitX {
        name: path!("core" => "cmp", "PartialEq"),
        visibility: Visibility::public(),
        typ_params: Arc::new(vec![]),
        typ_bounds: Arc::new(vec![]),
        assoc_typs: Arc::new(vec![std_ident("Rhs")]),
        assoc_typs_bounds: Arc::new(vec![]),
        methods: Arc::new(vec![
            fun!("core" => "cmp", "PartialEq", "eq"),
            fun!("core" => "cmp", "PartialEq", "ne"),
        ]),
    }));*/

    // Ignoring clone_from for now because it has a default implementation
    // which makes it complicated to get it working with the external_fn_specification
    // stuff.

    krate.traits.push(Spanned::new(
        no_span,
        TraitX {
            name: path!("core" => "clone", "Clone"),
            visibility: Visibility::public(),
            typ_params: Arc::new(vec![]),
            typ_bounds: Arc::new(vec![]),
            assoc_typs: Arc::new(vec![]),
            assoc_typs_bounds: Arc::new(vec![]),
            methods: Arc::new(vec![
                fun!("core" => "clone", "Clone", "clone"),
                //fun!("core" => "clone", "Clone", "clone_from"),
            ]),
        },
    ));
}
