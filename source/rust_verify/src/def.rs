use std::sync::Arc;

use crate::{context::Context, rust_to_vir_base::def_id_to_vir_path};

pub const IS_VARIANT_PREFIX: &str = "is";
pub const GET_VARIANT_PREFIX: &str = "get";

pub(crate) fn path_to_well_known_item(
    ctxt: &Context,
) -> Arc<std::collections::HashMap<vir::ast::Path, vir::ast::WellKnownItem>> {
    Arc::new(
        vec![(
            ctxt.tcx.lang_items().drop_trait().expect("drop trait lang item"),
            vir::ast::WellKnownItem::DropTrait,
        )]
        .into_iter()
        .map(|(did, wii)| (def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, did), wii))
        .collect(),
    )
}
