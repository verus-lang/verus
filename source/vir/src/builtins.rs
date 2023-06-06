use crate::ast::{DatatypeTransparency, DatatypeX, GenericBoundX, Krate, KrateX, Mode, Visibility};
use crate::def::Spanned;
use air::ast::Span;
use air::ast_util::ident_binder;
use std::sync::Arc;

pub fn krate_add_builtins(no_span: &Span, krate: &mut KrateX) {
    // Add a datatype for 'slice'

    let path = crate::def::slice_type();
    let visibility = Visibility { owning_module: None, restricted_to: None };
    let transparency = DatatypeTransparency::Never;

    // Create a fake variant; it shouldn't matter, since transparency is Never.
    let fields = Arc::new(vec![]);
    let variant = ident_binder(&Arc::new("DummySliceVariant".to_string()), &fields);
    let variants = Arc::new(vec![variant]);

    let bound = Arc::new(GenericBoundX::Traits(vec![]));
    let is_strictly_positive = true;
    let typ_params = Arc::new(vec![(crate::def::slice_param(), bound, is_strictly_positive)]);
    let datatypex =
        DatatypeX { path, visibility, transparency, typ_params, variants, mode: Mode::Exec };
    krate.datatypes.push(Spanned::new(no_span.clone(), datatypex));
}

pub fn builtin_krate(no_span: &Span) -> Krate {
    let mut kratex = KrateX {
        functions: Vec::new(),
        datatypes: Vec::new(),
        traits: Vec::new(),
        assoc_type_impls: Vec::new(),
        module_ids: Vec::new(),
    };
    krate_add_builtins(no_span, &mut kratex);
    Arc::new(kratex)
}
