/// Traits with special handling
enum SpecialTrait {
    Clone,
    PartialEq,
}

/// What to do for a given automatically-derived trait impl
enum AutomaticDeriveAction {
    Special(SpecialTrait),
    VerifyAsIs,
    Ignore(Option<VirErrAs>),
}

pub fn get_action(rust_item: Option<RustItem>) {
    match rust_item {
        Some(RustItem::PartialEq) => AutomaticDeriveAction::Special(SpecialTrait::PartialEq),
        Some(RustItem::Clone) => AutomaticDeriveAction::Special(SpecialTrait::Clone),

        Some(RustItem::Eq) | Some(RustItem::Copy) => AutomaticDeriveAction::VerifyAsIs,

        Some(RustItem::Hash)
        | Some(RustItem::Default)
        | Some(RustItem::Debug)
        => AutomaticDeriveAction::Ignore(None),

        Some(_) => {
            AutomaticDeriveAction::Ignore()
        }
        None => AutomaticDeriveAction::VerifyAsIs,
    }
}

pub fn is_automatically_derived(attrs: &[rustc_ast::Attribute]) -> bool {
    for attr in attrs.iter() {
        match &attr.kind {
            rustc_ast::AttrKind::Normal(item) => match &item.item.path.segments[..] {
                [segment] => if segment.ident.as_str() == "automatically_derived" {
                    return true;
                }
                _ => { }
            }
            _ => { }
        }
    }
    false
}
