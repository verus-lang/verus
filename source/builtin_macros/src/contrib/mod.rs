pub mod auto_spec;

use proc_macro2::TokenStream;
use syn_verus::{Attribute, ImplItem, Item, Meta, Path};

fn item_attrs(item: &Item) -> Option<&Vec<Attribute>> {
    match item {
        Item::Const(i) => Some(&i.attrs),
        Item::Enum(i) => Some(&i.attrs),
        Item::ExternCrate(i) => Some(&i.attrs),
        Item::Fn(i) => Some(&i.attrs),
        Item::ForeignMod(i) => Some(&i.attrs),
        Item::Impl(i) => Some(&i.attrs),
        Item::Macro(i) => Some(&i.attrs),
        Item::Mod(i) => Some(&i.attrs),
        Item::Static(i) => Some(&i.attrs),
        Item::Struct(i) => Some(&i.attrs),
        Item::Trait(i) => Some(&i.attrs),
        Item::TraitAlias(i) => Some(&i.attrs),
        Item::Type(i) => Some(&i.attrs),
        Item::Union(i) => Some(&i.attrs),
        Item::Use(i) => Some(&i.attrs),
        Item::Global(i) => Some(&i.attrs),
        Item::BroadcastUse(i) => Some(&i.attrs),
        Item::BroadcastGroup(i) => Some(&i.attrs),
        Item::AssumeSpecification(i) => Some(&i.attrs),
        Item::Verbatim(_) => None,
        _ => {
            panic!("Item is non_exhaustive, preventing us from catching this panic statically")
        }
    }
}

fn impl_item_attrs(item: &ImplItem) -> Option<&Vec<Attribute>> {
    match item {
        ImplItem::Const(i) => Some(&i.attrs),
        ImplItem::Fn(i) => Some(&i.attrs),
        ImplItem::Type(i) => Some(&i.attrs),
        ImplItem::Macro(i) => Some(&i.attrs),
        ImplItem::BroadcastGroup(i) => Some(&i.attrs),
        ImplItem::Verbatim(_) => None,
        _ => {
            panic!("ImplItem is non_exhaustive, preventing us from catching this panic statically")
        }
    }
}

fn traverse_path(path: &Path) -> Option<String> {
    if path.leading_colon.is_some() {
        return None;
    }
    let segments: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segments: Vec<&str> = segments.iter().map(|s| s.as_str()).collect();
    match &segments[..] {
        [s] => Some(s.to_string()),
        ["contrib", s] => Some(s.to_string()),
        ["vstd", "contrib", s] => Some(s.to_string()),
        _ => None,
    }
}

fn collect_attrs(attrs: Option<&Vec<Attribute>>) -> Vec<(String, Option<TokenStream>)> {
    let Some(attrs) = attrs else {
        return vec![];
    };
    let mut attr_infos: Vec<(String, Option<TokenStream>)> = Vec::new();
    for attr in attrs {
        let Some(name) = traverse_path(attr.path()) else {
            continue;
        };
        let tokens = match &attr.meta {
            Meta::Path(_) => None,
            Meta::List(list) => Some(list.tokens.clone()),
            Meta::NameValue(_) => None,
        };
        attr_infos.push((name, tokens));
    }
    attr_infos
}

// It's often more useful to apply a macro to a syn_verus::Item before it's transformed
// by "verus!" into a verbose syn encoding.
// For example, we may want to look for "proof { ... }" blocks or change the mode of a Fn,
// and it's better to do these directly in syn_verus syntax than to try to reverse engineer
// the syn encoding of these features.
// Therefore, we give contrib macros a chance to preprocess the syn_verus code here.

// Unfortunately, name resolution hasn't run on item's attributes yet,
// so we don't have a good way to identify which macro is which.
// As a hack, we look for any of:
// - #[vstd::contrib::m(args)]
// - #[contrib::m(args)]
// - #[m(args)]
// where m is on the list of contrib macros and (args) is optional.

pub(crate) fn contrib_preprocess_item(item: &mut Item, new_items: &mut Vec<Item>) {
    for (name, tokens) in collect_attrs(item_attrs(item)) {
        match name.as_str() {
            // Add contrib macros needing preprocessing here:
            "auto_spec" => auto_spec::auto_spec_item(item, tokens, new_items),
            _ => {}
        };
    }
}

pub(crate) fn contrib_preprocess_impl_item(item: &mut ImplItem, new_items: &mut Vec<ImplItem>) {
    for (name, tokens) in collect_attrs(impl_item_attrs(item)) {
        match name.as_str() {
            // Add contrib macros needing preprocessing here:
            "auto_spec" => auto_spec::auto_spec_impl_item(item, tokens, new_items),
            _ => {}
        }
    }
}

pub(crate) fn contrib_preprocess_items(items: &mut Vec<Item>) {
    let mut i = 0;
    while i < items.len() {
        let mut new_items: Vec<Item> = Vec::new();
        contrib_preprocess_item(&mut items[i], &mut new_items);
        // Add new items and preprocess the new items as well:
        items.extend(new_items);
        i += 1;
    }
}

pub(crate) fn contrib_preprocess_impl_items(items: &mut Vec<ImplItem>) {
    let mut i = 0;
    while i < items.len() {
        let mut new_items: Vec<ImplItem> = Vec::new();
        contrib_preprocess_impl_item(&mut items[i], &mut new_items);
        // Add new items and preprocess the new items as well:
        items.extend(new_items);
        i += 1;
    }
}
