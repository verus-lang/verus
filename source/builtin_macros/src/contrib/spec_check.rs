//! Labels for [verus-spec-check](https://github.com/verus-lang/verus-spec-check) inside `verus!`.
//!
//! verus-spec-check turns contracts into tests. Code opts in with labels:
//! `#[vcheck]`, `#[vcheck_provide]`, `#[vcheck_axiom]`, `#[vcheck_view]`,
//! `#[vcheck_cov_mutate]` and `#[vcheck_cov_fuzz]` on items, `#[vcheck] assert(...)` inside
//! function bodies, and `external_vcheck_provide! { ... }` items. Like the other contrib
//! attributes, a label may be written as `#[m]`, `#[contrib::m]` or `#[vstd::contrib::m]`.
//!
//! By default the labels are inert: `verus!` strips them, so labeled code builds and verifies
//! exactly as if they were absent. This is the stub that lets vstd carry labels without
//! always depending on verus-spec-check.
//!
//! With the `spec-check` cargo feature, a labeled item list in vstd is instead handed, prior
//! to other `verus!` processing, to `vstd::contrib::spec_check::vcheck_preprocess!`. In vstd's
//! `cargo test --features spec-check` build that macro runs the verus-spec-check engine over the
//! list and re-enters `verus!` through `verus_spec_check_resume!`, which then strips whatever
//! labels are left. In every other build it forwards straight to `verus_spec_check_resume!`.
//! See `source/vstd_spec_check/README.md`.

use verus_syn::visit_mut::{self, VisitMut};
use verus_syn::{Attribute, ImplItem, Item, TraitItem};

/// Attribute labels, matched leniently like the other contrib attributes.
const LABELS: &[&str] = &[
    "vcheck",
    "vcheck_provide",
    "vcheck_axiom",
    "vcheck_view",
    "vcheck_cov_mutate",
    "vcheck_cov_fuzz",
];

/// Item-level macro that only means something to the verus-spec-check engine.
const PROVIDE_MACRO: &str = "external_vcheck_provide";

fn is_label(attr: &Attribute) -> bool {
    super::traverse_path(attr.path()).is_some_and(|name| LABELS.contains(&name.as_str()))
}

fn has_label(attrs: &[Attribute]) -> bool {
    attrs.iter().any(is_label)
}

fn strip_labels(attrs: &mut Vec<Attribute>) {
    attrs.retain(|attr| !is_label(attr));
}

fn is_provide_macro(item: &Item) -> bool {
    match item {
        Item::Macro(m) => super::traverse_path(&m.mac.path).is_some_and(|n| n == PROVIDE_MACRO),
        _ => false,
    }
}

fn item_attrs_mut(item: &mut Item) -> Option<&mut Vec<Attribute>> {
    match item {
        Item::Const(i) => Some(&mut i.attrs),
        Item::Enum(i) => Some(&mut i.attrs),
        Item::ExternCrate(i) => Some(&mut i.attrs),
        Item::Fn(i) => Some(&mut i.attrs),
        Item::ForeignMod(i) => Some(&mut i.attrs),
        Item::Impl(i) => Some(&mut i.attrs),
        Item::Macro(i) => Some(&mut i.attrs),
        Item::Mod(i) => Some(&mut i.attrs),
        Item::Static(i) => Some(&mut i.attrs),
        Item::Struct(i) => Some(&mut i.attrs),
        Item::Trait(i) => Some(&mut i.attrs),
        Item::TraitAlias(i) => Some(&mut i.attrs),
        Item::Type(i) => Some(&mut i.attrs),
        Item::Union(i) => Some(&mut i.attrs),
        Item::Use(i) => Some(&mut i.attrs),
        Item::Global(i) => Some(&mut i.attrs),
        Item::BroadcastUse(i) => Some(&mut i.attrs),
        Item::BroadcastGroup(i) => Some(&mut i.attrs),
        Item::AssumeSpecification(i) => Some(&mut i.attrs),
        _ => None,
    }
}

fn impl_item_attrs_mut(item: &mut ImplItem) -> Option<&mut Vec<Attribute>> {
    match item {
        ImplItem::Const(i) => Some(&mut i.attrs),
        ImplItem::Fn(i) => Some(&mut i.attrs),
        ImplItem::Type(i) => Some(&mut i.attrs),
        ImplItem::Macro(i) => Some(&mut i.attrs),
        ImplItem::BroadcastGroup(i) => Some(&mut i.attrs),
        _ => None,
    }
}

fn trait_item_attrs_mut(item: &mut TraitItem) -> Option<&mut Vec<Attribute>> {
    match item {
        TraitItem::Const(i) => Some(&mut i.attrs),
        TraitItem::Fn(i) => Some(&mut i.attrs),
        TraitItem::Type(i) => Some(&mut i.attrs),
        TraitItem::Macro(i) => Some(&mut i.attrs),
        _ => None,
    }
}

/// Finds (`strip == false`) or removes (`strip == true`) the labels on inline
/// `assert(...)` / `assert forall` expressions, the only expressions the engine labels.
struct AssertLabels {
    strip: bool,
    found: bool,
}

impl VisitMut for AssertLabels {
    fn visit_assert_mut(&mut self, node: &mut verus_syn::Assert) {
        self.found |= has_label(&node.attrs);
        if self.strip {
            strip_labels(&mut node.attrs);
        }
        visit_mut::visit_assert_mut(self, node);
    }

    fn visit_assert_forall_mut(&mut self, node: &mut verus_syn::AssertForall) {
        self.found |= has_label(&node.attrs);
        if self.strip {
            strip_labels(&mut node.attrs);
        }
        visit_mut::visit_assert_forall_mut(self, node);
    }
}

fn visit_asserts_in_item(item: &mut Item, strip: bool) -> bool {
    let mut visitor = AssertLabels { strip, found: false };
    match item {
        Item::Fn(f) => visitor.visit_block_mut(&mut f.block),
        Item::Impl(i) => {
            for ii in &mut i.items {
                if let ImplItem::Fn(f) = ii {
                    visitor.visit_block_mut(&mut f.block);
                }
            }
        }
        Item::Trait(t) => {
            for ti in &mut t.items {
                if let TraitItem::Fn(f) = ti {
                    if let Some(block) = &mut f.default {
                        visitor.visit_block_mut(block);
                    }
                }
            }
        }
        _ => {}
    }
    visitor.found
}

/// True if any item in the list (or one of its impl/trait items, or an inline assert in one
/// of its function bodies) carries a label, or if the list contains `external_vcheck_provide!`.
fn has_labels(items: &mut [Item]) -> bool {
    items.iter_mut().any(|item| {
        if is_provide_macro(item) {
            return true;
        }
        if item_attrs_mut(item).is_some_and(|attrs| has_label(attrs)) {
            return true;
        }
        let member_labeled = match item {
            Item::Impl(i) => i
                .items
                .iter_mut()
                .any(|ii| impl_item_attrs_mut(ii).is_some_and(|attrs| has_label(attrs))),
            Item::Trait(t) => t
                .items
                .iter_mut()
                .any(|ti| trait_item_attrs_mut(ti).is_some_and(|attrs| has_label(attrs))),
            _ => false,
        };
        member_labeled || visit_asserts_in_item(item, false)
    })
}

fn strip_items(items: &mut Vec<Item>) {
    items.retain(|item| !is_provide_macro(item));
    for item in items.iter_mut() {
        if let Some(attrs) = item_attrs_mut(item) {
            strip_labels(attrs);
        }
        match item {
            Item::Impl(i) => {
                for ii in &mut i.items {
                    if let Some(attrs) = impl_item_attrs_mut(ii) {
                        strip_labels(attrs);
                    }
                }
            }
            Item::Trait(t) => {
                for ti in &mut t.items {
                    if let Some(attrs) = trait_item_attrs_mut(ti) {
                        strip_labels(attrs);
                    }
                }
            }
            _ => {}
        }
        visit_asserts_in_item(item, true);
    }
}

/// Runs on every item list `verus!` preprocesses (top level, inline modules, and items inside
/// function bodies), after any out-of-tree `contrib::hooks`.
pub(crate) fn preprocess_items(items: &mut Vec<Item>) {
    if !has_labels(items) {
        return;
    }
    #[cfg(feature = "spec-check")]
    if !resume::active() && matches!(crate::vstd_kind(), crate::VstdKind::IsVstd) {
        let labeled = std::mem::take(items);
        items.push(verus_syn::parse_quote! {
            crate::contrib::spec_check::vcheck_preprocess! { #(#labeled)* }
        });
        return;
    }
    strip_items(items);
}

/// Runs on every impl item list `verus_impl!` / `verus_trait_impl!` preprocess. The engine has
/// no pass over bare impl item lists, so labels here are always stripped.
pub(crate) fn preprocess_impl_items(items: &mut Vec<ImplItem>) {
    for item in items.iter_mut() {
        if let Some(attrs) = impl_item_attrs_mut(item) {
            strip_labels(attrs);
        }
        if let ImplItem::Fn(f) = item {
            AssertLabels { strip: true, found: false }.visit_block_mut(&mut f.block);
        }
    }
}

/// Tracks whether the current expansion is `verus_spec_check_resume!`, i.e. whether the engine
/// has already run over this item list, so that leftover labels are stripped rather than
/// handed back to the engine.
#[cfg(feature = "spec-check")]
pub(crate) mod resume {
    use std::cell::Cell;

    thread_local! {
        static ACTIVE: Cell<bool> = const { Cell::new(false) };
    }

    pub(crate) fn active() -> bool {
        ACTIVE.with(|a| a.get())
    }

    struct Reset(bool);

    impl Drop for Reset {
        fn drop(&mut self) {
            ACTIVE.with(|a| a.set(self.0));
        }
    }

    pub(crate) fn run<R>(f: impl FnOnce() -> R) -> R {
        let _reset = Reset(ACTIVE.with(|a| a.replace(true)));
        f()
    }
}
