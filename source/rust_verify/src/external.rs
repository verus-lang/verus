/*!
This function traverses the entire crate and categorizes every
Item, ImplItem, TraitItem, and ForeignItem as either 'verus-aware' or 'external'.

This roughly goes as follows:

 * By default, things are external (though this can be configured)

 * If something is marked with a Verus attribute (such as `verify`) then it gets marked VerusAware

 * If something is marked external, then it's ignored. Also *all nested items*
   inside it are ignored.

Here are some odd cases to watch out for:

 * If an item is marked external_body, it automatically gets marked VerusAware.
   That way you don't have to mark the item as 'verify' too (since that'd be confusing).
   Similarly for a few other attributes, (see the `opts_in_to_verus` function).

 * However, if an item is marked external_body, then while the item itself
   is marked VerusAware, all its *nested* items are ignored.
   (This is important for the rare case where a function has nested items, for example.)

 * If an item (e.g., a module) is marked 'external', then EVERYTHING inside it is ignored,
   this can't be overriden from inside, not even if a nested item is marked 'verify'.
   This situation results in a warning.

 * For trait decls and trait impls, we disallow #[verifier::external] on individual
   TraitItems or ImplItems.

 * Autoderive traits need to be handled specially.

To implement this traversal, we use some rustc visitor machinery to do the recursive
traversal, while keeping track of the current state (Default, Verify, or External).
(The difference between Default and External is that if a module is in the Default state,
then it's nested items can be marked VerusAware, but if it's External, this this is not the case.)
*/

use crate::attributes::ExternalAttrs;
use crate::automatic_derive::AutomaticDeriveAction;
use crate::context::ContextX;
use crate::rust_to_vir_base::def_id_to_vir_path_option;
use crate::rustc_hir::intravisit::*;
use crate::verus_items::get_rust_item;
use rustc_hir::{
    ForeignItem, ForeignItemId, HirId, ImplItem, ImplItemId, ImplItemKind, Item, ItemId, ItemKind,
    OwnerId, TraitItem, TraitItemId, TraitItemKind,
};
use rustc_span::Span;
use std::collections::HashMap;
use vir::ast::{Path, VirErr, VirErrAs};

/// Main exported type of this module.
/// Contains all item-things and their categorizations
#[derive(Debug)]
pub struct CrateItems {
    /// Vector of all crate items
    pub items: Vec<CrateItem>,
    /// Same information, indexed by OwnerId
    pub map: HashMap<OwnerId, VerifOrExternal>,
}

/// Categorizes a single item-thing as VerusAware of External.
#[derive(Debug)]
pub struct CrateItem {
    pub id: GeneralItemId,
    pub verif: VerifOrExternal,
}

#[derive(Debug)]
pub struct OpaqueDef {
    pub id: rustc_hir::def_id::LocalDefId,
    pub verif: VerifOrExternal,
}

#[derive(Debug, Clone)]
pub enum VerifOrExternal {
    /// Path is the *module path* containing this item
    VerusAware { module_path: Path, const_directive: bool, external_body: bool },
    /// Path/String to refer to this item for diagnostics
    /// Path is an Option because there are some items we can't compute a Path for
    External { path: Option<Path>, path_string: String, explicit: bool },
}

/// Abstracts over the different the different ItemX things in rust

#[derive(Clone, Copy, Debug)]
pub enum GeneralItem<'a> {
    Item(&'a Item<'a>),
    ForeignItem(&'a ForeignItem<'a>),
    ImplItem(&'a ImplItem<'a>),
    TraitItem(&'a TraitItem<'a>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralItemId {
    ItemId(ItemId),
    ForeignItemId(ForeignItemId),
    ImplItemId(ImplItemId),
    TraitItemId(TraitItemId),
}

impl CrateItems {
    pub fn is_item_external(&self, item_id: ItemId) -> bool {
        matches!(self.map.get(&item_id.owner_id), Some(VerifOrExternal::External { .. }))
    }

    pub fn is_impl_item_external(&self, impl_item_id: ImplItemId) -> bool {
        matches!(self.map.get(&impl_item_id.owner_id), Some(VerifOrExternal::External { .. }))
    }

    pub fn is_trait_item_external(&self, trait_item_id: TraitItemId) -> bool {
        matches!(self.map.get(&trait_item_id.owner_id), Some(VerifOrExternal::External { .. }))
    }
}

/// Collect all items (Items, ForeignItems, and ImplItems), classified as either
/// 'External' or 'VerusAware'.
///
/// We should try to never 'error' for anything not marked verification-ready.
///
/// Notes:
///
///  1. Items can be nested. Verus doesn't really support these now but we need to
///     be careful about them in external/external_body functions. Don't error
///     if there's a nested item inside an external_body function.
///
///  2. Impls can be either 'normal impls' or 'trait impls'. For normal impls,
///     individual items can be treated as external individually.
///     Trait impls need to be "whole" so we forbid external_body on individual
///     ImplItems in a trait_impl.
pub(crate) fn get_crate_items<'tcx>(ctxt: &ContextX<'tcx>) -> Result<CrateItems, VirErr> {
    let default_state = if ctxt.cmd_line_args.no_external_by_default {
        VerifState::Verify
    } else {
        VerifState::Default
    };

    let root_module = ctxt.tcx.hir_root_module();
    let root_module_path = crate::rust_to_vir::get_root_module_path(ctxt);

    let mut visitor = VisitMod {
        items: vec![],
        ctxt: ctxt,
        state: default_state,
        module_path: Some(root_module_path),
        errors: vec![],
        in_impl: None,
    };
    let owner = ctxt.tcx.hir_owner_node(rustc_hir::CRATE_OWNER_ID);
    visitor.visit_mod(root_module, owner.span(), rustc_hir::CRATE_HIR_ID);

    if visitor.errors.len() > 0 {
        return Err(visitor.errors[0].clone());
    }

    let mut map = HashMap::<OwnerId, VerifOrExternal>::new();
    for crate_item in visitor.items.iter() {
        let owner_id = crate_item.id.owner_id();
        let old = map.insert(owner_id, crate_item.verif.clone());
        assert!(old.is_none());
    }

    Ok(CrateItems { items: visitor.items, map })
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum VerifState {
    /// This is what the root module is unless it's overridden. Nothing has been
    /// marked either 'external' or 'verify'
    Default,
    /// We're in a context that has been marked 'verify'
    Verify,
    /// We're in a context that has been marked 'external'
    /// (This is a terminal state - we can never get out of it.)
    External,
}

// Information about the impl, used when visitings its ImplItems.
#[derive(Copy, Clone)]
struct InsideImpl {
    is_trait: bool,
    has_any_verus_aware_item: bool,
}

struct VisitMod<'a, 'tcx> {
    items: Vec<CrateItem>,
    ctxt: &'a ContextX<'tcx>,
    errors: Vec<VirErr>,

    state: VerifState,
    module_path: Option<Path>,
    in_impl: Option<InsideImpl>,
}

impl<'a, 'tcx> rustc_hir::intravisit::Visitor<'tcx> for VisitMod<'a, 'tcx> {
    // Configure the visitor for nested visits
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        self.visit_general(GeneralItem::Item(item), item.hir_id(), item.span);
    }

    fn visit_foreign_item(&mut self, item: &'tcx ForeignItem<'tcx>) {
        self.visit_general(GeneralItem::ForeignItem(item), item.hir_id(), item.span);
    }

    fn visit_impl_item(&mut self, item: &'tcx ImplItem<'tcx>) {
        self.visit_general(GeneralItem::ImplItem(item), item.hir_id(), item.span);
    }

    fn visit_trait_item(&mut self, item: &'tcx TraitItem<'tcx>) {
        self.visit_general(GeneralItem::TraitItem(item), item.hir_id(), item.span);
    }

    fn maybe_tcx(&mut self) -> rustc_middle::ty::TyCtxt<'tcx> {
        self.ctxt.tcx
    }
}

fn opts_in_to_verus(eattrs: &ExternalAttrs) -> bool {
    eattrs.verify
        || eattrs.verus_macro
        || eattrs.external_body
        || eattrs.external_fn_specification
        || eattrs.external_type_specification
        || eattrs.external_trait_specification
        || eattrs.sets_mode
        || eattrs.size_of_global
}

impl<'a, 'tcx> VisitMod<'a, 'tcx> {
    fn visit_general(&mut self, general_item: GeneralItem<'tcx>, hir_id: HirId, span: Span) {
        let attrs = self.ctxt.tcx.hir_attrs(hir_id);

        let eattrs = match self.ctxt.get_external_attrs(attrs) {
            Ok(eattrs) => eattrs,
            Err(err) => {
                self.errors.push(err);
                return;
            }
        };

        let owner_id = hir_id.expect_owner();
        let def_id = owner_id.to_def_id();

        {
            emit_errors_warnings_for_ignored_attrs(
                self.ctxt,
                self.state,
                &eattrs,
                &mut *self.ctxt.diagnostics.borrow_mut(),
                &mut self.errors,
                span,
            );
        }

        // Compute the VerifState of this particular item based on its context
        // and its attributes.

        let my_eattrs = eattrs.clone();

        let auto_derive_eattrs =
            get_attributes_for_automatic_derive(&self.ctxt, &general_item, attrs, span);
        let eattrs = if let Some(auto_derive_eattrs) = auto_derive_eattrs {
            auto_derive_eattrs
        } else {
            my_eattrs.clone()
        };

        let state_for_this_item = match self.state {
            VerifState::Default => {
                if eattrs.external {
                    VerifState::External
                } else if opts_in_to_verus(&eattrs) {
                    VerifState::Verify
                } else {
                    VerifState::Default
                }
            }
            VerifState::Verify => {
                if eattrs.external {
                    VerifState::External
                } else {
                    VerifState::Verify
                }
            }
            VerifState::External => VerifState::External,
        };

        if matches!(general_item, GeneralItem::ImplItem(_)) && self.in_impl.is_none() {
            self.errors.push(crate::util::err_span_bare(
                span,
                "Verus internal error: expected ImplItem to be child of Impl",
            ));
            return;
        }

        // Error if any item of a trait or trait impl is ignored.

        if matches!(general_item, GeneralItem::ImplItem(_))
            && self.in_impl.as_ref().unwrap().is_trait
            && self.state == VerifState::Verify
            && state_for_this_item == VerifState::External
        {
            self.errors.push(crate::util::err_span_bare(
                span,
                "An individual item of a trait impl cannot be marked external. Perhaps you meant to mark the entire trait impl external, or you meant to mark this item as `external_body`?",
              ));
            return;
        }
        if matches!(general_item, GeneralItem::TraitItem(_))
            && self.state == VerifState::Verify
            && state_for_this_item == VerifState::External
        {
            self.errors.push(crate::util::err_span_bare(
                span,
                "An individual item of a trait cannot be marked external. Perhaps you meant to mark the entire trait external?",
              ));
            return;
        }

        if matches!(general_item, GeneralItem::ImplItem(_))
            && state_for_this_item == VerifState::Verify
        {
            self.in_impl.as_mut().unwrap().has_any_verus_aware_item = true;
        }

        // Append this item to the items

        let verif = if state_for_this_item == VerifState::Verify {
            if let Some(module_path) = self.module_path.clone() {
                VerifOrExternal::VerusAware {
                    module_path: module_path,
                    const_directive: eattrs.size_of_global || eattrs.item_broadcast_use,
                    external_body: my_eattrs.external_body,
                }
            } else {
                self.errors.push(crate::util::err_span_bare(
                    span,
                    "Verus is unable to compute the path of the module this item is in",
                ));
                return;
            }
        } else {
            let path_opt =
                def_id_to_vir_path_option(self.ctxt.tcx, Some(&self.ctxt.verus_items), def_id);
            let path_string = match &path_opt {
                Some(path) => vir::ast_util::path_as_friendly_rust_name(&path),
                None => format!("{:?}", def_id),
            };
            VerifOrExternal::External {
                path: path_opt,
                path_string,
                explicit: state_for_this_item == VerifState::External,
            }
        };

        self.items.push(CrateItem { id: general_item.id(), verif });
        let this_item_idx = self.items.len() - 1;

        // Compute the context for any _nested_ items

        let state_inside = if my_eattrs.external_body {
            if !general_item.may_have_external_body() {
                self.errors.push(crate::util::err_span_bare(
                    span,
                    "#[verifier::external_body] doesn't make sense for this item type -- it is only applicable to functions and datatype declarations",
                  ));
                return;
            }
            VerifState::External
        } else {
            state_for_this_item
        };

        // Recurse. If entering a module or an impl, update the relevant
        // recursion state.

        let saved_state = self.state;
        let saved_mod = self.module_path.clone();
        let saved_in_impl = self.in_impl;

        self.state = state_inside;
        self.in_impl = None;

        match general_item {
            GeneralItem::Item(item) => match item.kind {
                ItemKind::Mod(_ident, _module) => {
                    self.module_path = def_id_to_vir_path_option(
                        self.ctxt.tcx,
                        Some(&self.ctxt.verus_items),
                        def_id,
                    );
                }
                ItemKind::Impl(impll) => {
                    self.in_impl = Some(InsideImpl {
                        is_trait: impll.of_trait.is_some(),
                        has_any_verus_aware_item: false,
                    });
                }
                ItemKind::Const(_ident, _ty, _generics, _body_id) => {
                    if eattrs.structural_const_wrapper {
                        self.state = VerifState::Verify;
                    }
                }
                _ => {}
            },
            _ => {}
        }

        match general_item {
            GeneralItem::Item(i) => rustc_hir::intravisit::walk_item(self, i),
            GeneralItem::ForeignItem(i) => rustc_hir::intravisit::walk_foreign_item(self, i),
            GeneralItem::ImplItem(i) => rustc_hir::intravisit::walk_impl_item(self, i),
            GeneralItem::TraitItem(i) => rustc_hir::intravisit::walk_trait_item(self, i),
        }

        if let Some(in_impl) = self.in_impl {
            if in_impl.has_any_verus_aware_item && state_for_this_item != VerifState::Verify {
                // Suppose the user writes something like:
                //
                // impl X {
                //     verus!{
                //          fn foo() { ... }
                //     }
                // }
                //
                // We need to make sure 'foo' isn't skipped just because the impl block
                // as a whole isn't marked verify.
                //
                // For _normal impls_, we just go ahead and mark the impl as verification-aware.
                // For _trait impls_, this situation would be too complicated, so we error.

                if in_impl.is_trait {
                    self.errors.push(crate::util::err_span_bare(
                        span,
                    "In order to verify any items of this trait impl, the entire impl must be verified. Try wrapping the entire impl in the `verus!` macro.",
                    ));
                } else {
                    if let Some(module_path) = self.module_path.clone() {
                        self.items[this_item_idx].verif = VerifOrExternal::VerusAware {
                            module_path,
                            const_directive: false,
                            external_body: false,
                        }
                    } else {
                        self.errors.push(crate::util::err_span_bare(
                            span,
                            "Verus is unable to compute the path of the module this item is in",
                        ));
                    }
                }
            }
        }

        self.state = saved_state;
        self.module_path = saved_mod;
        self.in_impl = saved_in_impl;
    }
}

/// Emit warnings and errors from nonsense combinations.
fn emit_errors_warnings_for_ignored_attrs<'tcx>(
    ctxt: &ContextX<'tcx>,
    state: VerifState,
    eattrs: &ExternalAttrs,
    diagnostics: &mut Vec<VirErrAs>,
    errors: &mut Vec<VirErr>,
    span: rustc_span::Span,
) {
    if ctxt.cmd_line_args.vstd == crate::config::Vstd::IsCore {
        // This gives a lot of warnings from the embedding of the 'verus_builtin' crate so ignore it
        return;
    }

    if eattrs.internal_get_field_many_variants {
        // The macro sometimes outputs this attribute together with 'external' for the purpose
        // of some diagnostics. We thus want to ignore it.
        return;
    }

    if eattrs.uses_unerased_proxy {
        return;
    }

    // If an item is external, of if it's in a module that is marked external, then
    // it will be ignored. Therefore, if there's any other verus-relevant attribute,
    // it's probably a mistake.
    //
    // It's a hard-error for external_{fn,type,trait}_specification and a warning for
    // everything else. This inconsistency is mostly for continuity with the legacy behavior,
    // not necessarily for a good reason, so we might revisit it later.
    if eattrs.external || state == VerifState::External {
        if eattrs.external_body {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!("#[verifier::external_body] has no effect because item is already marked external"),
            )));
        } else if eattrs.verify {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!(
                    "#[verifier::verify] has no effect because item is already marked external"
                ),
            )));
        } else if eattrs.external_fn_specification {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!("an `assume_specification` declaration cannot be marked `external`"),
            )));
            if eattrs.external {
                errors.push(crate::util::err_span_bare(
                    span,
                    format!("an `assume_specification` declaration cannot be marked `external`"),
                ));
            }
        } else if eattrs.external_type_specification {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!("#[verifier::external_type_specification] has no effect because item is already marked external"),
            )));
            if eattrs.external {
                errors.push(crate::util::err_span_bare(
                    span,
                    format!(
                        "a type cannot be marked both `external_type_specification` and `external`"
                    ),
                ));
            }
        } else if eattrs.external_trait_specification {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!("#[verifier::external_trait_specification] has no effect because item is already marked external"),
            )));
            if eattrs.external {
                errors.push(crate::util::err_span_bare(
                    span,
                    format!("a trait cannot be marked both `external_trait_specification` and `external`"),
                ));
            }
        } else if eattrs.sets_mode {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!(
                    "verifier mode attribute has no effect because item is already marked external"
                ),
            )));
        //} else if eattrs.verus_macro {
        //diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
        //    span,
        //    format!("The verus macro has no effect because item is already marked external"),
        //)));
        } else if eattrs.any_other_verus_specific_attribute {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!(
                    "verus-related attribute has no effect because item is already marked external"
                ),
            )));
        }
    }

    if state == VerifState::Default && !opts_in_to_verus(&eattrs) {
        if eattrs.any_other_verus_specific_attribute {
            diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                span,
                format!("verus-related attribute has no effect because Verus is already ignoring this item. You may need to mark it as `#[verifier::verify]`."),
            )));
        }
    }
}

impl GeneralItemId {
    pub(crate) fn owner_id(self) -> OwnerId {
        match self {
            GeneralItemId::ItemId(id) => id.owner_id,
            GeneralItemId::ImplItemId(id) => id.owner_id,
            GeneralItemId::ForeignItemId(id) => id.owner_id,
            GeneralItemId::TraitItemId(id) => id.owner_id,
        }
    }
}

impl<'a> GeneralItem<'a> {
    fn id(self) -> GeneralItemId {
        match self {
            GeneralItem::Item(i) => GeneralItemId::ItemId(i.item_id()),
            GeneralItem::ForeignItem(i) => GeneralItemId::ForeignItemId(i.foreign_item_id()),
            GeneralItem::ImplItem(i) => GeneralItemId::ImplItemId(i.impl_item_id()),
            GeneralItem::TraitItem(i) => GeneralItemId::TraitItemId(i.trait_item_id()),
        }
    }

    fn may_have_external_body(self) -> bool {
        match self {
            GeneralItem::Item(i) => match i.kind {
                ItemKind::Fn { .. } => true,
                ItemKind::Struct(..) => true,
                ItemKind::Enum(..) => true,
                ItemKind::Union(..) => true,
                ItemKind::Const(..) => true,
                _ => false,
            },
            GeneralItem::ForeignItem(_) => false,
            GeneralItem::ImplItem(i) => match i.kind {
                ImplItemKind::Fn(..) => true,
                _ => false,
            },
            GeneralItem::TraitItem(i) => match i.kind {
                TraitItemKind::Fn(..) => true,
                _ => false,
            },
        }
    }
}

/// If the user uses a 'derive' trait on a datatype definition, then the
/// autoderived trait impl needs to be handled specially. This is because
/// the autoderived trait impl doesn't 'inherit' all the attributes of the
/// struct; in particular, it doesn't inherit the verus_macro attribute.
/// So when we come across an autoderive struct, we need to check if
/// the *type* has the verus_macro attribute.
///
/// Different traits are handled on a case-by-case basis; see automatic_derive.rs
fn get_attributes_for_automatic_derive<'tcx>(
    ctxt: &ContextX<'tcx>,
    general_item: &GeneralItem<'tcx>,
    attrs: &[rustc_hir::Attribute],
    span: Span,
) -> Option<ExternalAttrs> {
    let warn_unknown = || {
        ctxt.diagnostics.borrow_mut().push(VirErrAs::Warning(crate::util::err_span_bare(
            span,
            format!(
                "Verus doesn't known how to handle this automatically derived item; ignoring it"
            ),
        )));
    };

    if !crate::automatic_derive::is_automatically_derived(attrs) {
        return None;
    }

    match general_item {
        GeneralItem::Item(item) => match &item.kind {
            ItemKind::Impl(impll) => {
                let Some(of_trait) = impll.of_trait else {
                    return None;
                };

                let type_def_id = match impll.self_ty.kind {
                    rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(None, path)) => {
                        path.res.def_id()
                    }
                    _ => {
                        warn_unknown();
                        return None;
                    }
                };
                if let Some(type_local_def_id) = type_def_id.as_local() {
                    let type_hir_id = ctxt.tcx.local_def_id_to_hir_id(type_local_def_id);
                    let type_attrs = ctxt.tcx.hir_attrs(type_hir_id);
                    let mut type_eattrs = match ctxt.get_external_attrs(type_attrs) {
                        Ok(eattrs) => eattrs,
                        Err(_) => {
                            warn_unknown();
                            return None;
                        }
                    };

                    if match &type_eattrs.external_auto_derives {
                        crate::attributes::AutoDerivesAttr::Regular => false,
                        crate::attributes::AutoDerivesAttr::AllExternal => true,
                        crate::attributes::AutoDerivesAttr::SomeExternal(names) => {
                            let def_path = ctxt.tcx.def_path(of_trait.trait_ref.path.res.def_id());
                            def_path
                                .data
                                .last()
                                .map(|seg| {
                                    names.iter().any(|d| {
                                        use rustc_hir::definitions::DefPathData;
                                        match &seg.data {
                                            DefPathData::ValueNs(symbol)
                                            | DefPathData::TypeNs(symbol) => {
                                                symbol.to_string().contains(d)
                                            }
                                            _ => true,
                                        }
                                    })
                                })
                                .unwrap_or(false)
                        }
                    } {
                        type_eattrs.external = true;
                        return Some(type_eattrs);
                    }

                    if opts_in_to_verus(&type_eattrs) {
                        let trait_def_id = impll.of_trait.unwrap().trait_ref.path.res.def_id();
                        let rust_item = get_rust_item(ctxt.tcx, trait_def_id);
                        let action = crate::automatic_derive::get_action(rust_item);
                        match action {
                            AutomaticDeriveAction::Special(_)
                            | AutomaticDeriveAction::VerifyAsIs => Some(type_eattrs),
                            AutomaticDeriveAction::Ignore => {
                                type_eattrs.external = true;
                                Some(type_eattrs)
                            }
                        }
                    } else {
                        None
                    }
                } else {
                    warn_unknown();
                    None
                }
            }
            _ => {
                warn_unknown();
                None
            }
        },
        _ => {
            warn_unknown();
            None
        }
    }
}
