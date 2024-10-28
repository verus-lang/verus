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

To implement this traversal, we use some rustc visitor machinery to do the recursive
traversal, while keeping track of the current state (Default, Verify, or External).
(The difference between Default and External is that if a module is in the Default state,
then it's nested items can be marked VerusAware, but if it's External, this this is not the case.)
*/

use crate::attributes::ExternalAttrs;
use crate::context::Context;
use crate::rust_to_vir_base::{def_id_to_vir_path, def_id_to_vir_path_option};
use crate::rustc_hir::intravisit::*;
use rustc_hir::{
    ForeignItem, ForeignItemId, HirId, ImplItem, ImplItemId, ImplItemKind, Item, ItemId, ItemKind,
    OwnerId, TraitItem, TraitItemId, TraitItemKind,
};
use rustc_span::Span;
use std::collections::HashMap;
use vir::ast::{Path, VirErr, VirErrAs};

/// Main exported type of this module.
/// Contains all item-things and their categorizations
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

#[derive(Debug, Clone)]
pub enum VerifOrExternal {
    /// Path is the *module path* containing this item
    VerusAware { module_path: Path },
    /// Path/String to refer to this item for diagnostics
    /// Path is an Option because there are some items we can't compute a Path for
    External { path: Option<Path>, path_string: String },
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

pub(crate) fn get_crate_items<'tcx>(ctxt: &Context<'tcx>) -> Result<CrateItems, VirErr> {
    let default_state = if ctxt.cmd_line_args.no_external_by_default {
        VerifState::Verify
    } else {
        VerifState::Default
    };

    let root_module = ctxt.tcx.hir().root_module();
    let root_module_path = crate::rust_to_vir::get_root_module_path(ctxt);

    let mut visitor = VisitMod {
        items: vec![],
        ctxt: ctxt,
        state: default_state,
        module_path: root_module_path,
        errors: vec![],
        is_impl_trait: false,
    };
    let owner = ctxt.tcx.hir().owner(rustc_hir::CRATE_OWNER_ID);
    visitor.visit_mod(root_module, owner.span(), rustc_hir::CRATE_HIR_ID);

    if visitor.errors.len() > 0 {
        return Err(visitor.errors[0].clone());
    }

    let mut map = HashMap::<OwnerId, VerifOrExternal>::new();
    for crate_item in visitor.items.iter() {
        let owner_id = match crate_item.id {
            GeneralItemId::ItemId(id) => id.owner_id,
            GeneralItemId::ImplItemId(id) => id.owner_id,
            GeneralItemId::ForeignItemId(id) => id.owner_id,
            GeneralItemId::TraitItemId(id) => id.owner_id,
        };
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

struct VisitMod<'a, 'tcx> {
    items: Vec<CrateItem>,
    ctxt: &'a Context<'tcx>,
    errors: Vec<VirErr>,

    state: VerifState,
    module_path: Path,
    is_impl_trait: bool,
}

impl<'a, 'tcx> rustc_hir::intravisit::Visitor<'tcx> for VisitMod<'a, 'tcx> {
    // Configure the visitor for nested visits
    type Map = rustc_middle::hir::map::Map<'tcx>;
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.ctxt.tcx.hir()
    }

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
}

fn opts_in_to_verus(eattrs: &ExternalAttrs) -> bool {
    eattrs.verify
        || eattrs.verus_macro
        || eattrs.external_body
        || eattrs.external_fn_specification
        || eattrs.external_type_specification
        || eattrs.external_trait_specification
        || eattrs.sets_mode
}

impl<'a, 'tcx> VisitMod<'a, 'tcx> {
    fn visit_general(&mut self, general_item: GeneralItem<'tcx>, hir_id: HirId, span: Span) {
        let attrs = self.ctxt.tcx.hir().attrs(hir_id);
        let eattrs = match self.ctxt.get_external_attrs(attrs) {
            Ok(eattrs) => eattrs,
            Err(err) => {
                self.errors.push(err);
                return;
            }
        };

        let owner_id = hir_id.expect_owner();
        let def_id = owner_id.to_def_id();

        emit_errors_warnings_for_ignored_attrs(
            self.ctxt,
            self.state,
            &eattrs,
            &mut *self.ctxt.diagnostics.borrow_mut(),
            &mut self.errors,
            span,
        );

        // Compute the VerifState of this particular item based on its context
        // and its attributes.

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

        // Error if any item of a trait or trait impl is ignored.

        if matches!(general_item, GeneralItem::ImplItem(_))
            && self.is_impl_trait
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

        // Append this item to the items

        let verif = if state_for_this_item == VerifState::Verify {
            VerifOrExternal::VerusAware { module_path: self.module_path.clone() }
        } else {
            let path_opt =
                def_id_to_vir_path_option(self.ctxt.tcx, Some(&self.ctxt.verus_items), def_id);
            let path_string = match &path_opt {
                Some(path) => vir::ast_util::path_as_friendly_rust_name(&path),
                None => format!("{:?}", def_id),
            };
            VerifOrExternal::External { path: path_opt, path_string }
        };

        self.items.push(CrateItem { id: general_item.id(), verif });

        // Compute the context for any _nested_ items

        let state_inside = if eattrs.external_body {
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
        let saved_is_impl_trait = self.is_impl_trait;

        self.state = state_inside;

        match general_item {
            GeneralItem::Item(item) => match item.kind {
                ItemKind::Mod(_module) => {
                    self.module_path =
                        def_id_to_vir_path(self.ctxt.tcx, &self.ctxt.verus_items, def_id);
                }
                ItemKind::Impl(impll) => {
                    self.is_impl_trait = impll.of_trait.is_some();
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

        self.state = saved_state;
        self.module_path = saved_mod;
        self.is_impl_trait = saved_is_impl_trait;
    }
}

/// Emit warnings and errors from nonsense combinations.
fn emit_errors_warnings_for_ignored_attrs<'tcx>(
    ctxt: &Context<'tcx>,
    state: VerifState,
    eattrs: &ExternalAttrs,
    diagnostics: &mut Vec<VirErrAs>,
    errors: &mut Vec<VirErr>,
    span: rustc_span::Span,
) {
    if ctxt.cmd_line_args.vstd == crate::config::Vstd::IsCore {
        // This gives a lot of warnings from the embedding of the 'builtin' crate so ignore it
        return;
    }

    if eattrs.internal_get_field_many_variants {
        // The macro sometimes outputs this attribute together with 'external' for the purpose
        // of some diagnostics. We thus want to ignore it.
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
                format!("#[verifier::external_fn_specification] has no effect because item is already marked external"),
            )));
            if eattrs.external {
                errors.push(crate::util::err_span_bare(
                    span,
                    format!("a function cannot be marked both `external_fn_specification` and `external`"),
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
                ItemKind::Fn(..) => true,
                ItemKind::Struct(..) => true,
                ItemKind::Enum(..) => true,
                ItemKind::Union(..) => true,
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
