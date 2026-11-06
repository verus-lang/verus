//! Compiler-style erasure for generated code, sharing the actual macro visitor.
use proc_macro2::TokenStream;
use quote::quote;
use verus_syn::visit_mut::{self, VisitMut};
use verus_syn::{ImplItem, Item};

use crate::source_erase::{has_ghost_cfg, is_item_wrapper_name, macro_name};
use crate::syntax::{ImplItems, Items};

pub fn expand_struct(input: TokenStream) -> verus_syn::Result<TokenStream> {
    erase_generated(crate::struct_decl_inv::expand(input)?)
}

pub fn expand_atomic(input: TokenStream) -> verus_syn::Result<TokenStream> {
    // The public macro_rules wrapper supplies this path to the proc-macro.
    // Exec-only expansion does not use it.
    crate::atomic_ghost::expand(quote! { ::vstd::atomic_ghost::atomic_with_ghost_inner, #input })
}

/// Erase generated items as normal rustc does, including their nested wrappers.
pub fn erase_generated(input: TokenStream) -> verus_syn::Result<TokenStream> {
    let mut items: Items = verus_syn::parse2(input)?;
    let mut unwrap = Unwrap { error: None };
    unwrap.items(&mut items.items);
    if let Some(error) = unwrap.error {
        return Err(error);
    }
    Ok(crate::syntax::rewrite_items_tokens(&mut items.items, crate::EraseGhost::EraseAll, false))
}

struct Unwrap {
    error: Option<verus_syn::Error>,
}

fn generated_macro_name(path: &verus_syn::Path) -> Option<&verus_syn::Ident> {
    macro_name(path).or_else(|| {
        // The *_vstd generator uses crate::prelude instead of ::vstd::prelude.
        // Recognize that path only in generated code, leaving caller macros
        // in other namespaces opaque.
        let mut segments = path.segments.iter();
        match (segments.next(), segments.next(), segments.next(), segments.next()) {
            (Some(root), Some(prelude), Some(name), None)
                if root.ident == "crate" && prelude.ident == "prelude" =>
            {
                Some(&name.ident)
            }
            _ => None,
        }
    })
}

impl Unwrap {
    fn items(&mut self, items: &mut Vec<Item>) {
        let mut output = Vec::new();
        for mut item in std::mem::take(items) {
            if has_ghost_cfg(&item, true) {
                continue;
            }
            if let Item::Macro(mac) = &item {
                if generated_macro_name(&mac.mac.path)
                    .is_some_and(|name| is_item_wrapper_name(&name.to_string()))
                {
                    match verus_syn::parse2::<Items>(mac.mac.tokens.clone()) {
                        Ok(mut inner) => {
                            self.items(&mut inner.items);
                            output.extend(inner.items);
                        }
                        Err(error) => self.error = Some(error),
                    }
                    continue;
                }
            }
            self.visit_item_mut(&mut item);
            output.push(item);
        }
        *items = output;
    }

    fn impl_items(&mut self, items: &mut Vec<ImplItem>) {
        let mut output = Vec::new();
        for mut item in std::mem::take(items) {
            if has_ghost_cfg(&item, true) {
                continue;
            }
            if let ImplItem::Macro(mac) = &item {
                if generated_macro_name(&mac.mac.path)
                    .is_some_and(|name| is_item_wrapper_name(&name.to_string()))
                {
                    match verus_syn::parse2::<ImplItems>(mac.mac.tokens.clone()) {
                        Ok(mut inner) => {
                            self.impl_items(&mut inner.items);
                            output.extend(inner.items);
                        }
                        Err(error) => self.error = Some(error),
                    }
                    continue;
                }
            }
            self.visit_impl_item_mut(&mut item);
            output.push(item);
        }
        *items = output;
    }
}

impl VisitMut for Unwrap {
    fn visit_item_mod_mut(&mut self, item: &mut verus_syn::ItemMod) {
        if let Some((_, items)) = &mut item.content {
            self.items(items);
        }
    }

    fn visit_item_impl_mut(&mut self, item: &mut verus_syn::ItemImpl) {
        self.impl_items(&mut item.items);
    }

    fn visit_block_mut(&mut self, block: &mut verus_syn::Block) {
        block.stmts.retain(|stmt| !has_ghost_cfg(stmt, true));
        visit_mut::visit_block_mut(self, block);
    }
}
