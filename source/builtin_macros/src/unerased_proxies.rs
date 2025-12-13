/*!
For many items, we need to "split them in two":

 - The erased version of the item, which retains the syntactic item kind, the name, and has
   ghost code erased.

 - The "unerased_proxy", which has a name prefixed with "VERUS_UNERASED_PROXY__",
   is always a function item, and has all the ghost code.

We do this for all 'const' items and 'const fn' items because any const code might be executed
during rustc's type-checking, but we still need a place for all the ghost code to go.

We also do this for 'static' items for consistency with const. Besides the above reason, this
method avoids the need for bespoke signature-encoding mechanisms for consts and statics.

Specifics:

```
const X: u64 = {
   assert(true);
   0
};
```

becomes

```
#[verus::internal(unerased_proxy)]
#[verus::internal(encoded_const)]
fn VERUS_UNERASED_PROXY__X() -> u64 {
   assert(true);
   0
}

#[verifier::external]
#[verus::internal(has_unerased_proxy)]
const X: u64 = { 0 };
```

Statics are similar, but use the `unerased_static` attribute.

Likewise `const fn` items get split in two:

```
const fn x(t: u64): u64 = {
    assert(true);
    x
}
```

becomes

```
#[verus::internal(unerased_proxy)]
fn VERUS_UNERASED_PROXY__x(t: u64): u64 = {
    assert(true);
    x
}

#[verifier::external]
#[verus::internal(has_unerased_proxy)]
const fn x(t: u64): u64 = {
    x
}
```
*/

use crate::EraseGhost;
use crate::syntax::{into_spans, is_external, mk_verifier_attr, mk_verus_attr};
use quote::{quote, quote_spanned};
use verus_syn::punctuated::Punctuated;
use verus_syn::spanned::Spanned;
use verus_syn::token::{Brace, Paren};
use verus_syn::visit_mut::VisitMut;
use verus_syn::*;

pub(crate) const VERUS_UNERASED_PROXY: &str = "VERUS_UNERASED_PROXY__";

impl crate::syntax::Visitor {
    fn needs_unerased_proxies(&self) -> bool {
        self.erase_ghost.keep() && !self.rustdoc
    }

    // There's a lot of duplicated code here because we need to handle both Items and ImplItems.
    // Unfortunately, trying to do it once generically is probably as much of a pain as just
    // duplicating the code.

    fn item_needs_unerased_proxy(&self, item: &Item) -> bool {
        match item {
            Item::Const(item_const) => !is_external(&item_const.attrs),
            Item::Static(item_static) => !is_external(&item_static.attrs),
            Item::Fn(item_fn) => item_fn.sig.constness.is_some() && !is_external(&item_fn.attrs),
            _ => false,
        }
    }

    fn impl_item_needs_unerased_proxy(&self, impl_item: &ImplItem) -> bool {
        match impl_item {
            ImplItem::Const(impl_item_const) => !is_external(&impl_item_const.attrs),
            ImplItem::Fn(impl_item_fn) => {
                impl_item_fn.sig.constness.is_some() && !is_external(&impl_item_fn.attrs)
            }
            _ => false,
        }
    }

    fn item_translate_const_to_0_arg_fn(&self, item: Item) -> Item {
        match item {
            Item::Const(item_const) => {
                let span = item_const.span();
                let ItemConst {
                    mut attrs,
                    vis,
                    const_token,
                    ident,
                    generics,
                    colon_token,
                    ty,
                    eq_token: _,
                    expr,
                    semi_token: _,
                    publish,
                    mode,
                    ensures,
                    block,
                } = item_const;
                attrs.push(mk_verus_attr(span, quote! { encoded_const }));

                let publish = match (publish, &mode, &vis) {
                    (publish, _, Visibility::Inherited) => publish,
                    (
                        Publish::Default,
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Default,
                        _,
                    ) => Publish::Open(verus_syn::Open { token: token::Open { span } }),
                    (publish, _, _) => publish,
                };

                Item::Fn(ItemFn {
                    attrs,
                    vis,
                    sig: Signature {
                        spec: SignatureSpec {
                            prover: None,
                            requires: None,
                            recommends: None,
                            ensures,
                            default_ensures: None,
                            returns: None,
                            decreases: None,
                            invariants: None,
                            unwind: None,
                            with: None,
                        },
                        publish,
                        constness: None,
                        asyncness: None,
                        unsafety: None,
                        abi: None,
                        broadcast: None,
                        mode: mode,
                        fn_token: token::Fn { span: const_token.span },
                        ident: ident.clone(),
                        generics,
                        paren_token: Paren { span: into_spans(colon_token.span) },
                        inputs: Punctuated::new(),
                        variadic: None,
                        output: ReturnType::Type(
                            token::RArrow { spans: [colon_token.span, colon_token.span] },
                            None,
                            None,
                            ty,
                        ),
                    },
                    block: (match block {
                        Some(block) => block,
                        _ => {
                            let expr = expr.unwrap();
                            Box::new(Block {
                                brace_token: Brace { span: into_spans(expr.span()) },
                                stmts: vec![Stmt::Expr(*expr, None)],
                            })
                        }
                    }),
                    semi_token: None,
                })
            }
            Item::Static(item_static) => {
                let span = item_static.span();
                let ItemStatic {
                    mut attrs,
                    vis,
                    static_token,
                    ident,
                    mutability,
                    colon_token,
                    ty,
                    eq_token: _,
                    expr,
                    semi_token: _,
                    publish,
                    mode,
                    ensures,
                    block,
                } = item_static;

                match mutability {
                    StaticMutability::Mut(_) => {
                        return Item::Verbatim(
                            quote_spanned!(span => const _: () = { compile_error!("Verus does not support 'static mut'") };),
                        );
                    }
                    _ => {}
                }

                attrs.push(mk_verus_attr(span, quote! { encoded_static }));

                let publish = match (publish, &mode, &vis) {
                    (publish, _, Visibility::Inherited) => publish,
                    (
                        Publish::Default,
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Default,
                        _,
                    ) => Publish::Open(verus_syn::Open { token: token::Open { span } }),
                    (publish, _, _) => publish,
                };

                Item::Fn(ItemFn {
                    attrs,
                    vis,
                    sig: Signature {
                        spec: SignatureSpec {
                            prover: None,
                            requires: None,
                            recommends: None,
                            ensures,
                            default_ensures: None,
                            returns: None,
                            decreases: None,
                            invariants: None,
                            unwind: None,
                            with: None,
                        },
                        publish,
                        constness: None,
                        asyncness: None,
                        unsafety: None,
                        abi: None,
                        broadcast: None,
                        mode: mode,
                        fn_token: token::Fn { span: static_token.span },
                        ident: ident.clone(),
                        generics: Generics {
                            lt_token: None,
                            params: Punctuated::new(),
                            gt_token: None,
                            where_clause: None,
                        },
                        paren_token: Paren { span: into_spans(colon_token.span) },
                        inputs: Punctuated::new(),
                        variadic: None,
                        output: ReturnType::Type(
                            token::RArrow { spans: [colon_token.span, colon_token.span] },
                            None,
                            None,
                            ty,
                        ),
                    },
                    block: (match block {
                        Some(block) => block,
                        _ => {
                            let expr = expr.unwrap();
                            Box::new(Block {
                                brace_token: Brace { span: into_spans(expr.span()) },
                                stmts: vec![Stmt::Expr(*expr, None)],
                            })
                        }
                    }),
                    semi_token: None,
                })
            }
            item => item,
        }
    }

    fn impl_item_translate_const_to_0_arg_fn(&self, impl_item: ImplItem) -> ImplItem {
        match impl_item {
            ImplItem::Const(impl_item_const) => {
                let span = impl_item_const.span();
                let ImplItemConst {
                    mut attrs,
                    vis,
                    const_token,
                    ident,
                    generics,
                    colon_token,
                    ty,
                    eq_token: _,
                    expr,
                    semi_token: _,
                    publish,
                    mode,
                    ensures,
                    block,
                    defaultness,
                } = impl_item_const;
                attrs.push(mk_verus_attr(span, quote! { encoded_const }));

                let publish = match (publish, &mode, &vis) {
                    (publish, _, Visibility::Inherited) => publish,
                    (
                        Publish::Default,
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Default,
                        _,
                    ) => Publish::Open(verus_syn::Open { token: token::Open { span } }),
                    (publish, _, _) => publish,
                };

                ImplItem::Fn(ImplItemFn {
                    attrs,
                    vis,
                    sig: Signature {
                        spec: SignatureSpec {
                            prover: None,
                            requires: None,
                            recommends: None,
                            ensures,
                            default_ensures: None,
                            returns: None,
                            decreases: None,
                            invariants: None,
                            unwind: None,
                            with: None,
                        },
                        publish,
                        constness: None,
                        asyncness: None,
                        unsafety: None,
                        abi: None,
                        broadcast: None,
                        mode: mode,
                        fn_token: token::Fn { span: const_token.span },
                        ident: ident.clone(),
                        generics,
                        paren_token: Paren { span: into_spans(colon_token.span) },
                        inputs: Punctuated::new(),
                        variadic: None,
                        output: ReturnType::Type(
                            token::RArrow { spans: [colon_token.span, colon_token.span] },
                            None,
                            None,
                            Box::new(ty),
                        ),
                    },
                    block: (match block {
                        Some(block) => *block,
                        _ => {
                            let expr = expr.unwrap();
                            Block {
                                brace_token: Brace { span: into_spans(expr.span()) },
                                stmts: vec![Stmt::Expr(*expr, None)],
                            }
                        }
                    }),
                    defaultness,
                    semi_token: None,
                })
            }
            impl_item => impl_item,
        }
    }

    fn item_make_proxy(&self, item: Item) -> Item {
        let mut item = item;
        item = self.item_translate_const_to_0_arg_fn(item);
        match &mut item {
            Item::Fn(item_fn) => {
                item_fn.sig.ident = Ident::new(
                    &format!("{}{}", VERUS_UNERASED_PROXY, &item_fn.sig.ident),
                    item_fn.sig.span(),
                );
                item_fn.attrs.push(mk_verus_attr(item_fn.span(), quote! { unerased_proxy }));
            }
            Item::Verbatim(_) => {
                // in case item_translate_const_to_0_arg_fn returns compile_error
            }
            _ => unreachable!(),
        }
        item
    }

    fn impl_item_make_proxy(&self, impl_item: ImplItem) -> ImplItem {
        let mut impl_item = impl_item;
        impl_item = self.impl_item_translate_const_to_0_arg_fn(impl_item);
        match &mut impl_item {
            ImplItem::Fn(item_fn) => {
                item_fn.sig.ident = Ident::new(
                    &format!("{}{}", VERUS_UNERASED_PROXY, &item_fn.sig.ident),
                    item_fn.sig.span(),
                );
                item_fn.attrs.push(mk_verus_attr(item_fn.span(), quote! { unerased_proxy }));
            }
            _ => unreachable!(),
        }
        impl_item
    }

    fn attribute_cannot_be_on_two_different_functions(attr: &verus_syn::Attribute) -> bool {
        // An attribute like `#[rustc_diagnostic_item = "Foo"]` isn't allowed to be on two
        // different functions.
        attr.path().is_ident("rustc_diagnostic_item")
    }

    fn item_make_external_and_erased(&mut self, item: Item) -> Item {
        let mut item = item;

        self.erase_ghost = EraseGhost::Erase;
        self.visit_item_mut(&mut item);
        self.erase_ghost = EraseGhost::Keep;

        let span = item.span();
        let attributes = match &mut item {
            Item::Fn(item_fn) => &mut item_fn.attrs,
            Item::Const(item_const) => &mut item_const.attrs,
            Item::Static(item_static) => &mut item_static.attrs,
            _ => unreachable!(),
        };
        // Remove any attributes that can't be on two different
        // functions, like `rustc_diagnostic_item`. Otherwise, there
        // would be a problem because these attributes are also put on
        // the non-erased, proxy version of this function.
        attributes.retain(|attr| !Self::attribute_cannot_be_on_two_different_functions(attr));
        attributes.push(mk_verifier_attr(span, quote! { external }));
        attributes.push(mk_verus_attr(span, quote! { uses_unerased_proxy }));

        item
    }

    fn impl_item_make_external_and_erased(&mut self, impl_item: ImplItem) -> ImplItem {
        let mut impl_item = impl_item;

        self.erase_ghost = EraseGhost::Erase;
        self.visit_impl_item_mut(&mut impl_item);
        self.erase_ghost = EraseGhost::Keep;

        let span = impl_item.span();
        let attributes = match &mut impl_item {
            ImplItem::Fn(item_fn) => &mut item_fn.attrs,
            ImplItem::Const(item_const) => &mut item_const.attrs,
            _ => unreachable!(),
        };
        // Remove any attributes that can't be on two different
        // functions, like `rustc_diagnostic_item`. Otherwise, there
        // would be a problem because these attributes are also put on
        // the non-erased, proxy version of this function.
        attributes.retain(|attr| !Self::attribute_cannot_be_on_two_different_functions(attr));
        attributes.push(mk_verifier_attr(span, quote! { external }));
        attributes.push(mk_verus_attr(span, quote! { uses_unerased_proxy }));

        impl_item
    }

    pub(crate) fn visit_items_make_unerased_proxies(&mut self, items: &mut Vec<Item>) {
        if !self.needs_unerased_proxies() {
            return;
        }

        let mut new_items = vec![];

        for item in std::mem::take(items).into_iter() {
            if self.item_needs_unerased_proxy(&item) {
                let proxy = self.item_make_proxy(item.clone());
                let erased = self.item_make_external_and_erased(item);
                new_items.push(proxy);
                new_items.push(erased);
            } else {
                new_items.push(item);
            }
        }

        *items = new_items;
    }

    pub(crate) fn visit_impl_items_make_unerased_proxies(
        &mut self,
        impl_items: &mut Vec<ImplItem>,
        for_trait: bool,
    ) {
        if !self.needs_unerased_proxies() {
            return;
        }

        let mut new_impl_items = vec![];

        for item in std::mem::take(impl_items).into_iter() {
            if self.impl_item_needs_unerased_proxy(&item) {
                if for_trait {
                    *impl_items = vec![ImplItem::Verbatim(
                        quote_spanned!(item.span() => compile_error!("Verus does not support const items in traits");),
                    )];
                    return;
                }

                let proxy = self.impl_item_make_proxy(item.clone());
                let erased = self.impl_item_make_external_and_erased(item);
                new_impl_items.push(proxy);
                new_impl_items.push(erased);
            } else {
                new_impl_items.push(item);
            }
        }

        *impl_items = new_impl_items;
    }
}
