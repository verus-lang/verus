use crate::syntax::{VERUS_SPEC, mk_rust_attr, mk_verus_attr};
use quote::quote_spanned;
use syn_verus::parse_quote_spanned;
use syn_verus::{
    FnMode, Ident, ImplItem, ImplItemFn, Item, ItemImpl, ItemTrait, Meta, Path, Token, TraitItem,
    Type, TypeParamBound, Visibility,
};

fn new_trait_from(tr: &ItemTrait, ident: Ident) -> ItemTrait {
    ItemTrait {
        attrs: Vec::new(),
        vis: tr.vis.clone(),
        unsafety: None,
        auto_token: None,
        restriction: None,
        trait_token: tr.trait_token,
        ident,
        generics: tr.generics.clone(),
        colon_token: tr.colon_token,
        supertraits: tr.supertraits.clone(),
        brace_token: tr.brace_token,
        items: Vec::new(),
    }
}

fn new_impl_for_trait(tr: &ItemTrait, tr_spec: &Path, self_ty: Box<Type>) -> ItemImpl {
    let t = &tr.ident;
    let span = t.span();
    ItemImpl {
        attrs: Vec::new(),
        defaultness: None,
        unsafety: None,
        impl_token: Token![impl](span),
        generics: tr.generics.clone(),
        trait_: Some((None, parse_quote_spanned!(span => #tr_spec), Token![for](span))),
        self_ty,
        brace_token: tr.brace_token,
        items: Vec::new(),
    }
}

/*
Given:
    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(TSpec)]
    trait Ex {
        type ExternalTraitSpecificationFor: T;
        ...
        spec fn s1(...) -> ...;
        ...
        spec fn sn(...) -> ...;
    }
Generate additional items:
    trait TSpec: T {
        // omitted for erase_all
        spec fn s1(...) -> ...;
        ...
        // omitted for erase_all
        spec fn sn(...) -> ...;
    }
    #[verifier::external]
    #[allow(non_camel_case_types)]
    trait VERUS_SPEC__TSpec: T {
        // omitted for erase_all
        fn s1(...) -> ...;
        ...
        // omitted for erase_all
        fn sn(...) -> ...;
    }
    #[verifier::external]
    #[verus::internal(external_trait_blanket)]
    impl<A: T + ?Sized> TSpec for A {
        // omitted for erase_all
        fn s1(...) -> ... { panic!() }
        ...
        // omitted for erase_all
        fn sn(...) -> ... { panic!() }
    }
Note: these generated items are trusted;
the code here that generates them is part of the trusted computing base.
*/
fn expand_extension_trait(
    erase_all: bool,
    new_items: &mut Vec<Item>,
    t: &Path,
    tr: &ItemTrait,
    tr_spec: Ident,
) {
    let mut tspec_items: Vec<TraitItem> = Vec::new();
    let mut tspec_impl_items: Vec<TraitItem> = Vec::new();
    let mut blanket_impl_items: Vec<ImplItem> = Vec::new();
    for item in &tr.items {
        if let TraitItem::Fn(f) = item {
            if !erase_all && matches!(f.sig.mode, FnMode::Spec(..)) {
                let span = f.sig.ident.span();
                let mut f_tspec = f.clone();
                let mut f_tspec_impl = f.clone();
                let mut f_blanket = ImplItemFn {
                    attrs: vec![],
                    vis: Visibility::Inherited,
                    defaultness: None,
                    sig: f.sig.clone(),
                    block: parse_quote_spanned!(span => { panic!() }),
                    semi_token: f.semi_token,
                };
                // TODO: when we support defaults, we might want to copy/move f's default body:
                f_tspec.default = None;
                f_tspec_impl.default = None;
                f_tspec_impl.sig.mode = FnMode::Default;
                f_blanket.sig.mode = FnMode::Default;
                tspec_items.push(TraitItem::Fn(f_tspec));
                tspec_impl_items.push(TraitItem::Fn(f_tspec_impl));
                blanket_impl_items.push(ImplItem::Fn(f_blanket));
            }
        }
    }
    let span = tr.ident.span();

    let mut tspec = new_trait_from(tr, tr_spec.clone());
    tspec.supertraits.push(parse_quote_spanned!(span => #t));
    tspec.items = tspec_items;

    let mut tspec_impl = new_trait_from(tr, Ident::new(&format!("{VERUS_SPEC}{tr_spec}"), span));
    tspec_impl.attrs.push(parse_quote_spanned!(span => #[verifier::external]));
    tspec_impl.attrs.push(mk_rust_attr(
        span,
        "allow",
        quote_spanned!(span => non_camel_case_types),
    ));
    tspec_impl.supertraits.push(parse_quote_spanned!(span => #t));
    tspec_impl.items = tspec_impl_items;

    let self_x = Ident::new(&format!("{VERUS_SPEC}A"), span);
    let self_ty = parse_quote_spanned!(span => #self_x);
    let tr_spec_path = if let Some(last) = t.segments.last() {
        use syn_verus::PathArguments;
        if let PathArguments::AngleBracketed(args) = &last.arguments {
            let args = &args.args;
            parse_quote_spanned!(span => #tr_spec<#args>)
        } else {
            parse_quote_spanned!(span => #tr_spec)
        }
    } else {
        parse_quote_spanned!(span => #tr_spec)
    };
    let mut blanket_impl = new_impl_for_trait(tr, &tr_spec_path, self_ty);
    blanket_impl.attrs.push(parse_quote_spanned!(span => #[verifier::external]));
    blanket_impl.attrs.push(mk_verus_attr(span, quote_spanned!(span => external_trait_blanket)));
    blanket_impl.attrs.push(mk_rust_attr(
        span,
        "allow",
        quote_spanned!(span => non_camel_case_types),
    ));
    blanket_impl.generics.params.push(parse_quote_spanned!(span => #self_x: #t + ?Sized));
    blanket_impl.items = blanket_impl_items;

    new_items.push(Item::Trait(tspec));
    new_items.push(Item::Trait(tspec_impl));
    new_items.push(Item::Impl(blanket_impl));
}

pub(crate) fn expand_extension_traits(erase_all: bool, items: &mut Vec<Item>) {
    let mut new_items: Vec<Item> = Vec::new();
    for item in items.iter() {
        if let Item::Trait(tr) = item {
            let mut t: Option<Path> = None;
            for ti in &tr.items {
                if let TraitItem::Type(tt) = ti {
                    if &tt.ident.to_string() == "ExternalTraitSpecificationFor" {
                        if tt.bounds.len() == 1 {
                            if let TypeParamBound::Trait(tr_t) = &&tt.bounds[0] {
                                t = Some(tr_t.path.clone());
                            }
                        }
                    }
                }
            }
            for attr in &tr.attrs {
                let is_external_trait_extension = attr.path().segments.len() == 2
                    && attr.path().segments[0].ident.to_string() == "verifier"
                    && attr.path().segments[1].ident.to_string() == "external_trait_extension";
                if is_external_trait_extension {
                    if let Meta::List(list) = &attr.meta {
                        if let Ok(tr_spec) = syn_verus::parse2::<Ident>(list.tokens.clone()) {
                            if let Some(t) = &t {
                                expand_extension_trait(erase_all, &mut new_items, t, tr, tr_spec);
                            }
                        }
                    }
                }
            }
        }
    }
    items.extend(new_items);
}

/*
Change:
    #[verifier::external_trait_extension]
    impl TSpec for ... { ... }
To:
    #[verifier::external_trait_extension]
    impl VERUS_SPEC__TSpec for ... { ... }
*/
pub(crate) fn trait_extension_rewrite_impl(tr: &mut ItemImpl) {
    let is_external_trait_extension_no_args = tr.attrs.iter().any(|attr| {
        matches!(attr.meta, Meta::Path(..))
            && attr.path().segments.len() == 2
            && attr.path().segments[0].ident.to_string() == "verifier"
            && attr.path().segments[1].ident.to_string() == "external_trait_extension"
    });
    if is_external_trait_extension_no_args {
        if let Some((_, path, _)) = &mut tr.trait_ {
            if let Some(segment) = path.segments.last_mut() {
                let x = &mut segment.ident;
                *x = syn_verus::Ident::new(&format!("{VERUS_SPEC}{x}"), x.span());
            }
        }
    }
}
