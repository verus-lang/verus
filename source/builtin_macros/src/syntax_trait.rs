use crate::syntax::{VERUS_SPEC, mk_rust_attr, mk_rust_attr_syn, mk_verus_attr};
use quote::{quote, quote_spanned};
use verus_syn::spanned::Spanned;
use verus_syn::{
    Expr, FnMode, Ident, ImplItem, ImplItemFn, Item, ItemImpl, ItemTrait, Meta, Path, Stmt, Token,
    TraitItem, TraitItemFn, Type, TypeParamBound, Visibility,
};
use verus_syn::{TraitBound, parse_quote_spanned};

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
    let mut generics = tr.generics.clone();
    for param in &mut generics.params {
        use verus_syn::GenericParam;
        match param {
            GenericParam::Lifetime(_) => {}
            GenericParam::Type(p) => {
                p.eq_token = None;
                p.default = None;
            }
            GenericParam::Const(p) => {
                p.eq_token = None;
                p.default = None;
            }
        }
    }
    ItemImpl {
        attrs: Vec::new(),
        defaultness: None,
        unsafety: None,
        impl_token: Token![impl](span),
        generics,
        trait_: Some((None, parse_quote_spanned!(span => #tr_spec), Token![for](span))),
        self_ty,
        brace_token: tr.brace_token,
        items: Vec::new(),
    }
}

/*
Given:
    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(TSpec via TSpecImpl)]
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
    trait TSpecImpl: T {
        // omitted for erase_all
        fn s1(...) -> ...;
        ...
        // omitted for erase_all
        fn sn(...) -> ...;
    }
    #[verus::internal(external_trait_blanket)]
    impl<A: T + <size bound of T>> TSpec for A {
        // omitted for erase_all
        #[verifier::external_body]
        fn s1(...) -> ... { panic!() }
        ...
        // omitted for erase_all
        #[verifier::external_body]
        fn sn(...) -> ... { panic!() }
    }
Note: these generated items are trusted;
the code here that generates them is part of the trusted computing base.
*/
fn expand_extension_trait<'tcx>(
    erase_all: bool,
    new_items: &mut Vec<Item>,
    t: &Path,
    tr: &ItemTrait,
    tr_spec: &Ident,
    tr_impl: &Ident,
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
                    attrs: vec![parse_quote_spanned!(span => #[verifier::external_body])],
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

    let mut tspec_impl = new_trait_from(tr, tr_impl.clone());
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
        use verus_syn::PathArguments;
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
    blanket_impl.attrs.push(mk_verus_attr(span, quote_spanned!(span => external_trait_blanket)));
    blanket_impl.attrs.push(mk_rust_attr(
        span,
        "allow",
        quote_spanned!(span => non_camel_case_types),
    ));
    let blanket_bound: TypeParamBound = {
        tr.supertraits.iter().find(|tpb| is_sizedness_bound(tpb)).cloned().unwrap_or_else(|| {
            let span = tr.generics.span();
            parse_quote_spanned!(span => core::marker::MetaSized)
        })
    };
    blanket_impl.generics.params.push(parse_quote_spanned!(span => #self_x: #t + #blanket_bound));
    blanket_impl.items = blanket_impl_items;

    new_items.push(Item::Trait(tspec));
    new_items.push(Item::Trait(tspec_impl));
    new_items.push(Item::Impl(blanket_impl));
}

/// Heuristically determines whether `tp` is a Size-related bound.  We cannot do
/// this correctly in a macro since identifiers are not yet resolved and traits
/// may be renamed when imported. However, this should be sufficiently rare in
/// practice, so we ignore this issue here. Otherwise, the user would have to
/// provide the external_trait_extension macro with an additional parameter.
fn is_sizedness_bound(tp: &TypeParamBound) -> bool {
    match tp {
        TypeParamBound::Trait(TraitBound { path, .. }) => {
            let last_segment = path.segments.last().unwrap().ident.to_string();
            ["Sized", "MetaSized", "PointeeSized"].contains(&last_segment.as_str())
        }
        _ => false,
    }
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
                #[allow(clippy::cmp_owned)] // There is no other way to compare an Ident
                let is_external_trait_extension = attr.path().segments.len() == 2
                    && attr.path().segments[0].ident.to_string() == "verifier"
                    && attr.path().segments[1].ident.to_string() == "external_trait_extension";
                if is_external_trait_extension {
                    if let Meta::List(list) = &attr.meta {
                        let tokens: Vec<_> = list.tokens.clone().into_iter().collect();
                        use proc_macro2::TokenTree;
                        match (&t, tokens.as_slice()) {
                            #[allow(clippy::cmp_owned)] // There is no other way to compare an Ident
                            (
                                Some(t),
                                [TokenTree::Ident(s), TokenTree::Ident(via), TokenTree::Ident(i)],
                            ) if via.to_string() == "via" => {
                                expand_extension_trait(erase_all, &mut new_items, t, tr, s, i);
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }
    items.extend(new_items);
}

macro_rules! do_split_trait_method {
    ($s:ident, $fun:ident, $spec_fun:ident, $mk_rust_attr:ident, $recv:ident, $pred:ident) => {
        let mut $spec_fun = $fun.clone();
        let x = &$fun.sig.ident;
        let span = x.span();
        $spec_fun.sig.ident = $s::Ident::new(&format!("{VERUS_SPEC}{x}"), span);
        $spec_fun.attrs.push($mk_rust_attr(span, "doc", quote! { hidden }));
        // Some traits, like core::ops::Add, declare functions whose parameters or return values
        // aren't guaranteed to be Sized.  This is allowed when the function has no default
        // (provided) body, but disallowed when there is a default body, so we may get an error
        // when we create $spec_fun here.  Ideally, we could just add :Sized bounds to all
        // the parameter and return types, but this is easier said than done, since types like
        // "&u8" need to be turned into something like "&'a u8" to be used in a bound.
        // For now, just handle the special case of a "self" parameter, which needs Self: Sized.
        if let Some(recv) = $recv {
            if recv.colon_token.is_none() && recv.reference.is_none() {
                $spec_fun.sig.generics.make_where_clause().predicates.push($pred);
            }
        }
    };
}

// In addition to prefiltering ghost code, we also split methods declarations
// into separate spec and implementation declarations.  For example:
//   fn f() requires x;
// becomes
//   fn VERUS_SPEC__f() requires x;
//   fn f();
// In a later pass, this becomes:
//   fn VERUS_SPEC__f() { requires(x); ... }
//   fn f();
// Note: we don't do this if there's a default body,
// because it turns out that the parameter names
// don't exactly match between fun and fun.clone() (they have different macro contexts),
// which would cause the body and specs to mismatch.
// (See also split_trait_method_syn below.)
pub(crate) fn split_trait_method(
    spec_items: &mut Vec<TraitItem>,
    fun: &mut TraitItemFn,
    erase_ghost: bool,
) {
    if !erase_ghost && fun.default.is_none() {
        // Copy into separate spec method, then remove spec from original method
        use verus_syn::FnArgKind;
        let recv = fun.sig.inputs.first().and_then(|a| match &a.kind {
            FnArgKind::Receiver(r) => Some(r),
            _ => None,
        });
        let pred = parse_quote_spanned!(fun.sig.ident.span() => Self: core::marker::Sized);
        do_split_trait_method!(verus_syn, fun, spec_fun, mk_rust_attr, recv, pred);
        spec_items.push(TraitItem::Fn(spec_fun));
        fun.sig.erase_spec_fields();
    } else if erase_ghost {
        match (&mut fun.default, &fun.sig.mode) {
            (
                Some(default),
                FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_),
            ) => {
                // replace body with panic!()
                let span = default.span();
                let expr: Expr = Expr::Verbatim(quote_spanned! {
                    span => { panic!() }
                });
                let stmt = Stmt::Expr(expr, None);
                default.stmts = vec![stmt];
            }
            _ => {}
        }
    }
}

// syn version of split_trait_method (see above)
// (Note: there are no spec fields to erase in syn; the spec attribute must be erased separately.)
pub(crate) fn split_trait_method_syn(
    fun: &syn::TraitItemFn,
    erase_ghost: bool,
) -> Option<syn::TraitItemFn> {
    use syn::{Block, Expr, Stmt, token::Brace};
    if !erase_ghost && fun.default.is_none() {
        use syn::FnArg;
        let recv = fun.sig.inputs.first().and_then(|a| match a {
            FnArg::Receiver(r) => Some(r),
            _ => None,
        });
        let pred = syn::parse_quote_spanned!(fun.sig.ident.span() => Self: core::marker::Sized);
        do_split_trait_method!(syn, fun, spec_fun, mk_rust_attr_syn, recv, pred);
        // We won't run visit_trait_item_fn_mut, so we need to add no_method_body here:
        let span = fun.sig.fn_token.span;
        let stmts = vec![Stmt::Expr(
            Expr::Verbatim(
                quote_spanned_builtin!(verus_builtin, span => #verus_builtin::no_method_body()),
            ),
            None,
        )];
        spec_fun.default = Some(Block { brace_token: Brace(span), stmts });
        Some(spec_fun)
    } else {
        // Note: we only support exec functions via syn; there is no fun.sig.mode here
        // So there's no case for spec, proof as in split_trait_method above
        None
    }
}
