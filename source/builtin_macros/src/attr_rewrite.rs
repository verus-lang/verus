/// Macros defined in this module enables developers to annotate Rust code in
/// standard Rust code, eliminating the need to wrap exec code inside `verus!
/// {}`.
///
/// Usage:
/// - Items (function, struct, const) used for verification need to be annotated
///   with `#[verus_verify].
/// - To apply `requires`, `ensures`, `invariant`, or `proof` in `exec`,
///   developers should call the corresponding macros at the beginning of the
///   function or loop.
///
/// Rationale:
/// - This approach avoids introducing new syntax into existing Rust executable
///   code, allowing verification and non-verification developers to collaborate
///   without affecting each other.
///   For developers who do not understand verification, they can easily ignore
///   verus code via feature selection and use standard rust tools like
///   `rustfmt` and `rust-analyzer`.
///
/// Limitations:
/// - #[verus_verify] does not support all `verus` syntax, particularly
///   those constructs not accepted by `rustc`.
/// - For defining complex `verus` specifications or proof functions, developers
///   should still use `verus! {}`.
/// - Use of tracked variable is possible but in a different style.
///
/// Example:
/// - Refer to the `test_small_macros_verus_verify` in `example/syntax.rs`.
use core::convert::TryFrom;
use core::convert::TryInto;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::{
    parse2, parse_macro_input, parse_quote, spanned::Spanned, token::Brace, visit_mut,
    visit_mut::VisitMut, Attribute, Block, Expr, Ident, ItemFn, Stmt, Token, TraitItem,
};

use crate::{attr_block_trait::AnyAttrBlock, syntax, EraseGhost};

#[derive(Debug)]
pub enum FnSpecAttributeKind {
    Requires,
    Ensures,
    Decreases,
}

#[derive(Debug)]
enum LoopSpecAttributeKind {
    Invariant,
    Decreases,
}

impl TryFrom<String> for FnSpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(FnSpecAttributeKind::Requires),
            "ensures" => Ok(FnSpecAttributeKind::Ensures),
            "decreases" => Ok(FnSpecAttributeKind::Decreases),
            _ => Err(name),
        }
    }
}

impl TryFrom<FnSpecAttributeKind> for String {
    type Error = FnSpecAttributeKind;

    fn try_from(name: FnSpecAttributeKind) -> Result<Self, Self::Error> {
        match name {
            FnSpecAttributeKind::Requires => Ok("requires".into()),
            FnSpecAttributeKind::Ensures => Ok("ensures".into()),
            FnSpecAttributeKind::Decreases => Ok("decreases".into()),
            _ => Err(name),
        }
    }
}

impl TryFrom<String> for LoopSpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "invariant" => Ok(LoopSpecAttributeKind::Invariant),
            _ => Err(name),
        }
    }
}

impl TryFrom<LoopSpecAttributeKind> for String {
    type Error = LoopSpecAttributeKind;

    fn try_from(name: LoopSpecAttributeKind) -> Result<Self, Self::Error> {
        match name {
            LoopSpecAttributeKind::Invariant => Ok("requires".into()),
            LoopSpecAttributeKind::Decreases => Ok("decreases".into()),
            _ => Err(name),
        }
    }
}

fn add_verifier_attr(attrs: &mut Vec<Attribute>) {
    let verifier_attr: Attribute = parse_quote!(#[verifier::verify]);
    attrs.push(verifier_attr.clone());
}

fn extract_verus_attributes<T: TryFrom<String>>(
    attrs: &mut Vec<Attribute>,
) -> Vec<(T, TokenStream)> {
    let mut verus_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in attrs.drain(0..) {
        if attr.path.segments.len() == 1 {
            if let Ok(attr_kind) = attr.path.segments[0].ident.to_string().try_into() {
                verus_attributes.push((attr_kind, attr.tokens));
            } else {
                regular_attributes.push(attr);
            }
        } else {
            regular_attributes.push(attr);
        }
    }
    *attrs = regular_attributes;
    verus_attributes
}

fn rewrite_verus_loop_attribute(
    erase: &EraseGhost,
    outer_attr_tokens: Vec<(LoopSpecAttributeKind, TokenStream)>,
    any_loop: &mut dyn AnyAttrBlock,
) {
    let mut verus_attrs = outer_attr_tokens;
    verus_attrs.extend(extract_verus_attributes(any_loop.attrs_mut()));
    if erase.keep() {
        // rewrite based on different spec attributes
        for (attr_kind, attr_tokens) in verus_attrs {
            match attr_kind {
                LoopSpecAttributeKind::Invariant | LoopSpecAttributeKind::Decreases => {
                    insert_spec_call(any_loop, attr_kind.try_into().unwrap(), attr_tokens);
                }
            }
        }
    }
}

fn rewrite_verus_fn_attribute(
    erase: &EraseGhost,
    outer_attr_tokens: Vec<(FnSpecAttributeKind, TokenStream)>,
    any_fn: &mut dyn AnyAttrBlock,
) {
    // Start with the outer attribute
    let mut verus_attrs = outer_attr_tokens;
    // remove verus attributes
    verus_attrs.extend(extract_verus_attributes(any_fn.attrs_mut()));

    let mut visitor = AttributesVisitor::new(erase.clone());
    if erase.keep() {
        visitor.visit_block_mut(any_fn.block_mut().unwrap());
        // insert verifier::verify
        add_verifier_attr(any_fn.attrs_mut());
        // rewrite based on different spec attributes
        for (attr_kind, attr_tokens) in verus_attrs {
            match attr_kind {
                FnSpecAttributeKind::Requires
                | FnSpecAttributeKind::Ensures
                | FnSpecAttributeKind::Decreases => {
                    insert_spec_call(any_fn, attr_kind.try_into().unwrap(), attr_tokens);
                }
            }
        }
    }
}

fn insert_spec_call(any_fn: &mut dyn AnyAttrBlock, call: String, outer_attr_tokens: TokenStream) {
    let tokens: TokenStream = syntax::proof_macro_exprs(
        EraseGhost::Keep,
        true,
        quote! {
                ::builtin::verus_proof_macro_exprs_args!([#outer_attr_tokens])
        }
        .into(),
    )
    .into();
    let fname = Ident::new(call.as_str(), outer_attr_tokens.span());
    any_fn
        .block_mut()
        .unwrap()
        .stmts
        .insert(0, syn::parse2(quote! { builtin::#fname(#tokens); }).unwrap());
}

pub fn rewrite_verus_attribute(erase: &EraseGhost, any_fn: TokenStream) -> TokenStream {
    let mut item = parse2(any_fn).expect("#[verify] must on item");
    let mut visitor = AttributesVisitor::new(*erase);
    visitor.visit_item_mut(&mut item);
    quote_spanned! {item.span()=>
        #item
    }
    .into()
}

pub fn rewrite_verus_itemfn_attribute(
    erase: &EraseGhost,
    outer_attr_tokens: Vec<(FnSpecAttributeKind, TokenStream)>,
    input: TokenStream,
) -> TokenStream {
    let mut f = syn::parse2::<ItemFn>(input).expect("Must on a function item. NOTE: #[verus_verify] is needed if using in impl or trait methods");
    let mut visitor = AttributesVisitor::new(erase.clone());
    visitor.visit_item_fn_mut(&mut f);
    quote_spanned! {item.span()=>
        #item
    }
    .into()
}

struct AttributesVisitor {
    erase: EraseGhost,
    spec_trait_items: Option<Vec<TraitItem>>,
}

impl AttributesVisitor {
    pub fn new(erase: EraseGhost) -> Self {
        AttributesVisitor { erase, spec_trait_items: None }
    }

    fn remove_verus_attributes<T: TryFrom<String>>(
        &mut self,
        attrs: &mut Vec<Attribute>,
    ) -> Vec<(T, TokenStream)> {
        let verus_attrs = extract_verus_attributes::<T>(attrs);
        verus_attrs
    }

    fn add_verifier_attr(&mut self, attrs: &mut Vec<Attribute>) {
        add_verifier_attr(attrs);
    }
}

impl VisitMut for AttributesVisitor {
    fn visit_item_fn_mut(&mut self, i: &mut syn::ItemFn) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_item_fn_mut(self, i);
        rewrite_verus_fn_attribute(&self.erase, verus_attrs, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_expr_loop_mut(&mut self, i: &mut syn::ExprLoop) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_expr_loop_mut(self, i);
        rewrite_verus_loop_attribute(&self.erase, verus_attrs, i);
    }

    fn visit_expr_for_loop_mut(&mut self, i: &mut syn::ExprForLoop) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_expr_for_loop_mut(self, i);
        rewrite_verus_loop_attribute(&self.erase, verus_attrs, i);
    }

    fn visit_item_impl_mut(&mut self, i: &mut syn::ItemImpl) {
        visit_mut::visit_item_impl_mut(self, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_impl_item_method_mut(&mut self, i: &mut syn::ImplItemMethod) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_impl_item_method_mut(self, i);
        rewrite_verus_fn_attribute(&self.erase, verus_attrs, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_trait_mut(&mut self, i: &mut syn::ItemTrait) {
        assert!(self.spec_trait_items.is_none());
        self.spec_trait_items = Some(vec![]);
        visit_mut::visit_item_trait_mut(self, i);
        i.items.append(self.spec_trait_items.as_mut().unwrap());
        self.spec_trait_items = None;
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_trait_item_method_mut(&mut self, fun: &mut syn::TraitItemMethod) {
        //   fn #[requires(x)]f(); //a trait method;
        // becomes
        //   #[requires(true)]
        //   fn VERUS_SPEC__f() {}
        //   fn f();
        // and then rewrite_verus_fn_attribute:
        //   fn VERUS_SPEC__f() { requires(x); ... }
        //   fn f();
        let verus_attrs = self.remove_verus_attributes(&mut fun.attrs);
        visit_mut::visit_trait_item_method_mut(self, fun);
        if !verus_attrs.is_empty() {
            let mut spec_fun = fun.clone();
            self.add_verifier_attr(&mut fun.attrs);
            // Add a default exec function with spec calls.
            let x = fun.sig.ident.clone();
            // need to use __VERUS_SPEC__ instead of VERUS_SPEC__ to avoid conflict if used inside verus!{}
            spec_fun.sig.ident = Ident::new(&format!("VERUS_SPEC__{x}"), spec_fun.sig.span());
            let hidden_attr: Attribute = parse_quote!(#[doc(hidden)]);
            spec_fun.attrs.push(hidden_attr);
            let stmts = vec![Stmt::Expr(Expr::Verbatim(
                quote_spanned_builtin!(builtin, spec_fun.default.span() => #builtin::no_method_body()),
            ))];
            spec_fun.default = Some(Block { brace_token: Brace(spec_fun.default.span()), stmts });
            rewrite_verus_fn_attribute(&self.erase, verus_attrs, &mut spec_fun);
            self.spec_trait_items.as_mut().unwrap().push(TraitItem::Method(spec_fun));
        }
    }
}
