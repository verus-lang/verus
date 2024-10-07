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
use core::convert::{TryFrom, TryInto};
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    parse2, parse_quote, spanned::Spanned, token::Brace, visit_mut, visit_mut::VisitMut, Attribute,
    Block, Error, Expr, ExprForLoop, ExprLoop, ExprWhile, Ident, ImplItemMethod, ItemConst,
    ItemEnum, ItemFn, ItemImpl, ItemMod, ItemStruct, ItemTrait, ItemUnion, Stmt, TraitItem,
    TraitItemMethod,
};

use crate::{attr_block_trait::AnyAttrBlock, syntax, syntax::VERUS_SPEC, EraseGhost};

#[derive(Debug)]
pub enum SpecAttributeKind {
    Requires,
    Ensures,
    Decreases,
    Invariant,
}

struct SpecAttributeApply {
    pub on_function: bool,
    pub on_loop: bool,
}

impl SpecAttributeKind {
    fn applies_to(&self) -> SpecAttributeApply {
        let (on_function, on_loop) = match self {
            SpecAttributeKind::Requires => (true, false),
            SpecAttributeKind::Ensures => (true, true),
            SpecAttributeKind::Decreases => (true, true),
            SpecAttributeKind::Invariant => (false, true),
        };
        SpecAttributeApply { on_function, on_loop }
    }

    fn applies_to_function(&self) -> bool {
        self.applies_to().on_function
    }

    fn applies_to_loop(&self) -> bool {
        self.applies_to().on_loop
    }
}

impl TryFrom<String> for SpecAttributeKind {
    type Error = String;

    fn try_from(name: String) -> Result<Self, Self::Error> {
        match name.as_str() {
            "requires" => Ok(SpecAttributeKind::Requires),
            "ensures" => Ok(SpecAttributeKind::Ensures),
            "decreases" => Ok(SpecAttributeKind::Decreases),
            "invariant" => Ok(SpecAttributeKind::Invariant),
            _ => Err(name),
        }
    }
}

fn has_external_code(attrs: &Vec<Attribute>) -> bool {
    let syn_verus_attrs: Vec<syn_verus::Attribute> =
        attrs.iter().map(|attr| syn_verus::parse_quote::parse(attr.to_token_stream())).collect();
    syntax::has_external_code(&syn_verus_attrs)
}
fn add_verifier_attr(attrs: &mut Vec<Attribute>) {
    if !has_external_code(attrs) {
        let verifier_attr: Attribute = parse_quote!(#[verifier::verify]);
        attrs.push(verifier_attr.clone());
    }
}

fn remove_verus_attributes(attrs: &mut Vec<Attribute>) -> Vec<(SpecAttributeKind, TokenStream)> {
    let mut verus_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in attrs.drain(0..) {
        if attr.path.segments.len() == 1 {
            if let Ok(attr_kind) = attr.path.segments[0].ident.to_string().try_into() {
                verus_attributes.push((
                    attr_kind,
                    remove_bracket(attr.tokens).expect(&format!(
                        "Must use #[{:#?}(..)]",
                        attr.path.segments[0].ident.to_string()
                    )),
                ));
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

fn remove_bracket(tokens: TokenStream) -> Result<TokenStream, syn_verus::Expr> {
    // Parse the TokenStream into a Syn Expression
    let t = syn_verus::parse2::<syn_verus::ExprTuple>(tokens.clone())
        .map_or(tokens, |e| e.elems.to_token_stream());
    Ok(t)
}

fn expand_verus_attribute(
    erase: &EraseGhost,
    verus_attrs: Vec<(SpecAttributeKind, TokenStream)>,
    any_with_attr_block: &mut dyn AnyAttrBlock,
    function_or_loop: bool,
) {
    if !erase.keep() {
        return;
    }
    // rewrite based on different spec attributes
    for (attr_kind, attr_tokens) in verus_attrs {
        if function_or_loop {
            assert!(attr_kind.applies_to_function());
        }
        if !function_or_loop {
            assert!(attr_kind.applies_to_loop());
        }
        match attr_kind {
            SpecAttributeKind::Invariant => {
                insert_spec_call(any_with_attr_block, "invariant", quote! {[#attr_tokens]})
            }
            SpecAttributeKind::Decreases => {
                insert_spec_call(any_with_attr_block, "decreases", attr_tokens)
            }
            SpecAttributeKind::Ensures => {
                insert_spec_call(any_with_attr_block, "ensures", attr_tokens)
            }
            SpecAttributeKind::Requires => {
                insert_spec_call(any_with_attr_block, "requires", quote! {[#attr_tokens]})
            }
        }
    }
}

fn insert_spec_call(any_fn: &mut dyn AnyAttrBlock, call: &str, verus_expr: TokenStream) {
    let fname = Ident::new(call, verus_expr.span());
    let tokens: TokenStream =
        syntax::rewrite_expr(EraseGhost::Keep, true, verus_expr.into()).into();
    any_fn
        .block_mut()
        .unwrap()
        .stmts
        .insert(0, parse2(quote! { ::builtin::#fname(#tokens); }).unwrap());
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

pub fn rewrite_item_fn(
    erase: &EraseGhost,
    outer_attr: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    input: TokenStream,
) -> Result<TokenStream, Error> {
    let mut f = parse2::<ItemFn>(input).map_err(|e| {
        let mut new_err = Error::new(
            e.span(),
            "Not on function. NOTE: impl/trait must be annotated with #[verus_verify]",
        );
        new_err.combine(e);
        new_err
    })?;

    let mut visitor = AttributesVisitor::new(erase.clone());
    let outer_attr_tokens =
        remove_bracket(outer_attr_tokens).expect(&format!("use #[{:#?}(..)]", outer_attr));

    let mut verus_attrs = vec![(outer_attr, outer_attr_tokens)];
    verus_attrs.extend(remove_verus_attributes(&mut f.attrs));
    visitor.visit_block_mut(&mut f.block);
    expand_verus_attribute(erase, verus_attrs, &mut f, true);
    if erase.keep() {
        add_verifier_attr(&mut f.attrs);
    }
    Ok(quote_spanned! {f.span()=>#f}.into())
}

struct AttributesVisitor {
    erase: EraseGhost,
    spec_trait_items: Option<Vec<TraitItem>>,
}

impl AttributesVisitor {
    pub fn new(erase: EraseGhost) -> Self {
        AttributesVisitor { erase, spec_trait_items: None }
    }

    fn remove_verus_attributes(
        &mut self,
        attrs: &mut Vec<Attribute>,
    ) -> Vec<(SpecAttributeKind, TokenStream)> {
        let verus_attrs = remove_verus_attributes(attrs);
        if self.erase.erase_all() { vec![] } else { verus_attrs }
    }

    // add verifier::verify for items, impl items, and trait items
    fn add_verifier_attr(&mut self, attrs: &mut Vec<Attribute>) {
        if self.erase.keep() {
            add_verifier_attr(attrs);
        }
    }

    /// Add a default exec function with spec calls.
    ///   fn #[requires(x)]f(); //a trait method;
    /// becomes
    ///   #[requires(true)]
    ///   fn VERUS_SPEC__f() {}
    ///   fn f();
    /// and then rewrite_verus_fn_attribute:
    ///   fn VERUS_SPEC__f() { requires(x); ... }
    ///   fn f();
    fn expand_verus_attribute_on_trait_method(
        &self,
        verus_attrs: Vec<(SpecAttributeKind, TokenStream)>,
        fun: &mut TraitItemMethod,
    ) -> Vec<TraitItem> {
        if verus_attrs.is_empty() {
            return vec![];
        }
        let mut spec_fun = fun.clone();
        let x = fun.sig.ident.clone();
        if fun.default.is_none() {
            spec_fun.sig.ident = Ident::new(&format!("{VERUS_SPEC}{x}"), spec_fun.sig.span());
            spec_fun.attrs.push(parse_quote!(#[doc(hidden)]));
            spec_fun.attrs.push(parse_quote!(#[allow(non_snake_case)]));
            let stmts = vec![Stmt::Expr(Expr::Verbatim(
                quote_spanned_builtin!(builtin, spec_fun.default.span() => #builtin::no_method_body()),
            ))];
            spec_fun.default = Some(Block { brace_token: Brace(spec_fun.default.span()), stmts });
            expand_verus_attribute(&self.erase, verus_attrs, &mut spec_fun, true);
            vec![TraitItem::Method(spec_fun)]
        } else {
            expand_verus_attribute(&self.erase, verus_attrs, fun, true);
            vec![]
        }
    }
}

impl VisitMut for AttributesVisitor {
    fn visit_item_const_mut(&mut self, i: &mut ItemConst) {
        visit_mut::visit_item_const_mut(self, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_mod_mut(&mut self, i: &mut ItemMod) {
        visit_mut::visit_item_mod_mut(self, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_struct_mut(&mut self, i: &mut ItemStruct) {
        visit_mut::visit_item_struct_mut(self, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_union_mut(&mut self, i: &mut ItemUnion) {
        visit_mut::visit_item_union_mut(self, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_enum_mut(&mut self, i: &mut ItemEnum) {
        visit_mut::visit_item_enum_mut(self, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_fn_mut(&mut self, i: &mut ItemFn) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_item_fn_mut(self, i);
        expand_verus_attribute(&self.erase, verus_attrs, i, true);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_impl_mut(&mut self, i: &mut ItemImpl) {
        visit_mut::visit_item_impl_mut(self, i);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_impl_item_method_mut(&mut self, i: &mut ImplItemMethod) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_impl_item_method_mut(self, i);
        expand_verus_attribute(&self.erase, verus_attrs, i, true);
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_item_trait_mut(&mut self, i: &mut ItemTrait) {
        assert!(self.spec_trait_items.is_none());
        self.spec_trait_items = Some(vec![]);
        visit_mut::visit_item_trait_mut(self, i);
        i.items.append(self.spec_trait_items.as_mut().unwrap());
        self.spec_trait_items = None;
        self.add_verifier_attr(&mut i.attrs);
    }

    fn visit_trait_item_method_mut(&mut self, fun: &mut TraitItemMethod) {
        self.add_verifier_attr(&mut fun.attrs);
        let verus_attrs = self.remove_verus_attributes(&mut fun.attrs);
        visit_mut::visit_trait_item_method_mut(self, fun);
        let spec_item = self.expand_verus_attribute_on_trait_method(verus_attrs, fun);
        self.spec_trait_items.as_mut().unwrap().extend(spec_item);
    }

    fn visit_expr_loop_mut(&mut self, i: &mut ExprLoop) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_expr_loop_mut(self, i);
        expand_verus_attribute(&self.erase, verus_attrs, i, false);
    }

    fn visit_expr_for_loop_mut(&mut self, i: &mut ExprForLoop) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_expr_for_loop_mut(self, i);
        expand_verus_attribute(&self.erase, verus_attrs, i, false);
    }

    fn visit_expr_while_mut(&mut self, i: &mut ExprWhile) {
        let verus_attrs = self.remove_verus_attributes(&mut i.attrs);
        visit_mut::visit_expr_while_mut(self, i);
        expand_verus_attribute(&self.erase, verus_attrs, i, false);
    }
}
