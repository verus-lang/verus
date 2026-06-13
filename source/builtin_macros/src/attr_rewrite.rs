/// Macros defined in this module enables developers to annotate Rust code in
/// standard Rust code, eliminating the need to wrap exec code inside `verus!
/// {}`.
///
/// Usage:
/// - Items (struct, const) used for verification need to be annotated
///   with `#[verus_verify].
/// - Functions used for verification need to be annotated with `#[verus_spec ...]`
///   or `#[verus_spec pattern => ...]`
///   where ... is a block of requires, ensures, decreases, etc. in the verus! syntax
/// - To apply `ensures`, `invariant`, `decreases` in `exec`,
///   developers should call the corresponding macros at the beginning of the loop
/// - To use proof block, add proof!{...} inside function body.
/// - To Add tracked/ghost in signature, use #[verus_spec(with ...)] in function definition.
///   To pass and get tracked/ghost from function call, use #[verus_spec(with ...)] in
///   call expr or local statement. Unverified code does not need to change arguments or outputs.
///
/// Rationale:
/// - This approach avoids introducing new syntax into existing Rust executable
///   code, allowing verification and non-verification developers to collaborate
///   without affecting each other.
///   Thus, this module uses syn instead of verus_syn in most cases.
///   For developers who do not understand verification, they can easily ignore
///   verus code via feature/cfg selection and use standard rust tools like
///   `rustfmt` and `rust-analyzer`.
/// - Unverified code does not need additional annotation to interact with verified.
///
/// Limitations:
/// - #[verus_verify] does not support all `verus` syntax, particularly
///   those constructs not accepted by `rustc`.
/// - For defining complex `verus` specifications or proof functions, developers
///   should still use `verus! {}`.
/// - Use of tracked variable is possible but in a different style.
///
/// Example:
/// - Refer to `examples/syntax_attr.rs`.
use proc_macro2::TokenStream;
use quote::{ToTokens, quote, quote_spanned};
use syn::parse::Parser;
use syn::visit_mut::VisitMut;
use syn::{Expr, Item, ItemConst, parse2, spanned::Spanned};

use crate::{
    EraseGhost,
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax::{self, has_external_code_syn, mk_verifier_attr_syn, mk_verus_attr_syn},
    syntax_trait,
    unerased_proxies::VERUS_UNERASED_PROXY,
};

pub const DUAL_SPEC_PREFIX: &str = "__VERUS_SPEC";

const VERUS_SPEC: &str = "verus_spec";

// No cross-function type registry. When Rust cannot infer types for
// proof_with/proof_with_ret (e.g., cross-crate calls or when callee is processed
// after caller), the user must provide explicit type annotations on their variables.

enum VerusIOTarget {
    Local(syn::Local),
    Expr(syn::Expr),
}

impl quote::ToTokens for VerusIOTarget {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            VerusIOTarget::Local(local) => local.to_tokens(tokens),
            VerusIOTarget::Expr(expr) => expr.to_tokens(tokens),
        }
    }
}

enum VerusSpecTarget {
    IOTarget(VerusIOTarget),
    FnOrLoop(AnyFnOrLoop),
    ItemConst(ItemConst),
    ItemStatic(syn::ItemStatic),
}

impl syn::parse::Parse for VerusSpecTarget {
    fn parse(input: syn::parse::ParseStream) -> syn::parse::Result<VerusSpecTarget> {
        use syn::parse::discouraged::Speculative;
        let fork = input.fork();
        if let Ok(fn_or_loop) = fork.parse() {
            input.advance_to(&fork);
            return Ok(VerusSpecTarget::FnOrLoop(fn_or_loop));
        }
        let fork = input.fork();
        if let Ok(stmt) = fork.parse() {
            if let syn::Stmt::Local(local) = stmt {
                input.advance_to(&fork);
                return Ok(VerusSpecTarget::IOTarget(VerusIOTarget::Local(local)));
            }
        }
        let fork = input.fork();
        if let Ok(item_const) = fork.parse::<ItemConst>() {
            input.advance_to(&fork);
            return Ok(VerusSpecTarget::ItemConst(item_const));
        }
        let fork = input.fork();
        if let Ok(item_static) = fork.parse::<syn::ItemStatic>() {
            input.advance_to(&fork);
            return Ok(VerusSpecTarget::ItemStatic(item_static));
        }

        let expr: Expr = input.parse()?;
        return Ok(VerusSpecTarget::IOTarget(VerusIOTarget::Expr(expr)));
    }
}

pub(crate) fn rewrite_verus_attribute(
    erase: &EraseGhost,
    attr_args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    if !erase.keep() {
        return input;
    }

    let mut item = syn::parse_macro_input!(input as Item);
    let args = syn::parse_macro_input!(attr_args with syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated);

    let mut attributes = Vec::new();
    let mut contains_non_external = false;
    let mut contains_external = false;
    let mut spec_fun = None;
    const VERIFY_ATTRS: [&str; 4] = ["rlimit", "spinoff_prover", "external_derive", "ext_equal"];
    const DUAL_ATTR: &str = "dual_spec";
    const IGNORE_VERIFY_ATTRS: [&str; 3] =
        ["external", "external_body", "external_type_specification"];
    // Modifier attrs are compatible with both external and non-external attrs.
    // They neither set contains_external nor contains_non_external.
    const MODIFIER_ATTRS: [&str; 3] = [
        "reject_recursive_types",
        "reject_recursive_types_in_ground_variants",
        "accept_recursive_types",
    ];

    for arg in &args {
        let path = arg.path().get_ident().expect("Invalid verus verifier attribute");
        if IGNORE_VERIFY_ATTRS.contains(&path.to_string().as_str()) {
            contains_external = true;
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if VERIFY_ATTRS.contains(&path.to_string().as_str()) {
            contains_non_external = true;
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if MODIFIER_ATTRS.contains(&path.to_string().as_str()) {
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if DUAL_ATTR == path.to_string().as_str() {
            // This is a macro-level hack to support dual mode.
            // Thus, only a limited number of pure compute functions are
            // supported.
            // The real dual mode is not ready yet (e.g., verifier::dual_spec).
            // The spec function is generated with the name _VERUS_SPEC_<name>
            // if no name is given.
            if let syn::Item::Fn(f) = &mut item {
                let mut spec_f = f.clone();
                let ident = if let syn::Meta::List(list) = arg {
                    syn::parse2(list.tokens.clone())
                        .expect("unsupported tokens in verus_verify(dual_spec(...))")
                } else {
                    syn::Ident::new(
                        &format!("{DUAL_SPEC_PREFIX}_{}", f.sig.ident),
                        f.sig.ident.span(),
                    )
                };
                spec_f.sig.ident = ident.clone();
                spec_f.attrs = vec![mk_verus_attr_syn(f.span(), quote! { spec })];
                // remove proof-related macros
                replace_block(EraseGhost::Erase, spec_f.block_mut().unwrap(), false);
                spec_fun = Some(spec_f);

                attributes
                    .push(quote_spanned!(arg.span() => #[verifier::when_used_as_spec(#ident)]));
            }
        } else {
            let span = arg.span();
            return proc_macro::TokenStream::from(quote_spanned!(span =>
                compile_error!("unsupported parameters {:?} in #[verus_verify(...)]", arg);
            ));
        }
    }
    if contains_external && contains_non_external {
        return proc_macro::TokenStream::from(quote_spanned!(args.span() =>
            compile_error!("conflict parameters in #[verus_verify(...)]");
        ));
    }
    if !contains_external {
        attributes.push(quote_spanned!(item.span() => #[verifier::verify]));
    }

    // Inject #[verus_spec] where missing and stamp impl methods with the sentinel marker.
    prepare_items_for_verus_spec(args.span(), &mut item);
    let mut new_stream = quote_spanned! {item.span()=>
        #(#attributes)*
        #item
    };
    spec_fun.map(|f| f.to_tokens(&mut new_stream));
    new_stream.into()
}

struct ExecReplacer {
    erase: EraseGhost,
    inside_external_code: bool,
}

impl VisitMut for ExecReplacer {
    // Enable the hack only when needed
    #[cfg(feature = "vpanic")]
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        syn::visit_mut::visit_macro_mut(self, mac);
        // Only replace in verification mode
        if !self.erase.keep() || self.inside_external_code {
            return;
        }
        if let Some(x) = mac.path.segments.first_mut() {
            let ident = x.ident.to_string();
            if ident == "panic" {
                // The builtin panic macro could not be supported due to
                // the use of panic_fmt takes Argument and Argument is created via Arguments::new_v1
                // with a private struct rt::Argument.
                // Directly replacing panic macro is the simpliest solution.
                // Build the full path: std::prelude::vpanic
                let mut segments = syn::punctuated::Punctuated::new();
                segments.push(syn::Ident::new("vstd", x.span()).into());
                segments.push(syn::Ident::new("vpanic", x.span()).into());
                mac.path = syn::Path { leading_colon: None, segments };
            }
        }
    }

    fn visit_attribute_mut(&mut self, node: &mut syn::Attribute) {
        // Ignore verus_spec in non-verification mode.
        // Thus, non-verification mode does not need to use unstable features.
        if self.erase.keep() {
            return;
        }
        if let Some(last) = node.path().segments.last() {
            if last.ident == VERUS_SPEC {
                *node = syn::parse_quote! {
                    #[doc = r"verus_spec is applied only in verification mode"]
                }
            }
        }
    }

    /// convert proof_with macro to functin with ghost/tracked argumemts.
    /// In order to apply `with` to expr/stmt without using unstable feature.
    /// proof_with!(Tracked(x), Ghost(y);
    /// f(a);
    /// Also supports struct constructors with ghost/tracked fields:
    /// proof_with!{ p: Tracked(p) }
    /// STest { u }
    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        // Don't call visit_block_mut to recurse on the whole block --
        // skip statements that will be processed by their own #[verus_spec] attribute.
        // syn::visit_mut::visit_block_mut(self, block);
        for stmt in &mut block.stmts {
            // Don't recurse here into Fn and Const.
            // Instead, let a subsequent expansion of #[verus_spec] handle the visit
            let span = stmt.span();
            match stmt {
                syn::Stmt::Item(Item::Fn(item)) => {
                    add_verus_spec_if_needed(&mut item.attrs, span);
                }
                syn::Stmt::Item(Item::Const(item)) => {
                    add_verus_spec_if_needed(&mut item.attrs, span);
                }
                _ => self.visit_stmt_mut(stmt),
            }
        }

        // If we are in non-verification mode, we erase all proof-related statements.
        if !self.erase.keep() {
            block.stmts.retain(|stmt| !is_verus_proof_stmt(stmt));
            return;
        }

        let mut with_args: TokenStream = TokenStream::new();
        for stmt in &mut block.stmts {
            match stmt {
                syn::Stmt::Macro(syn::StmtMacro { mac, .. }) if mac.path.is_ident("proof_with") => {
                    verus_syn::Token![with](mac.span()).to_tokens(&mut with_args);
                    mac.tokens.to_tokens(&mut with_args);
                }
                syn::Stmt::Local(syn::Local { attrs, init: Some(_), .. })
                    if !with_args.is_empty() =>
                {
                    attrs.push(crate::syntax::mk_rust_attr_syn(
                        with_args.span(),
                        VERUS_SPEC,
                        with_args,
                    ));
                    with_args = TokenStream::new();
                }
                syn::Stmt::Expr(expr, _) if !with_args.is_empty() => {
                    let call_with_spec = verus_syn::parse2(with_args.clone()).unwrap_or_else(|e| {
                        panic!("Failed to parse proof_with {:?}: {:?}", with_args, e)
                    });
                    rewrite_with_expr(self.erase.clone(), expr, call_with_spec);
                    with_args = TokenStream::new();
                }
                _ if with_args.is_empty() => {
                    // do nothing
                }
                _ => {
                    panic!(
                        "Expected a function call or struct constructor after proof_with! macro"
                    );
                }
            };
        }
    }

    fn visit_expr_for_loop_mut(&mut self, for_loop: &mut syn::ExprForLoop) {
        syn::visit_mut::visit_expr_for_loop_mut(self, for_loop);

        if !self.erase.keep() || self.inside_external_code {
            return;
        }

        // In verification mode, even without verus spec on the loop, we still
        // need to desugar the for loop.
        // So, if there's no `verus_spec` attribute, we need to add an empty one.
        let span = for_loop.span();
        add_verus_spec_if_needed(&mut for_loop.attrs, span);
    }
}

fn add_verus_spec_if_needed(attrs: &mut Vec<syn::Attribute>, span: proc_macro2::Span) {
    if attrs.iter().any(|attr| attr.path().get_ident().map_or(false, |ident| ident == VERUS_SPEC)) {
        return;
    }
    attrs.push(crate::syntax::mk_rust_attr_syn(span, VERUS_SPEC, TokenStream::new()));
}

/// Prepares items under `#[verus_verify]` for subsequent `#[verus_spec]` expansion.
///
/// This function performs two tasks:
///
/// 1. **Inject `#[verus_spec]` where missing.** Items and impl items that carry
///    `#[verus_verify]` but no `#[verus_spec]` would otherwise be marked as
///    verifier-aware without receiving the necessary rewrites (loop desugaring,
///    const/static proxy generation, etc.), resulting in confusing error messages.
///    An empty `#[verus_spec]` is added so the rewriter has something to act on.
///
/// 2. **Mark impl methods with a sentinel attribute.** Each impl method that has
///    (or just received) a `#[verus_spec]` attribute is tagged with an internal
///    `#[allow(unused, verus_impl_method_marker)]` attribute. This signals to the
///    `#[verus_spec]` expansion that the method lives inside an impl block,
///    enabling it to apply impl-specific rewrites.
///
/// Recursion into nested items is intentionally skipped here; `#[verus_spec]`
/// handles that during its own expansion pass.
fn prepare_items_for_verus_spec(span: proc_macro2::Span, i: &mut syn::Item) {
    match i {
        syn::Item::Const(syn::ItemConst { attrs, .. })
        | syn::Item::Static(syn::ItemStatic { attrs, .. })
        | syn::Item::Fn(syn::ItemFn { attrs, .. }) => {
            add_verus_spec_if_needed(attrs, span);
        }
        syn::Item::Impl(i) => {
            for item in &mut i.items {
                match item {
                    syn::ImplItem::Const(syn::ImplItemConst { attrs, .. }) => {
                        add_verus_spec_if_needed(attrs, span);
                    }
                    syn::ImplItem::Fn(syn::ImplItemFn { attrs, .. }) => {
                        add_verus_spec_if_needed(attrs, span);
                        attrs.push(crate::syntax::mk_rust_attr_syn(
                            span,
                            "allow",
                            quote_spanned! { span => (unused, verus_impl_method_marker)},
                        ));
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

fn is_verus_proof_stmt(stmt: &syn::Stmt) -> bool {
    pub const VERUS_MACROS: [&str; 3] = ["proof", "proof_decl", "proof_with"];
    if let syn::Stmt::Macro(mac_stmt) = stmt {
        let syn::Macro { path, .. } = &mac_stmt.mac;
        if let Some(ident) = path.get_ident() {
            return VERUS_MACROS.contains(&ident.to_string().as_str());
        }
    }
    false
}

// We need to replace some macros/attributes.
// For example, panic, println, fmt macro is hard to support in verus.
// We can replace them to enable the support.
// TODO: when tracked/ghost is supported, we need to clear verus-related
// attributes for expression so that unverfied `cargo build` does not need to
// enable unstable feature for macro.
pub(crate) fn replace_block(
    erase: EraseGhost,
    fblock: &mut syn::Block,
    inside_external_code: bool,
) {
    let mut replacer = ExecReplacer { erase, inside_external_code };
    replacer.visit_block_mut(fblock);
}

pub(crate) fn replace_expr(erase: EraseGhost, expr: &mut syn::Expr) {
    let mut replacer = ExecReplacer { erase, inside_external_code: false };
    replacer.visit_expr_mut(expr);
}

pub(crate) fn rewrite_verus_spec(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    if erase.erase_all() {
        return input;
    }
    // Remove the last `,` if `input` has one.
    let mut tokens: Vec<_> = proc_macro2::TokenStream::from(input).into_iter().collect();
    if matches!(tokens.last(), Some(proc_macro2::TokenTree::Punct(p)) if p.as_char() == ',') {
        tokens.pop();
    }
    let input: proc_macro::TokenStream =
        tokens.into_iter().collect::<proc_macro2::TokenStream>().into();

    let f = match syn::parse::<VerusSpecTarget>(input) {
        Ok(f) => f,
        Err(err) => {
            // Make sure at least one error is reported, just in case Rust parses the function
            // successfully but syn fails to parse it.
            // (In the normal case, this results in a redundant extra error message after
            // the normal Rust syntax error, but it's a reasonable looking error message.)
            return proc_macro::TokenStream::from(
                quote_spanned!(err.span() => compile_error!("Misuse of #[verus_spec]");),
            );
        }
    };

    match f {
        VerusSpecTarget::FnOrLoop(f) => {
            rewrite_verus_spec_on_fun_or_loop(erase, outer_attr_tokens, f)
        }
        VerusSpecTarget::ItemConst(i) => {
            rewrite_verus_spec_on_item_const(erase, outer_attr_tokens, i)
        }
        VerusSpecTarget::ItemStatic(i) => {
            rewrite_verus_spec_on_item_static(erase, outer_attr_tokens, i)
        }
        VerusSpecTarget::IOTarget(i) => {
            rewrite_verus_spec_on_expr_local(erase, outer_attr_tokens, i)
        }
    }
}

fn closure_to_fn_sig(closure: &syn::ExprClosure) -> syn::Signature {
    let infer_type = |span| {
        Box::new(syn::Type::Infer(syn::TypeInfer { underscore_token: syn::Token![_](span) }))
    };
    syn::Signature {
        constness: closure.constness,
        asyncness: closure.asyncness,
        unsafety: None,
        abi: None,
        fn_token: syn::Token![fn](closure.span()),
        ident: syn::Ident::new("closure", closure.span()),
        generics: syn::Generics::default(),
        inputs: closure
            .inputs
            .iter()
            .map(|arg| {
                let (pat, ty) = match arg {
                    syn::Pat::Type(pat_ty) => (pat_ty.pat.clone(), pat_ty.ty.clone()),
                    syn::Pat::Ident(pat_ident) => {
                        let ty = infer_type(pat_ident.span());
                        (Box::new(syn::Pat::Ident(pat_ident.clone())), ty)
                    }
                    _ => {
                        panic!("unexpected pattern in closure argument: {:?}", arg);
                    }
                };
                syn::FnArg::Typed(syn::PatType {
                    attrs: vec![],
                    pat: pat,
                    colon_token: syn::Token![:](arg.span()),
                    ty: ty,
                })
            })
            .collect(),
        variadic: None,
        output: closure.output.clone(),
        paren_token: syn::token::Paren::default(),
    }
}

fn syn_to_verus_syn<V: verus_syn::parse::Parse>(input: impl ToTokens) -> V {
    let tokens = input.to_token_stream();
    verus_syn::parse2(tokens).unwrap()
}

pub(crate) fn rewrite_verus_spec_on_item_const(
    erase_ghost: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    item_const: ItemConst,
) -> proc_macro::TokenStream {
    if erase_ghost.erase() {
        return item_const.to_token_stream().into();
    }
    let spec_attr =
        verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
    let mut verus_item_const = syn_to_verus_syn::<verus_syn::ItemConst>(item_const);
    let span = verus_item_const.span();
    if spec_attr.spec.ensures.is_some() {
        verus_item_const.ensures = spec_attr.spec.ensures;
        verus_item_const.mode = verus_syn::FnMode::Exec(verus_syn::ModeExec {
            exec_token: verus_syn::Token![exec](span),
        });
        verus_item_const.block = Some(Box::new(verus_syn::Block {
            brace_token: verus_syn::token::Brace::default(),
            stmts: vec![verus_syn::Stmt::Expr(
                verus_syn::Expr::Verbatim(verus_item_const.expr.to_token_stream()),
                None,
            )],
        }));
        verus_item_const.eq_token = None;
        verus_item_const.expr = None;
        verus_item_const.semi_token = None;
    }
    let mut items = vec![verus_syn::Item::Const(verus_item_const)];
    crate::syntax::rewrite_items_inner(&mut items, erase_ghost, true)
}

pub(crate) fn rewrite_verus_spec_on_item_static(
    erase_ghost: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    item_static: syn::ItemStatic,
) -> proc_macro::TokenStream {
    if erase_ghost.erase() {
        return item_static.to_token_stream().into();
    }
    let spec_attr =
        verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
    let mut verus_item_static = syn_to_verus_syn::<verus_syn::ItemStatic>(item_static);
    let span = verus_item_static.span();
    // Must add exec mode to static explicitly
    verus_item_static.mode =
        verus_syn::FnMode::Exec(verus_syn::ModeExec { exec_token: verus_syn::Token![exec](span) });
    if spec_attr.spec.ensures.is_some() {
        verus_item_static.ensures = spec_attr.spec.ensures;
        verus_item_static.block = Some(Box::new(verus_syn::Block {
            brace_token: verus_syn::token::Brace::default(),
            stmts: vec![verus_syn::Stmt::Expr(
                verus_syn::Expr::Verbatim(verus_item_static.expr.to_token_stream()),
                None,
            )],
        }));
        verus_item_static.eq_token = None;
        verus_item_static.expr = None;
        verus_item_static.semi_token = None;
    }
    let mut items = vec![verus_syn::Item::Static(verus_item_static)];
    crate::syntax::rewrite_items_inner(&mut items, erase_ghost, true)
}

pub(crate) fn rewrite_verus_spec_on_fun_or_loop(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    f: AnyFnOrLoop,
) -> proc_macro::TokenStream {
    match f {
        AnyFnOrLoop::Fn(mut fun) => {
            // Note: trait default methods appear in this case,
            // since they look syntactically like non-trait functions
            let spec_attr =
                verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);

            fun.attrs.push(mk_verus_attr_syn(fun.span(), quote! { verus_macro }));

            let is_hidden_impl_marker = |attr: &syn::Attribute| {
                attr.path().get_ident().map_or(false, |ident| {
                    ident == "allow"
                        && matches!(&attr.meta, syn::Meta::List(meta_list)
                        if meta_list.tokens.to_string().contains("verus_impl_method_marker"))
                })
            };

            // Check if the function has the impl method marker
            let is_impl_fn = fun.attrs.iter().any(&is_hidden_impl_marker);

            // Remove the marker attribute (internal use only)
            fun.attrs.retain(|attr| !is_hidden_impl_marker(attr));

            let mut new_stream = TokenStream::new();
            let mut rustdoc_attrs: Vec<syn::Attribute> = vec![];
            if crate::rustdoc::env_rustdoc() {
                let mut verus_fun: verus_syn::ItemFn = syn_to_verus_syn(fun.clone());
                verus_fun.sig.spec = spec_attr.spec.clone();

                // Set return variable name
                if let Some((verus_syn::Pat::Ident(pat_ident), _)) = &spec_attr.ret_pat {
                    if let verus_syn::ReturnType::Type(_, _, opt_name, _) =
                        &mut verus_fun.sig.output
                    {
                        *opt_name = Some(Box::new((
                            verus_syn::token::Paren::default(),
                            verus_syn::Pat::Ident(pat_ident.clone()),
                            verus_syn::Token![:](pat_ident.span()),
                        )));
                    }
                }

                crate::rustdoc::process_item_fn(&mut verus_fun);

                for attr in &verus_fun.attrs {
                    if attr.path().is_ident("doc")
                        && attr.to_token_stream().to_string().contains("verusdoc_special_attr")
                    {
                        if let Ok(doc_attrs) =
                            syn::Attribute::parse_outer.parse(attr.to_token_stream().into())
                        {
                            rustdoc_attrs.extend(doc_attrs);
                        }
                    }
                }
            }

            // With declare_with/declare_ret_with approach, no need to create
            // a VERIFIED_ copy. The function keeps its original name and uses
            // declare_with() in its body for extra ghost/tracked params.
            if let Some(_with) = &spec_attr.spec.with {
                if crate::rustdoc::env_rustdoc() {
                    fun.attrs.extend(rustdoc_attrs.clone());
                }
            } else if crate::rustdoc::env_rustdoc() {
                fun.attrs.extend(rustdoc_attrs);
            }

            // Inject doc attribute in rustdoc mode
            if crate::rustdoc::env_rustdoc() {
                let mut verus_fun: verus_syn::ItemFn = syn_to_verus_syn(fun.clone());
                verus_fun.sig.spec = spec_attr.spec.clone();

                // Set return variable name
                if let Some((verus_syn::Pat::Ident(pat_ident), _)) = &spec_attr.ret_pat {
                    if let verus_syn::ReturnType::Type(_, _, opt_name, _) =
                        &mut verus_fun.sig.output
                    {
                        *opt_name = Some(Box::new((
                            verus_syn::token::Paren::default(),
                            verus_syn::Pat::Ident(pat_ident.clone()),
                            verus_syn::Token![:](pat_ident.span()),
                        )));
                    }
                }

                crate::rustdoc::process_item_fn(&mut verus_fun);

                for attr in &verus_fun.attrs {
                    if attr.path().is_ident("doc")
                        && attr.to_token_stream().to_string().contains("verusdoc_special_attr")
                    {
                        if let Ok(doc_attrs) =
                            syn::Attribute::parse_outer.parse(attr.to_token_stream().into())
                        {
                            fun.attrs.extend(doc_attrs);
                        }
                    }
                }
            }

            // Update function signature based on verus_spec.
            let spec_stmts =
                syntax::sig_specs_attr(erase, spec_attr, &mut fun.sig, is_impl_fn, false);

            if erase.erase() {
                // In erase mode, just return the stub functions.
                // No need to add proof statements.
                fun.to_tokens(&mut new_stream);
                return proc_macro::TokenStream::from(new_stream);
            }
            // Create const proxy function if it is a const function.
            if fun.sig.constness.is_some() {
                let proxy = rewrite_const_ret_proxy(&mut fun);
                fun.to_tokens(&mut new_stream);
                fun = proxy; // Add proof and spec on proxy func.
            }

            // Add the spec/proof (requires/ensures) to the function body.
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let _ = fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);

            // Parse and replace proof_xxx!() inside function and replace panic.
            let inside_external_code = has_external_code_syn(&fun.attrs);
            replace_block(erase, fun.block_mut().unwrap(), inside_external_code);
            fun.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        // erase non-function cases if in erase mode
        _ if erase.erase() => return f.to_token_stream().into(),
        AnyFnOrLoop::Closure(mut closure) => {
            replace_expr(erase, &mut closure.body);
            let mut spec_attr =
                verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
            if let Some(_) = &spec_attr.spec.with {
                return quote_spanned! {spec_attr.span() => compile_error!("`with` does not support closure")}.into();
            }
            if let Some((verus_syn::Pat::Type(pat_ty), ar)) = spec_attr.ret_pat {
                spec_attr.ret_pat = Some((*pat_ty.pat.clone(), ar));
                closure.output = syn::ReturnType::Type(
                    syn::Token![->](pat_ty.span()),
                    Box::new(syn::Type::Verbatim(pat_ty.ty.to_token_stream())),
                );
            }
            if matches!(closure.output, syn::ReturnType::Default) {
                return quote_spanned! {closure.span() =>
                    compile_error!("Closure must have a return type, or add `$ret: $type =>` in verus_spec");
                }.into();
            }
            let mut signature = closure_to_fn_sig(&closure);
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut signature, false, true);
            let body = &closure.body;
            let new_body = quote_spanned!(closure.body.span() =>
                #(#spec_stmts)*
                {#body}
            );
            *closure.body = Expr::Verbatim(new_body);
            closure.to_token_stream().into()
        }
        AnyFnOrLoop::TraitMethod(mut method) => {
            // Note: default trait methods appear in the AnyFnOrLoop::Fn case, not here
            let spec_attr =
                verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::SignatureSpecAttr);
            let mut new_stream = TokenStream::new();

            if let Some(with) = &spec_attr.spec.with {
                // Trait method requires can only be inherited from the trait declaration
                // However, we cannot distinguish trait function impl vs other function impl.
                // let unverified_method = rewrite_unverified_func(&mut method, with.with.span());
                // unverified_method.to_tokens(&mut new_stream);
                return proc_macro::TokenStream::from(
                    quote_spanned!(with.with.span() => compile_error!("`with` does not support trait");),
                );
            }

            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut method.sig, true, false);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let mut spec_fun_opt = syntax_trait::split_trait_method_syn(&method, erase.erase());
            let spec_fun = spec_fun_opt.as_mut().unwrap_or(&mut method);
            let _ = spec_fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            method.attrs.push(mk_verus_attr_syn(method.span(), quote! { verus_macro }));
            spec_fun_opt.to_tokens(&mut new_stream);
            method.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        AnyFnOrLoop::ForLoop(forloop) => {
            let spec_attr = verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::LoopSpec);
            syntax::for_loop_spec_attr(erase, spec_attr, forloop).to_token_stream().into()
        }
        AnyFnOrLoop::Loop(mut l) => {
            let spec_attr = verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
        AnyFnOrLoop::While(mut l) => {
            let spec_attr = verus_syn::parse_macro_input!(outer_attr_tokens as verus_syn::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
    }
}

pub(crate) fn proof_rewrite(erase: EraseGhost, input: TokenStream) -> proc_macro::TokenStream {
    if erase.keep() {
        let block: TokenStream =
            syntax::proof_block(erase, quote_spanned!(input.span() => {#input}).into()).into();
        quote! {
            #[verifier::proof_block]
            {
                #block;
            }
        }
        .into()
    } else {
        proc_macro::TokenStream::new()
    }
}

/// The `verus_spec(with)` annotation can be applied to either a local statement or an expression.
///
/// - When applied to an expression (`expr`), the trailing semicolon (`;`) is ignored due to limitations of the procedure macro.
///   To include the semicolon, developers must use the following syntax:
///   ```rust
///   {#[verus_spec(with ..)] expr};
///   ```
///
/// - When used with an expression, developers must explicitly declare the returned ghost or tracked patterns.
///   This is because the additional declarations cannot be automatically added in a meaningful way.
///
/// Example:
/// ```rust
/// if #[verus_io(with Tracked(arg1), Ghost(arg2) -> Tracked(out) |= Tracked(extra))]
/// call(arg0) == something {
/// }
/// ```
/// This will be transformed to the following:
/// ```rust
/// {
///     let (tmp, tmp_out) = call(arg0, Tracked(arg1), Tracked(arg2));
///     proof!{out = tmp_out.get();}  // Ensuring `out` is properly assigned.
///     (tmp, Tracked(extra))  // Returning the transformed values.
/// }
/// ```
///
/// The recommended approach for handling returned ghost/tracked outputs is to use a local statement:
///
/// Example:
/// ```rust
/// #[verus_spec(with Tracked(arg1), Ghost(arg2) -> Tracked(out) |= Tracked(extra))]
/// let out0 = call(arg0);
/// ```
/// This will be transformed to:
/// ```rust
/// let tracked mut out;
/// let out0 = {
///     let (tmp, tmp_out) = call(arg0, Tracked(arg1), Tracked(arg2));
///     proof!{out = tmp_out.get();}  // Ensure proper assignment of the ghost value.
///     (tmp, Tracked(extra))  // Returning the transformed values.
/// };
/// ```
fn rewrite_verus_spec_on_expr_local(
    erase: EraseGhost,
    attr_input: proc_macro::TokenStream,
    io_target: VerusIOTarget,
) -> proc_macro::TokenStream {
    if erase.erase() {
        return io_target.to_token_stream().into();
    }
    let call_with_spec = verus_syn::parse_macro_input!(attr_input as verus_syn::WithSpecOnExpr);
    let tokens = match io_target {
        VerusIOTarget::Local(mut local) => {
            let syn::Local { init, .. } = &mut local;
            if let Some(syn::LocalInit { expr, .. }) = init {
                let x_declares = rewrite_with_expr(erase, expr, call_with_spec);
                quote! {
                    #(#x_declares)*
                    #local
                }
            } else {
                proc_macro2::TokenStream::from(quote_spanned!(local.span() =>
                    compile_error!("with attribute cannot be applied to a local without init");
                ))
            }
        }
        VerusIOTarget::Expr(mut e) => {
            rewrite_with_expr(erase, &mut e, call_with_spec);
            e.into_token_stream()
        }
    };
    tokens.into()
}

/// The `|= Ghost(...)` follow-expression syntax is no longer supported.
/// Users should assign directly to the named output variable instead, e.g.:
///
/// ```ignore
/// #[verus_spec(with -> z: Ghost<u32>)]
/// fn f() -> u32 {
///     proof! { z = Ghost(0); }
///     0
/// }
/// ```
fn apply_follows(expr: &mut Expr, follow_tokens: TokenStream) {
    let span = if follow_tokens.is_empty() { expr.span() } else { follow_tokens.span() };
    let expr_tokens = expr.to_token_stream();
    *expr = Expr::Verbatim(quote_spanned!(span => {
        compile_error!(
            "the `|= ...` follow-expression is no longer supported; \
             assign to the extra named output directly with `proof! { name = value; }` \
             (the output name is the ident from `-> name: Type` in the function's `with` clause)"
        );
        #expr_tokens
    }));
}

fn is_tracked_ghost_expr(expr: &verus_syn::Expr) -> bool {
    // check expr is of the form Tracked(...) or Ghost(...)
    if let verus_syn::Expr::Call(verus_syn::ExprCall { func, .. }) = expr {
        if let verus_syn::Expr::Path(path) = func.as_ref() {
            if let Some(ident) = path.path.get_ident() {
                return ident == "Tracked" || ident == "Ghost";
            }
        }
    }
    false
}

/// Apply ghost/tracked fields in `with` clause to a struct constructor expression.
/// Return Err if the ghost/tracked fields are not valid.
fn apply_erased_fields<'a>(
    erase: EraseGhost,
    expr: &mut Expr,
    erased_fields: impl Iterator<Item = &'a verus_syn::FieldValue>,
) -> Result<(), ()> {
    let syn::Expr::Struct(expr_struct) = expr else {
        // If there's no struct constructor, we cannot apply ghost/tracked fields.
        if let Some(field) = erased_fields.last() {
            *expr = syn::Expr::Verbatim(quote_spanned! {field.span() =>
                compile_error!("Ghost/tracked fields can only be applied to struct constructors.")
            });
            return Err(());
        }
        // No ghost/tracked fields, just return.
        return Ok(());
    };
    for field in erased_fields {
        let rewritten =
            syntax::rewrite_expr(erase.clone(), false, field.expr.to_token_stream().into());
        let verus_syn::Member::Named(field_name) = &field.member else {
            *expr = syn::Expr::Verbatim(quote_spanned! {field.member.span() =>
                compile_error!("A ghost/tracked field must be a named field.")
            });
            return Err(());
        };
        if !is_tracked_ghost_expr(&field.expr) {
            *expr = syn::Expr::Verbatim(quote_spanned! {field.expr.span() =>
                compile_error!("A ghost/tracked field must be a tracked/ghost expression. If you want to add ghost/tracked fields to a struct constructor, you should use $ident: Tracked/Ghost($ident).")
            });
            return Err(());
        }
        assert!(field.attrs.is_empty()); // guarded by verus_syn::WithSpecOnExpr parsing
        let extra_field = syn::FieldValue {
            attrs: vec![],
            member: syn::Member::Named(field_name.clone()),
            colon_token: field.colon_token.and_then(|c| Some(syn::Token![:](c.span()))),
            expr: syn::Expr::Verbatim(rewritten.into()),
        };
        expr_struct.fields.push(extra_field);
    }
    return Ok(());
}

// Expand `with extra_in => extra_out` on a method call expr.
// Return some pre-statements that needs to be declared before the expr.
fn rewrite_with_expr(
    erase: EraseGhost,
    expr: &mut Expr,
    call_with_spec: verus_syn::WithSpecOnExpr,
) -> Vec<proc_macro2::TokenStream> {
    let verus_syn::WithSpecOnExpr { inputs, outputs, follows, erased_fields, .. } = call_with_spec;

    // Handle Try expressions by recursing into inner
    if outputs.is_some() || inputs.len() > 0 {
        match expr {
            syn::Expr::Call(_) | syn::Expr::MethodCall(_) => {
                // OK — these are valid call expressions
            }
            syn::Expr::Try(syn::ExprTry { expr, .. }) => {
                let call_with_spec = verus_syn::WithSpecOnExpr {
                    inputs,
                    outputs,
                    follows,
                    erased_fields,
                    ..call_with_spec
                };
                return rewrite_with_expr(erase, expr, call_with_spec);
            }
            _ => {
                *expr = Expr::Verbatim(quote_spanned!(expr.span() =>
                    compile_error!("with ghost inputs/outputs cannot be applied to a non-call expression. You may want to use proof_with!(|= var) to append a ghost var to the expr.")
                ));
                return vec![];
            }
        }
    }

    if apply_erased_fields(erase.clone(), expr, erased_fields.iter()).is_err() {
        return vec![];
    }

    // Build proof_with input args
    let input_args: Vec<proc_macro2::TokenStream> = inputs
        .into_iter()
        .map(|arg| {
            let rewritten: proc_macro2::TokenStream =
                syntax::rewrite_expr(erase.clone(), false, arg.into_token_stream().into()).into();
            rewritten
        })
        .collect();

    let has_inputs = !input_args.is_empty();
    let has_outputs = outputs.is_some();

    if has_inputs || has_outputs {
        let inputs_expr = if input_args.len() == 1 {
            let arg = &input_args[0];
            quote! { #arg }
        } else if input_args.is_empty() {
            quote! { () }
        } else {
            quote! { (#(#input_args),*) }
        };

        let call_expr = expr.to_token_stream();

        if has_outputs {
            let (_, extra_pat) = outputs.unwrap();
            let mut out_pats = Vec::new();
            flatten_output_pat(extra_pat, &mut out_pats);

            // If all outputs are wildcard, just use proof_with (no ret needed)
            let all_wild = out_pats.iter().all(|p| matches!(p, OutputPat::Wild));
            let pre_decls: Vec<proc_macro2::TokenStream> = Vec::new();
            if all_wild {
                *expr = syn::Expr::Verbatim(quote_spanned_builtin!(verus_builtin, expr.span() =>
                    #verus_builtin::proof_with(#inputs_expr, #call_expr)
                ));
            } else {
                // Use proof_with_ret to capture extra outputs.
                // Type annotation uses `_` — user must ensure Rust can infer types
                // (e.g., by annotating their variables explicitly).
                let mut tmp_idents = Vec::new();
                let mut unwrap_stmts = Vec::new();

                let mut tmp_type_annotations: Vec<proc_macro2::TokenStream> = Vec::new();

                for (i, pat) in out_pats.iter().enumerate() {
                    let tmp_ident = syn::Ident::new(
                        &format!("__verus_out_tmp_{i}"),
                        proc_macro2::Span::call_site(),
                    );
                    match pat {
                        OutputPat::Ghost(ident, explicit_ty) => {
                            unwrap_stmts.push(quote! {
                                #[verifier::proof_block]
                                { #ident = #tmp_ident.view(); }
                            });
                            if let Some(ty) = explicit_ty {
                                tmp_type_annotations.push(ty.clone());
                            } else {
                                tmp_type_annotations.push(quote! { Ghost<_> });
                            }
                        }
                        OutputPat::Tracked(ident, explicit_ty) => {
                            unwrap_stmts.push(quote! {
                                #[verifier::proof_block]
                                { #ident = #tmp_ident.get(); }
                            });
                            if let Some(ty) = explicit_ty {
                                tmp_type_annotations.push(ty.clone());
                            } else {
                                tmp_type_annotations.push(quote! { Tracked<_> });
                            }
                        }
                        OutputPat::Wild => {
                            tmp_type_annotations.push(quote! { _ });
                        }
                    }
                    tmp_idents.push(tmp_ident);
                }

                let tmp_pat_tokens = if tmp_idents.len() == 1 {
                    let t = &tmp_idents[0];
                    quote! { (#t,) }
                } else {
                    quote! { (#(#tmp_idents),*) }
                };

                let tmp_type_tokens = if tmp_type_annotations.len() == 1 {
                    let t = &tmp_type_annotations[0];
                    quote! { (#t,) }
                } else {
                    quote! { (#(#tmp_type_annotations),*) }
                };

                *expr = syn::Expr::Verbatim(quote_spanned_builtin!(verus_builtin, expr.span() =>
                    {
                        let (__verus_tmp_expr_var__, #tmp_pat_tokens): (_, #tmp_type_tokens) = #verus_builtin::proof_with_ret(#inputs_expr, #call_expr);
                        #(#unwrap_stmts)*
                        __verus_tmp_expr_var__
                    }
                ));
            }
            return pre_decls;
        } else {
            // Inputs only — use proof_with
            *expr = syn::Expr::Verbatim(quote_spanned_builtin!(verus_builtin, expr.span() =>
                #verus_builtin::proof_with(#inputs_expr, #call_expr)
            ));
        }
    }

    if let Some((_, follow)) = follows {
        apply_follows(expr, follow.into_token_stream());
    }
    vec![]
}

enum OutputPat {
    Ghost(syn::Ident, Option<proc_macro2::TokenStream>),
    Tracked(syn::Ident, Option<proc_macro2::TokenStream>),
    Wild,
}

fn flatten_output_pat(pat: verus_syn::Pat, out: &mut Vec<OutputPat>) {
    match pat {
        verus_syn::Pat::Tuple(tuple) => {
            for elem in tuple.elems {
                flatten_output_pat(elem, out);
            }
        }
        verus_syn::Pat::Type(pat_type) => {
            // Handle `Ghost(z): Ghost<u32>` — extract the explicit type annotation
            let explicit_ty: proc_macro2::TokenStream = pat_type.ty.to_token_stream();
            let inner = *pat_type.pat;
            flatten_output_pat_with_type(inner, Some(explicit_ty), out);
        }
        _ => flatten_output_pat_with_type(pat, None, out),
    }
}

fn flatten_output_pat_with_type(
    pat: verus_syn::Pat,
    explicit_ty: Option<proc_macro2::TokenStream>,
    out: &mut Vec<OutputPat>,
) {
    match pat {
        verus_syn::Pat::Tuple(tuple) => {
            for elem in tuple.elems {
                flatten_output_pat(elem, out);
            }
        }
        verus_syn::Pat::TupleStruct(ts) => {
            let is_ghost = ts.path.is_ident("Ghost");
            let is_tracked = ts.path.is_ident("Tracked");
            if (is_ghost || is_tracked) && ts.elems.len() == 1 {
                if let verus_syn::Pat::Ident(id) = &ts.elems[0] {
                    if is_ghost {
                        out.push(OutputPat::Ghost(
                            syn::Ident::new(&id.ident.to_string(), id.ident.span()),
                            explicit_ty,
                        ));
                    } else {
                        out.push(OutputPat::Tracked(
                            syn::Ident::new(&id.ident.to_string(), id.ident.span()),
                            explicit_ty,
                        ));
                    }
                    return;
                }
            }
            out.push(OutputPat::Wild);
        }
        verus_syn::Pat::Wild(_) => {
            out.push(OutputPat::Wild);
        }
        verus_syn::Pat::Ident(id) => {
            out.push(OutputPat::Ghost(
                syn::Ident::new(&id.ident.to_string(), id.ident.span()),
                explicit_ty,
            ));
        }
        _ => {
            out.push(OutputPat::Wild);
        }
    }
}

/// Rewrite the const function and return a proxy function.
fn rewrite_const_ret_proxy(const_fun: &mut syn::ItemFn) -> syn::ItemFn {
    // This function is used to rewrite a const function to link it to a proxy function
    // that can be used to verify code.
    // It seems that we do not need to erase anything.
    // But just do it to be safe and consistent with verus macro.
    let span = const_fun.sig.constness.unwrap().span();
    let mut proxy_fun = const_fun.clone();
    let inside_external_code = has_external_code_syn(&const_fun.attrs);
    replace_block(EraseGhost::Erase, const_fun.block_mut().unwrap(), inside_external_code);
    const_fun.attrs.push(mk_verifier_attr_syn(span, quote! { external }));
    const_fun.attrs.push(mk_verus_attr_syn(span, quote! { uses_unerased_proxy }));
    const_fun.attrs.push(mk_verus_attr_syn(span, quote! { encoded_const }));

    proxy_fun.sig.ident = syn::Ident::new(
        &format!("{VERUS_UNERASED_PROXY}{}", const_fun.sig.ident),
        const_fun.sig.ident.span(),
    );
    proxy_fun.attrs.push(mk_verus_attr_syn(span, quote! { unerased_proxy }));
    proxy_fun
}
