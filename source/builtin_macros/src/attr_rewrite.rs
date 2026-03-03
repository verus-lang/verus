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
use syn::visit_mut::VisitMut;
use syn::{Expr, Item, ItemConst, parse2, spanned::Spanned};

use crate::{
    EraseGhost,
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax::{self, mk_verifier_attr_syn, mk_verus_attr_syn},
    syntax_trait,
    unerased_proxies::VERUS_UNERASED_PROXY,
};

pub const VERIFIED: &str = "_VERUS_VERIFIED";

pub const DUAL_SPEC_PREFIX: &str = "__VERUS_SPEC";

const VERUS_SPEC: &str = "verus_spec";

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
    const VERIFY_ATTRS: [&str; 3] = ["rlimit", "spinoff_prover", "external_derive"];
    const DUAL_ATTR: &str = "dual_spec";
    const IGNORE_VERIFY_ATTRS: [&str; 2] = ["external", "external_body"];

    for arg in &args {
        let path = arg.path().get_ident().expect("Invalid verus verifier attribute");
        if IGNORE_VERIFY_ATTRS.contains(&path.to_string().as_str()) {
            contains_external = true;
            attributes.push(quote_spanned!(arg.span() => #[verifier::#arg]));
        } else if VERIFY_ATTRS.contains(&path.to_string().as_str()) {
            contains_non_external = true;
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
                replace_block(EraseGhost::Erase, spec_f.block_mut().unwrap());
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

    // Special handling for impl blocks, add marker attribute to each method for `#[verus_spec]`.
    let mut impl_item_replacer = ImplItemReplacer { verify_const: true };
    impl_item_replacer.visit_item_mut(&mut item);

    let mut new_stream = quote_spanned! {item.span()=>
        #(#attributes)*
        #item
    };
    spec_fun.map(|f| f.to_tokens(&mut new_stream));
    new_stream.into()
}

struct ExecReplacer {
    erase: EraseGhost,
}

impl VisitMut for ExecReplacer {
    // Enable the hack only when needed
    #[cfg(feature = "vpanic")]
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        syn::visit_mut::visit_macro_mut(self, mac);
        // Only replace in verification mode
        if !self.erase.keep() {
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
    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        syn::visit_mut::visit_block_mut(self, block);

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
                    panic!("Expected a function call after proof_with! macro");
                }
            };
        }
    }
}

struct ImplItemReplacer {
    verify_const: bool,
}

fn get_verus_spec(attrs: &[syn::Attribute]) -> Option<&syn::Attribute> {
    attrs.iter().find(|attr| attr.path().get_ident().map_or(false, |ident| ident == VERUS_SPEC))
}

impl VisitMut for ImplItemReplacer {
    fn visit_impl_item_fn_mut(&mut self, method: &mut syn::ImplItemFn) {
        syn::visit_mut::visit_impl_item_fn_mut(self, method);
        // Help verus_spec be aware that it is in impl function.
        if let Some(verus_spec) = get_verus_spec(&method.attrs) {
            let span = verus_spec.span();
            method.attrs.push(crate::syntax::mk_rust_attr_syn(
                span,
                "allow",
                quote_spanned! { span => (unused, verus_impl_method_marker)},
            ));
        }
    }

    fn visit_impl_item_const_mut(&mut self, i: &mut syn::ImplItemConst) {
        syn::visit_mut::visit_impl_item_const_mut(self, i);
        if !self.verify_const {
            return;
        }
        // Add verus_spec if not exists
        if get_verus_spec(&i.attrs).is_none() {
            i.attrs.push(crate::syntax::mk_rust_attr_syn(i.span(), VERUS_SPEC, TokenStream::new()));
        }
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
pub(crate) fn replace_block(erase: EraseGhost, fblock: &mut syn::Block) {
    let mut replacer = ExecReplacer { erase };
    replacer.visit_block_mut(fblock);
}

pub(crate) fn replace_expr(erase: EraseGhost, expr: &mut syn::Expr) {
    let mut replacer = ExecReplacer { erase };
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
    crate::syntax::rewrite_items(verus_item_const.to_token_stream().into(), erase_ghost, true)
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

            // Create a copy of unverified function.
            // To avoid misuse of the unverified function,
            // we add `requires false` and thus prevent verified function to use it.
            // Allow unverified code to use the function without changing in/output.
            if let Some(with) = &spec_attr.spec.with {
                let extra_funs = rewrite_unverified_func(&mut fun, with.with.span(), erase);
                extra_funs.iter().for_each(|f| f.to_tokens(&mut new_stream));
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
            replace_block(erase, fun.block_mut().unwrap());
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

// Expand `with extra_in => extra_out` on a method call expr.
// Return some pre-statements that needs to be declared before the expr.
fn rewrite_with_expr(
    erase: EraseGhost,
    expr: &mut Expr,
    call_with_spec: verus_syn::WithSpecOnExpr,
) -> Vec<verus_syn::Stmt> {
    let verus_syn::WithSpecOnExpr { inputs, outputs, follows, .. } = call_with_spec;
    if outputs.is_some() || inputs.len() > 0 {
        match expr {
            syn::Expr::Call(syn::ExprCall { func, .. }) => {
                if let Expr::Path(path) = func.as_mut() {
                    let x = &path.path.segments.last().unwrap().ident;
                    path.path.segments.last_mut().unwrap().ident =
                        syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
                }
            }
            syn::Expr::MethodCall(syn::ExprMethodCall { method, .. }) => {
                let x = &method;
                *method = syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
            }
            syn::Expr::Try(syn::ExprTry { expr, .. }) => {
                let call_with_spec =
                    verus_syn::WithSpecOnExpr { inputs, outputs, follows, ..call_with_spec };
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

    match expr {
        syn::Expr::Call(syn::ExprCall { args, .. })
        | syn::Expr::MethodCall(syn::ExprMethodCall { args, .. }) => {
            for arg in inputs {
                let arg =
                    syntax::rewrite_expr(erase.clone(), false, arg.into_token_stream().into());
                args.push(syn::Expr::Verbatim(arg.into()));
            }
        }
        _ => {}
    };
    let x_declares = if let Some((_, extra_pat)) = outputs {
        // The expected pat.
        let tmp_pat =
            verus_syn::Pat::Verbatim(quote_spanned! {expr.span() => __verus_tmp_expr_var__});
        let mut elems =
            verus_syn::punctuated::Punctuated::<verus_syn::Pat, verus_syn::Token![,]>::new();
        elems.push(tmp_pat.clone());
        elems.push(extra_pat);
        // The actual pat.
        let mut pat = verus_syn::Pat::Tuple(verus_syn::PatTuple {
            attrs: vec![],
            paren_token: verus_syn::token::Paren::default(),
            elems,
        });
        let (x_declares, x_assigns) = syntax::rewrite_exe_pat(&mut pat);
        *expr = syn::Expr::Verbatim(quote_spanned! {expr.span() => {
            let #pat = #expr;
            proof!{
                #(#x_assigns)*
            }
            #tmp_pat
        }
        });
        x_declares
    } else {
        vec![]
    };
    if let Some((_, follow)) = follows {
        let follow: TokenStream =
            syntax::rewrite_expr(erase.clone(), false, follow.into_token_stream().into()).into();
        *expr = Expr::Verbatim(quote_spanned!(expr.span() => (#expr, #follow)));
    }
    x_declares
}

/// Rewrite the const function and return a proxy function.
fn rewrite_const_ret_proxy(const_fun: &mut syn::ItemFn) -> syn::ItemFn {
    // This function is used to rewrite a const function to link it to a proxy function
    // that can be used to verify code.
    // It seems that we do not need to erase anything.
    // But just do it to be safe and consistent with verus macro.
    let span = const_fun.sig.constness.unwrap().span();
    let mut proxy_fun = const_fun.clone();
    replace_block(EraseGhost::Erase, const_fun.block_mut().unwrap());
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

// Create a copy of function with unverified function signature without a
// function body, to enable seamless use of unverified call to the function in
// verification.
// If the function is const, it will be rewritten to a proxy function and a verified function.
fn rewrite_unverified_func(
    fun: &mut syn::ItemFn,
    span: proc_macro2::Span,
    erase: EraseGhost,
) -> Vec<syn::ItemFn> {
    let mut ret = vec![];
    let mut unverified_fun = fun.clone();
    if fun.sig.constness.is_some() {
        // Create a proxy function to include requires/ensures.
        let proxy = rewrite_const_ret_proxy(&mut unverified_fun);
        ret.push(unverified_fun);
        unverified_fun = proxy;
    }
    let unimplemented = syn::Stmt::Expr(
        syn::Expr::Verbatim(quote_spanned! {span => unimplemented!()}),
        Some(syn::token::Semi { spans: [span] }),
    );
    let precondition_false = syn::Stmt::Expr(
        syn::Expr::Verbatim(
            quote_spanned_builtin!(verus_builtin, span => #verus_builtin::requires([false])),
        ),
        Some(syn::token::Semi { spans: [span] }),
    );
    unverified_fun.attrs_mut().push(mk_verus_attr_syn(span, quote! { external_body }));
    if let Some(block) = unverified_fun.block_mut() {
        // For an unverified function, if it is in keep mode,
        // we erase the function body to avoid using
        // proof code, since we do not need to verify anything in unverified
        // function and we never pass ghost/tracked to unverified function
        // and so it may cause errors due to undefined vars.
        // Since the body is erased only in keep mode, we still
        // see correct body in generated executable in erase mode.
        if erase.keep() {
            block.stmts.clear();
            block.stmts.push(precondition_false);
            block.stmts.push(unimplemented.clone());
        }
    }
    // change name to verified_{fname}
    let x = &fun.sig.ident;
    fun.sig.ident = syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
    fun.attrs.push(crate::syntax::mk_rust_attr_syn(span, "allow", quote! {non_snake_case}));

    // In erase mode, we just keep the verified function with unimplemented!()
    // since we do not need to verifying the function body and only unverified
    // function is called in erase mode.
    if erase.erase() {
        fun.block.stmts.clear();
        fun.block.stmts.push(unimplemented);
    }
    ret.push(unverified_fun);
    ret
}
