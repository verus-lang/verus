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
///   Thus, this module uses syn instead of syn_verus in most cases.
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
use syn::{Expr, Item, parse2, spanned::Spanned};

use crate::{
    EraseGhost,
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax,
    syntax::mk_verus_attr_syn,
};

pub const VERIFIED: &str = "_VERUS_VERIFIED";

pub const DUAL_SPEC_PREFIX: &str = "__VERUS_SPEC";

enum VerusIOTarget {
    Local(syn::Local),
    Expr(syn::Expr),
}
enum VerusSpecTarget {
    IOTarget(VerusIOTarget),
    FnOrLoop(AnyFnOrLoop),
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

        let expr: Expr = input.parse()?;
        return Ok(VerusSpecTarget::IOTarget(VerusIOTarget::Expr(expr)));
    }
}

pub fn rewrite_verus_attribute(
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
    const VERIFY_ATTRS: [&str; 2] = ["rlimit", "spinoff_prover"];
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
                        &format!("{DUAL_SPEC_PREFIX}_{}", f.sig.ident.to_string()),
                        f.sig.ident.span(),
                    )
                };
                spec_f.sig.ident = ident.clone();
                spec_f.attrs = vec![mk_verus_attr_syn(f.span(), quote! { spec })];
                // remove proof-related macros
                spec_f.block.as_mut().stmts.retain(|stmt| !is_verus_proof_stmt(stmt));
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

    let mut new_stream = quote_spanned! {item.span()=>
        #(#attributes)*
        #item
    };
    spec_fun.map(|f| f.to_tokens(&mut new_stream));
    new_stream.into()
}

use syn::visit_mut::VisitMut;

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
            if last.ident == "verus_spec" {
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

        if !self.erase.keep() {
            return;
        }

        let mut with_args: TokenStream = TokenStream::new();
        for stmt in &mut block.stmts {
            match stmt {
                syn::Stmt::Macro(syn::StmtMacro { mac, .. }) if mac.path.is_ident("proof_with") => {
                    syn_verus::Token![with](mac.span()).to_tokens(&mut with_args);
                    mac.tokens.to_tokens(&mut with_args);
                }
                syn::Stmt::Local(syn::Local { attrs, init: Some(_), .. })
                    if !with_args.is_empty() =>
                {
                    attrs.push(crate::syntax::mk_rust_attr_syn(
                        with_args.span(),
                        "verus_spec",
                        with_args,
                    ));
                    with_args = TokenStream::new();
                }
                syn::Stmt::Expr(expr, _) if !with_args.is_empty() => {
                    let call_with_spec = syn_verus::parse2(with_args.clone())
                        .expect(format!("Failed to parse proof_with {:?}", with_args).as_str());
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
pub fn replace_block(erase: EraseGhost, fblock: &mut syn::Block) {
    let mut replacer = ExecReplacer { erase };
    replacer.visit_block_mut(fblock);
}

pub fn replace_expr(erase: EraseGhost, expr: &mut syn::Expr) {
    let mut replacer = ExecReplacer { erase };
    replacer.visit_expr_mut(expr);
}

pub fn rewrite_verus_spec(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    if !erase.keep() {
        return input;
    }
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

pub fn rewrite_verus_spec_on_fun_or_loop(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    f: AnyFnOrLoop,
) -> proc_macro::TokenStream {
    match f {
        AnyFnOrLoop::Fn(mut fun) => {
            // Note: trait default methods appear in this case,
            // since they look syntactically like non-trait functions
            replace_block(erase, fun.block_mut().unwrap());
            let spec_attr =
                syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::SignatureSpecAttr);

            fun.attrs.push(mk_verus_attr_syn(fun.span(), quote! { verus_macro }));

            // Create a copy of unverified function.
            // To avoid misuse of the unverified function,
            // we add `requires false` and thus prevent verified function to use it.
            // Allow unverified code to use the function without changing in/output.
            let mut new_stream = TokenStream::new();
            if let Some(with) = &spec_attr.spec.with {
                let unverified_fun = rewrite_unverified_func(&mut fun, with.with.span());
                unverified_fun.to_tokens(&mut new_stream);
            }
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut fun.sig);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let _ = fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            fun.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        AnyFnOrLoop::Closure(mut closure) => {
            replace_expr(erase, &mut closure.body);
            let mut spec_attr =
                syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::SignatureSpecAttr);
            if let Some(_) = &spec_attr.spec.with {
                return quote_spanned! {spec_attr.span() => compile_error!("`with` does not support closure")}.into();
            }
            if let Some((syn_verus::Pat::Type(pat_ty), ar)) = spec_attr.ret_pat {
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
            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut signature);
            let body = &closure.body;
            let new_body = quote_spanned!(closure.body.span() =>
                #(#spec_stmts)*
                {#body}
            );
            closure.body = Box::new(Expr::Verbatim(new_body));
            closure.to_token_stream().into()
        }
        AnyFnOrLoop::TraitMethod(mut method) => {
            // Note: default trait methods appear in the AnyFnOrLoop::Fn case, not here
            let spec_attr =
                syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::SignatureSpecAttr);
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

            let spec_stmts = syntax::sig_specs_attr(erase, spec_attr, &mut method.sig);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            let mut spec_fun_opt = syntax::split_trait_method_syn(&method, erase.erase());
            let spec_fun = spec_fun_opt.as_mut().unwrap_or(&mut method);
            let _ = spec_fun.block_mut().unwrap().stmts.splice(0..0, new_stmts);
            method.attrs.push(mk_verus_attr_syn(method.span(), quote! { verus_macro }));
            spec_fun_opt.to_tokens(&mut new_stream);
            method.to_tokens(&mut new_stream);
            proc_macro::TokenStream::from(new_stream)
        }
        AnyFnOrLoop::ForLoop(forloop) => {
            let spec_attr = syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::LoopSpec);
            syntax::for_loop_spec_attr(erase, spec_attr, forloop).to_token_stream().into()
        }
        AnyFnOrLoop::Loop(mut l) => {
            let spec_attr = syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
        AnyFnOrLoop::While(mut l) => {
            let spec_attr = syn_verus::parse_macro_input!(outer_attr_tokens as syn_verus::LoopSpec);
            let spec_stmts = syntax::while_loop_spec_attr(erase, spec_attr);
            let new_stmts = spec_stmts.into_iter().map(|s| parse2(quote! { #s }).unwrap());
            if erase.keep() {
                l.body.stmts.splice(0..0, new_stmts);
            }
            l.to_token_stream().into()
        }
    }
}

pub fn proof_rewrite(erase: EraseGhost, input: TokenStream) -> proc_macro::TokenStream {
    if erase.keep() {
        let block: TokenStream =
            syntax::proof_block(erase, quote_spanned!(input.span() => {#input}).into()).into();
        quote! {
            #[verifier::proof_block]
            {
                #[verus::internal(const_header_wrapper)]||#block;
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
    let call_with_spec = syn_verus::parse_macro_input!(attr_input as syn_verus::WithSpecOnExpr);
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
    call_with_spec: syn_verus::WithSpecOnExpr,
) -> Vec<syn_verus::Stmt> {
    let syn_verus::WithSpecOnExpr { inputs, outputs, follows, .. } = call_with_spec;
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
            _ => {}
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
            syn_verus::Pat::Verbatim(quote_spanned! {expr.span() => __verus_tmp_expr_var__});
        let mut elems =
            syn_verus::punctuated::Punctuated::<syn_verus::Pat, syn_verus::Token![,]>::new();
        elems.push(tmp_pat.clone());
        elems.push(extra_pat);
        // The actual pat.
        let mut pat = syn_verus::Pat::Tuple(syn_verus::PatTuple {
            attrs: vec![],
            paren_token: syn_verus::token::Paren::default(),
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

// Create a copy of function with unverified function signature without a
// function body, to enable seamless use of unverified call to the function in
// verification.
fn rewrite_unverified_func(fun: &mut syn::ItemFn, span: proc_macro2::Span) -> syn::ItemFn {
    let mut unverified_fun = fun.clone();
    let stmts = vec![
        syn::Stmt::Expr(
            syn::Expr::Verbatim(
                quote_spanned_builtin!(builtin, span => #builtin::requires([false])),
            ),
            Some(syn::token::Semi { spans: [span] }),
        ),
        syn::Stmt::Expr(
            syn::Expr::Verbatim(quote_spanned! {span => unimplemented!()}),
            Some(syn::token::Semi { spans: [span] }),
        ),
    ];
    unverified_fun.attrs_mut().push(mk_verus_attr_syn(span, quote! { external_body }));
    if let Some(block) = unverified_fun.block_mut() {
        block.stmts.clear();
        block.stmts.extend(stmts);
    }
    // change name to verified_{fname}
    let x = &fun.sig.ident;
    fun.sig.ident = syn::Ident::new(&format!("{VERIFIED}_{x}"), x.span());
    unverified_fun
}
