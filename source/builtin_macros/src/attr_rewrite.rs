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
///   To pass and get tracked/ghost from function call, use #[verus_io(with ...)] in
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
/// - Refer to `example/syntax_attr.rs`.
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse2, spanned::Spanned, Expr, Item};

use crate::{
    attr_block_trait::{AnyAttrBlock, AnyFnOrLoop},
    syntax,
    syntax::mk_verus_attr_syn,
    EraseGhost,
};

pub const VERIFIED: &str = "_VERUS_VERIFIED";

pub fn rewrite_verus_attribute(
    erase: &EraseGhost,
    attr_args: Vec<syn::Ident>,
    input: TokenStream,
) -> TokenStream {
    if erase.keep() {
        let item: Item = parse2(input).expect("#[verus_verify] must be applied to an item");
        let mut attributes = Vec::new();
        const VERIFIER_ATTRS: [&str; 2] = ["external", "external_body"];
        for arg in attr_args {
            if VERIFIER_ATTRS.contains(&arg.to_string().as_str()) {
                attributes.push(mk_verus_attr_syn(arg.span(), quote! { #arg }));
            } else {
                let span = arg.span();
                return proc_macro2::TokenStream::from(quote_spanned!(span =>
                    compile_error!("unsupported parameters {:?} in #[verus_verify(...)]");
                ));
            }
        }
        if attributes.len() == 0 {
            attributes.push(mk_verus_attr_syn(item.span(), quote! { verus_macro }));
        }

        quote_spanned! {item.span()=>
            #(#attributes)*
            #item
        }
    } else {
        input
    }
}

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

pub fn rewrite_verus_spec(
    erase: EraseGhost,
    outer_attr_tokens: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let f = match syn::parse::<AnyFnOrLoop>(input) {
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
        AnyFnOrLoop::Fn(mut fun) => {
            // Note: trait default methods appear in this case,
            // since they look syntactically like non-trait functions
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

enum VerusIOTarget {
    Local(syn::Local),
    Expr(syn::Expr),
}

impl syn::parse::Parse for VerusIOTarget {
    fn parse(input: syn::parse::ParseStream) -> syn::parse::Result<VerusIOTarget> {
        use syn::parse::discouraged::Speculative;
        let fork = input.fork();
        if let Ok(stmt) = fork.parse() {
            if let syn::Stmt::Local(local) = stmt {
                input.advance_to(&fork);
                return Ok(VerusIOTarget::Local(local));
            }
        }

        let expr: Expr = input.parse().expect("Need stmt local or expr");
        return Ok(VerusIOTarget::Expr(expr));
    }
}

/// The `verus_io(with)` annotation can be applied to either a local statement or an expression.
///
/// - When applied to an expression (`expr`), the trailing semicolon (`;`) is ignored due to limitations of the procedure macro.
///   To include the semicolon, developers must use the following syntax:
///   ```rust
///   {#[verus_io] expr};
///   ```
///
/// - When used with an expression, developers must explicitly declare the returned ghost or tracked patterns.
///   This is because the additional declarations cannot be automatically added in a meaningful way.
///
/// Example:
/// ```rust
/// if #[verus_io(with Tracked(arg1), Ghost(arg2) => Tracked(out) @ Tracked(extra))]
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
/// #[verus_io(with Tracked(arg1), Ghost(arg2) => Tracked(out) @ Tracked(extra))]
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
pub(crate) fn verus_io(
    erase: &EraseGhost,
    attr_input: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> Result<proc_macro::TokenStream, syn::Error> {
    if !erase.keep() {
        return Ok(input);
    }
    let mut target = syn::parse::<VerusIOTarget>(input).expect("failed to parse Stmt verusio");
    let call_with_spec = syn_verus::parse::<syn_verus::CallWithSpec>(attr_input)
        .expect("failed to parse CallWithSpec");
    let tokens = match &mut target {
        VerusIOTarget::Local(local) => {
            let syn::Local { init, .. } = local;
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
        VerusIOTarget::Expr(e) => {
            rewrite_with_expr(erase, e, call_with_spec);
            e.into_token_stream().into()
        }
    };
    Ok(tokens.into())
}

// Return some pre-statements
fn rewrite_with_expr(
    erase: &EraseGhost,
    expr: &mut Expr,
    call_with_spec: syn_verus::CallWithSpec,
) -> Vec<syn_verus::Stmt> {
    let syn_verus::CallWithSpec { inputs, outputs, follows, .. } = call_with_spec;
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
