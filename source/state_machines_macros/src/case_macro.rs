use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::parse_macro_input;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::{braced, parenthesized, Error, Expr, ExprBlock, ExprPath, Ident, Path, Token};
use syn_verus::{parse, PathArguments};

pub fn case_on(
    input: proc_macro::TokenStream,
    is_init: bool,
    is_strong: bool,
) -> proc_macro::TokenStream {
    assert!(!is_init || !is_strong);

    let (pre_post, label, mut name, arms) = if is_init {
        let m: MatchPost = parse_macro_input!(input as MatchPost);
        let MatchPost { post, label, name, arms } = m;
        let pre_post = quote! {#post};
        (pre_post, label, name, arms)
    } else {
        let m: MatchPrePost = parse_macro_input!(input as MatchPrePost);
        let MatchPrePost { pre, post, label, name, arms } = m;
        let pre_post = quote! {#pre, #post};
        (pre_post, label, name, arms)
    };

    let mut name_path_last = name.segments.last_mut();
    let name_path_args = &mut name_path_last.as_mut().unwrap().arguments;
    let path_arguments = name_path_args.clone();
    *name_path_args = PathArguments::None;

    let next_by = if is_init {
        quote! { #name::State#path_arguments::init_by }
    } else {
        if is_strong {
            quote! { #name::State#path_arguments::next_strong_by }
        } else {
            quote! { #name::State#path_arguments::next_by }
        }
    };

    let reveal_next_by = if is_init {
        quote! { #name::State::init_by }
    } else {
        if is_strong {
            quote! { #name::State::next_strong_by }
        } else {
            quote! { #name::State::next_by }
        }
    };

    let reveal_next = if is_init {
        quote! { #name::State::init }
    } else {
        if is_strong {
            quote! { #name::State::next_strong }
        } else {
            quote! { #name::State::next }
        }
    };

    let step = if is_init {
        quote! { #name::Config#path_arguments }
    } else {
        quote! { #name::Step#path_arguments }
    };

    let label_arg = match label {
        None => TokenStream::new(),
        Some(l) => quote_spanned! { l.span() => #l , },
    };

    let arms: Vec<TokenStream> = arms
        .into_iter()
        .map(|arm| {
            let Arm { step_name, params, block } = arm;
            let relation_name = if is_strong {
                Ident::new(&(step_name.to_string() + "_strong"), step_name.span())
            } else {
                step_name.clone()
            };
            quote! {
                #step::#step_name(#(#params),*) => {
                    ::builtin::assert_by(#name::State::#relation_name(#pre_post, #label_arg #(#params),*), {
                        reveal(#reveal_next_by);
                    });
                    #block
                }
            }
        })
        .collect();

    let res = quote! {
        ::builtin_macros::verus_proof_expr!{
            {
                reveal(#reveal_next);
                match (choose |step: #step| #next_by(#pre_post, #label_arg step)) {
                    #step::dummy_to_use_type_params(_) => {
                        ::builtin::assert_by(false, {
                            reveal(#reveal_next_by);
                        });
                    }
                    #( #arms )*
                }
            }
        }
    };

    res.into()
}

struct MatchPost {
    post: Expr,
    name: Path,
    arms: Vec<Arm>,
    label: Option<Expr>,
}

struct MatchPrePost {
    pre: Expr,
    post: Expr,
    name: Path,
    arms: Vec<Arm>,
    label: Option<Expr>,
}

struct Arm {
    step_name: Ident,
    params: Vec<Ident>,
    block: ExprBlock,
}

impl Parse for MatchPost {
    fn parse(input: ParseStream) -> parse::Result<MatchPost> {
        let post: Expr = input.parse()?;
        let _: Token![,] = input.parse()?;

        let next_arg: Expr = input.parse()?;

        let label;
        let name;

        if input.peek(Token![,]) {
            let _: Token![,] = input.parse()?;
            let path: Path = input.parse()?;
            let _: Token![=>] = input.parse()?;

            name = path;
            label = Some(next_arg);
        } else {
            let _: Token![=>] = input.parse()?;

            label = None;
            name = match next_arg {
                Expr::Path(ExprPath { attrs, qself: None, path }) if attrs.len() == 0 => path,
                _ => {
                    return Err(Error::new(
                        next_arg.span(),
                        "expected path for the transition system being cased on",
                    ));
                }
            }
        }

        let content;
        let _ = braced!(content in input);
        let mut arms = Vec::new();
        while !content.is_empty() {
            let arm = parse_arm(&content)?;
            arms.push(arm);
        }

        Ok(MatchPost { post, label, name, arms })
    }
}

impl Parse for MatchPrePost {
    fn parse(input: ParseStream) -> parse::Result<MatchPrePost> {
        let pre: Expr = input.parse()?;
        let _: Token![,] = input.parse()?;
        let post: Expr = input.parse()?;
        let _: Token![,] = input.parse()?;

        let next_arg: Expr = input.parse()?;

        let label;
        let name;

        if input.peek(Token![,]) {
            let _: Token![,] = input.parse()?;
            let path: Path = input.parse()?;
            let _: Token![=>] = input.parse()?;

            name = path;
            label = Some(next_arg);
        } else {
            let _: Token![=>] = input.parse()?;

            label = None;
            name = match next_arg {
                Expr::Path(ExprPath { attrs, qself: None, path }) if attrs.len() == 0 => path,
                _ => {
                    return Err(Error::new(
                        next_arg.span(),
                        "expected path for the transition system being cased on",
                    ));
                }
            }
        }

        let content;
        let _ = braced!(content in input);
        let mut arms = Vec::new();
        while !content.is_empty() {
            let arm = parse_arm(&content)?;
            arms.push(arm);
        }

        Ok(MatchPrePost { pre, post, label, name, arms })
    }
}

fn parse_arm(input: ParseStream) -> parse::Result<Arm> {
    let step_name: Ident = input.parse()?;

    let param_stream;
    let _ = parenthesized!(param_stream in input);
    let params: Punctuated<Ident, token::Comma> = param_stream.parse_terminated(Ident::parse)?;

    let _: Token![=>] = input.parse()?;
    let block: ExprBlock = input.parse()?;

    let params = params.into_iter().collect();

    Ok(Arm { step_name, params, block })
}

/* Original attempt at making this macro with macro_rules!, just for reference:
   (It seems like it's not possible to compose `path` arguments the way I tried here.)

#[macro_export]
macro_rules! case_on_next {
    {$pre:expr, $post:expr, $name:path => {
        $( $sname:ident ($($p:ident),*) => $b:block )*
    }} => {
        #vstd::prelude::reveal($name::State::next);
        match #vstd::prelude::choose(|step: $name::Step| $name::State::next_by($pre, $post, step)) {
            $(
                $name::Step::$sname($($p),*) => {
                    #vstd::prelude::assert_by($name::State::add($pre, $post, $($p),*), {
                        #vstd::prelude::reveal($name::State::next_by);
                    });
                    $b
                }
            )*
        }
    }
}
*/
