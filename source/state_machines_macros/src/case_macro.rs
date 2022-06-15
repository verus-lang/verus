use proc_macro2::TokenStream;
use quote::quote;
use syn::parse;
use syn::parse::{Parse, ParseStream};
use syn::parse_macro_input;
use syn::punctuated::Punctuated;
use syn::token;
use syn::{braced, parenthesized, Expr, ExprBlock, Ident, Path, Token};

pub fn case_on(input: proc_macro::TokenStream, is_init: bool) -> proc_macro::TokenStream {
    let (pre_post, name, arms) = if is_init {
        let m: MatchPost = parse_macro_input!(input as MatchPost);
        let MatchPost { post, name, arms } = m;
        let pre_post = quote! {#post};
        (pre_post, name, arms)
    } else {
        let m: MatchPrePost = parse_macro_input!(input as MatchPrePost);
        let MatchPrePost { pre, post, name, arms } = m;
        let pre_post = quote! {#pre, #post};
        (pre_post, name, arms)
    };

    let next_by = if is_init {
        quote! { #name::State::init_by }
    } else {
        quote! { #name::State::next_by }
    };

    let next = if is_init {
        quote! { #name::State::init }
    } else {
        quote! { #name::State::next }
    };

    let step = if is_init {
        quote! { #name::Config }
    } else {
        quote! { #name::Step }
    };

    let arms: Vec<TokenStream> = arms
        .into_iter()
        .map(|arm| {
            let Arm { step_name, params, block } = arm;
            quote! {
                #step::#step_name(#(#params),*) => {
                    ::builtin::assert_by(#name::State::#step_name(#pre_post, #(#params),*), {
                        ::builtin::reveal(#next_by);
                    });
                    #block
                }
            }
        })
        .collect();

    let res = quote! {
        ::builtin::reveal(#next);
        match ::builtin::choose(|step: #step| #next_by(#pre_post, step)) {
            #step::dummy_to_use_type_params(_) => {
                ::builtin::assert_by(false, {
                    ::builtin::reveal(#next_by);
                });
            }
            #( #arms )*
        }
    };

    res.into()
}

struct MatchPost {
    post: Expr,
    name: Path,
    arms: Vec<Arm>,
}

struct MatchPrePost {
    pre: Expr,
    post: Expr,
    name: Path,
    arms: Vec<Arm>,
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
        let name: Path = input.parse()?;
        let _: Token![=>] = input.parse()?;

        let content;
        let _ = braced!(content in input);
        let mut arms = Vec::new();
        while !content.is_empty() {
            let arm = parse_arm(&content)?;
            arms.push(arm);
        }

        Ok(MatchPost { post, name, arms })
    }
}

impl Parse for MatchPrePost {
    fn parse(input: ParseStream) -> parse::Result<MatchPrePost> {
        let pre: Expr = input.parse()?;
        let _: Token![,] = input.parse()?;
        let post: Expr = input.parse()?;
        let _: Token![,] = input.parse()?;
        let name: Path = input.parse()?;
        let _: Token![=>] = input.parse()?;

        let content;
        let _ = braced!(content in input);
        let mut arms = Vec::new();
        while !content.is_empty() {
            let arm = parse_arm(&content)?;
            arms.push(arm);
        }

        Ok(MatchPrePost { pre, post, name, arms })
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
        ::builtin::reveal($name::State::next);
        match ::builtin::choose(|step: $name::Step| $name::State::next_by($pre, $post, step)) {
            $(
                $name::Step::$sname($($p),*) => {
                    ::builtin::assert_by($name::State::add($pre, $post, $($p),*), {
                        ::builtin::reveal($name::State::next_by);
                    });
                    $b
                }
            )*
        }
    }
}
*/
