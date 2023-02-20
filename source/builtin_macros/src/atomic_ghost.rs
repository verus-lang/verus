use crate::struct_decl_inv::keyword;
use crate::struct_decl_inv::peek_keyword;
///! Helper proc-macro for the atomic_ghost lib
use proc_macro2::TokenStream;
use quote::quote;
use syn_verus::parse;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::parse_macro_input;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::Token;
use syn_verus::{parenthesized, Block, Error, Expr, Ident};

pub fn atomic_ghost(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ag: AG = parse_macro_input!(input as AG);
    match atomic_ghost_main(ag) {
        Ok(t) => t.into(),
        Err(err) => proc_macro::TokenStream::from(err.to_compile_error()),
    }
}

struct AG {
    pub atomic: Expr,
    pub op_name: Ident,
    pub operands: Vec<Expr>,
    pub prev_next: Option<(Ident, Ident)>,
    pub ret: Option<Ident>,
    pub ghost_name: Ident,
    pub block: Block,
}

impl Parse for AG {
    fn parse(input: ParseStream) -> parse::Result<AG> {
        let atomic: Expr = input.parse()?;
        let _: Token![=>] = input.parse()?;
        let op_name: Ident = input.parse()?;

        let paren_content;
        let _ = parenthesized!(paren_content in input);

        let operands: Punctuated<Expr, token::Comma> =
            paren_content.parse_terminated(Expr::parse)?;
        let operands: Vec<Expr> = operands.into_iter().collect();

        let _: Token![;] = input.parse()?;

        let prev_next = if peek_keyword(input.cursor(), "update") {
            let _ = keyword(input, "update");
            let prev: Ident = input.parse()?;
            let _: Token![->] = input.parse()?;
            let next: Ident = input.parse()?;
            let _: Token![;] = input.parse()?;
            Some((prev, next))
        } else {
            None
        };

        let ret = if peek_keyword(input.cursor(), "returning") {
            let _ = keyword(input, "returning");
            let ret: Ident = input.parse()?;
            let _: Token![;] = input.parse()?;
            Some(ret)
        } else {
            None
        };

        let _ = keyword(input, "ghost");

        let ghost_name: Ident = input.parse()?;
        let _: Token![=>] = input.parse()?;
        let block: Block = input.parse()?;

        Ok(AG { atomic, op_name, operands, prev_next, ret, ghost_name, block })
    }
}

fn atomic_ghost_main(ag: AG) -> parse::Result<TokenStream> {
    // valid op names and the # of arguments they take
    // see the documentation in the verus atomic_ghost lib
    let ops = vec![
        ("load", 0),
        ("store", 1),
        ("swap", 1),
        ("compare_exchange", 2),
        ("fetch_add", 1),
        ("fetch_add_wrapping", 1),
        ("fetch_sub", 1),
        ("fetch_sub_wrapping", 1),
        ("fetch_or", 1),
        ("fetch_and", 1),
        ("fetch_xor", 1),
        ("fetch_nand", 1),
        ("fetch_max", 1),
        ("fetch_min", 1),
        ("no_op", 0),
    ];

    let op_name = ag.op_name.to_string();
    match ops.iter().find(|p| &op_name == p.0) {
        None => {
            let valid_ops: Vec<&str> = ops.iter().map(|p| p.0).collect();
            let valid_ops = valid_ops.join(", ");

            Err(Error::new(
                op_name.span(),
                &format!(
                    "atomic_with_ghost: `{:}` is not a recognized operation (valid operations are: {:})",
                    op_name.to_string(),
                    valid_ops
                ),
            ))
        }
        Some((_, num_args)) if *num_args != ag.operands.len() => Err(Error::new(
            op_name.span(),
            &format!(
                "atomic_with_ghost: `{:}` expected {:} arguments (found {:})",
                op_name.to_string(),
                num_args,
                ag.operands.len()
            ),
        )),
        Some((_, _)) => {
            let AG { atomic, op_name, operands, prev_next, ret, ghost_name, block } = ag;

            let (prev, next) = match prev_next {
                Some((p, n)) => (quote! { #p }, quote! { #n }),
                None => (quote! { _ }, quote! { _ }),
            };

            let ret = match ret {
                Some(r) => quote! { #r },
                None => quote! { _ },
            };

            Ok(quote! {
                crate::pervasive::atomic_ghost::atomic_with_ghost_inner!(
                    #op_name,
                    #atomic,
                    (#(#operands),*),
                    #prev,
                    #next,
                    #ret,
                    #ghost_name,
                    #block
                )
            })
        }
    }
}
