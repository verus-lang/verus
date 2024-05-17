use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::quote;
use quote::ToTokens;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::parse_macro_input;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::ExprBlock;
use syn_verus::Token;
use syn_verus::{parenthesized, Block, Expr};

use crate::cfg_erase;
use crate::syntax::rewrite_expr;

fn rewrite_expr_to_token_stream(expr: &Expr) -> TokenStream {
    TokenStream::from(rewrite_expr(cfg_erase(), true, expr.to_token_stream().into()))
}

pub fn calc_macro(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as CalcInput);

    let mut output_steps = vec![];
    for (i, (expr, op, block)) in input.steps.iter().enumerate() {
        let next_expr = input.steps.get(i + 1).map(|x| &x.0).unwrap_or(&input.last);
        let op = op.as_ref().unwrap_or(&input.reln);
        let op_expr = op.op.to_expr(expr, next_expr);
        let block = rewrite_expr_to_token_stream(&Expr::Block(ExprBlock {
            attrs: vec![],
            label: None,
            block: block.clone(),
        }));
        output_steps
            .push(quote_spanned_builtin! (builtin, block.span() => #builtin::assert_by(#op_expr, { #block })));
    }
    let combined_block = quote! {
        #(#output_steps);*
    };
    let top_level = input.reln.op.to_expr(&input.steps[0].0, &input.last);
    quote_builtin!(builtin => #builtin::assert_by(#top_level, { #combined_block });).into()
}

#[derive(Debug)]
struct CalcInput {
    reln: Relation,
    steps: Vec<(Expr, Option<Relation>, Block)>,
    last: Expr,
}

impl Parse for CalcInput {
    fn parse(input: ParseStream) -> syn_verus::Result<Self> {
        let reln: Relation = input.parse()?;
        let mut steps = Vec::new();
        let mut last: Expr = input.parse()?;
        input.parse::<Token![;]>()?;
        while !input.is_empty() {
            let op: Option<Relation> = if input.peek(token::Brace) {
                None
            } else {
                let op: Relation = input.parse()?;
                if !reln.op.compatible(&op.op) {
                    return Err(syn_verus::Error::new(
                        op.span,
                        format!("inconsistent relation `{}` with `{}`", op.op, reln.op),
                    ));
                }
                Some(op)
            };
            if input.is_empty() {
                if op.is_some() {
                    return Err(input.error("unexpected end of input"));
                } else {
                    break;
                }
            } else {
                let block: Block = input.parse()?;
                steps.push((last, op, block));
                last = input.parse()?;
                input.parse::<Token![;]>()?;
            }
        }
        if steps.is_empty() {
            return Err(syn_verus::Error::new(last.span(), "single-step calculation"));
        }
        Ok(Self { reln, steps, last })
    }
}

#[derive(Debug)]
struct Relation {
    op: RelationOp,
    span: Span,
}

impl Parse for Relation {
    fn parse(input: ParseStream) -> syn_verus::Result<Self> {
        let span = input.span();
        let op = input.parse()?;
        Ok(Self { op, span })
    }
}

#[derive(Debug)]
enum RelationOp {
    Eq,
    Lt,
    Leq,
    Gt,
    Geq,
    Implies,
    Iff,
}

impl Parse for RelationOp {
    fn parse(input: ParseStream) -> syn_verus::Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(token::Paren) {
            let content;
            parenthesized!(content in input);
            let reln = content.parse()?;
            Ok(reln)
        } else if lookahead.peek(Token![==>]) {
            input.parse::<Token![==>]>()?;
            Ok(Self::Implies)
        } else if lookahead.peek(Token![==]) {
            input.parse::<Token![==]>()?;
            Ok(Self::Eq)
        } else if lookahead.peek(Token![<==>]) {
            input.parse::<Token![<==>]>()?;
            Ok(Self::Iff)
        } else if lookahead.peek(Token![<=]) {
            input.parse::<Token![<=]>()?;
            Ok(Self::Leq)
        } else if lookahead.peek(Token![<]) {
            input.parse::<Token![<]>()?;
            Ok(Self::Lt)
        } else if lookahead.peek(Token![>=]) {
            input.parse::<Token![>=]>()?;
            Ok(Self::Geq)
        } else if lookahead.peek(Token![>]) {
            input.parse::<Token![>]>()?;
            Ok(Self::Gt)
        } else {
            Err(lookahead.error())
        }
    }
}

impl RelationOp {
    /// Confirm that a `middle` relation is consistent with the main relation (self)
    fn compatible(&self, middle: &Self) -> bool {
        use RelationOp::*;
        match (self, middle) {
            // Equality is only consistent with itself
            (Eq, Eq) => true,
            // Less-than-or-equal can be proven via any combination of <, ==, and <=
            (Leq, Lt | Eq | Leq) => true,
            // Strictly-less-than is allowed to use <= and == as intermediates, as long as at least one < shows up at some point
            (Lt, Lt | Eq | Leq) => true,
            // Greater-than-or-equal, similar to less-than-or-equal
            (Geq, Gt | Eq | Geq) => true,
            // Strictly-greater-than, similar to strictly-less-than
            (Gt, Gt | Eq | Geq) => true,
            // Implication is consistent with itself, equality, and if-and-only-if
            (Implies, Implies | Eq | Iff) => true,
            // If-and-only-if is consistent with itself, and equality
            (Iff, Iff | Eq) => true,
            // Fallthrough
            _ => false,
        }
    }

    /// Translate to a Rust boolean expression
    fn to_expr(&self, left: &Expr, right: &Expr) -> TokenStream {
        use RelationOp::*;
        let left = rewrite_expr_to_token_stream(left);
        let right = rewrite_expr_to_token_stream(right);

        match self {
            Eq => quote_builtin! { builtin => #builtin::equal(#left, #right) },
            Lt => quote! { #left < #right },
            Leq => quote! { #left <= #right },
            Gt => quote! { #left > #right },
            Geq => quote! { #left >= #right },
            Implies => quote_builtin! { builtin => #builtin::imply(#left, #right) },
            Iff => {
                quote_builtin! { builtin => #builtin::imply(#left, #right) && #builtin::imply(#right, #left) }
            }
        }
    }
}

impl ToTokens for RelationOp {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        use RelationOp::*;
        match self {
            Eq => tokens.extend(quote! { == }),
            Lt => tokens.extend(quote! { < }),
            Leq => tokens.extend(quote! { <= }),
            Gt => tokens.extend(quote! { > }),
            Geq => tokens.extend(quote! { >= }),
            Implies => tokens.extend(quote! { ==> }),
            Iff => tokens.extend(quote! { <==> }),
        }
    }
}

impl std::fmt::Display for RelationOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use RelationOp::*;
        match self {
            Eq => write!(f, "=="),
            Lt => write!(f, "<"),
            Leq => write!(f, "<="),
            Gt => write!(f, ">"),
            Geq => write!(f, ">="),
            Implies => write!(f, "==>"),
            Iff => write!(f, "<==>"),
        }
    }
}

impl ToTokens for Relation {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.op.to_tokens(tokens);
    }
}
