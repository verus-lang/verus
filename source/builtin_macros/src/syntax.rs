use proc_macro2::TokenStream;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::punctuated::Punctuated;
use syn_verus::token::Paren;
use syn_verus::visit_mut::{visit_expr_mut, visit_item_fn_mut, VisitMut};
use syn_verus::{
    parse_macro_input, parse_quote_spanned, Attribute, Expr, ExprBinary, ExprCall, FnMode, Item,
    ItemFn,
};

struct Visitor {}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        visit_expr_mut(self, expr);
        if let Expr::Unary(unary) = expr {
            use syn_verus::spanned::Spanned;
            let span = unary.span();
            let low_prec_op = match unary.op {
                syn_verus::UnOp::BigAnd(syn_verus::token::BigAnd { .. }) => true,
                syn_verus::UnOp::BigOr(syn_verus::token::BigOr { .. }) => true,
                _ => false,
            };
            if low_prec_op {
                let dummy: Expr = parse_quote_spanned!(span => ());
                let inner = std::mem::replace(&mut *unary.expr, dummy.clone());
                *expr = inner;
            }
        } else if let Expr::Binary(binary) = expr {
            use syn_verus::spanned::Spanned;
            let span = binary.span();
            let low_prec_op = match binary.op {
                syn_verus::BinOp::BigAnd(syn_verus::token::BigAnd { spans }) => {
                    let spans = [spans[0], spans[1]];
                    Some(syn_verus::BinOp::And(syn_verus::token::AndAnd { spans }))
                }
                syn_verus::BinOp::BigOr(syn_verus::token::BigOr { spans }) => {
                    let spans = [spans[0], spans[1]];
                    Some(syn_verus::BinOp::Or(syn_verus::token::OrOr { spans }))
                }
                syn_verus::BinOp::Equiv(syn_verus::token::Equiv { spans }) => {
                    let spans = [spans[1], spans[2]];
                    Some(syn_verus::BinOp::Eq(syn_verus::token::EqEq { spans }))
                }
                _ => None,
            };
            let ply = match binary.op {
                syn_verus::BinOp::Imply(_) => Some(true),
                syn_verus::BinOp::Exply(_) => Some(false),
                _ => None,
            };
            let big_eq = match binary.op {
                syn_verus::BinOp::BigEq(_) => Some(true),
                syn_verus::BinOp::BigNe(_) => Some(false),
                _ => None,
            };
            if let Some(op) = low_prec_op {
                let attrs = std::mem::take(&mut binary.attrs);
                let dummy: Expr = parse_quote_spanned!(span => ());
                let left = Box::new(std::mem::replace(&mut *binary.left, dummy.clone()));
                let right = Box::new(std::mem::replace(&mut *binary.right, dummy));
                let left = parse_quote_spanned!(span => (#left));
                let right = parse_quote_spanned!(span => (#right));
                let bin = ExprBinary { attrs, op, left, right };
                *expr = Expr::Binary(bin);
            } else if let Some(imply) = ply {
                let attrs = std::mem::take(&mut binary.attrs);
                let func = parse_quote_spanned!(span => ::builtin::imply);
                let paren_token = Paren { span };
                let mut args = Punctuated::new();
                let dummy: Expr = parse_quote_spanned!(span => ());
                if imply {
                    args.push(std::mem::replace(&mut *binary.left, dummy.clone()));
                    args.push(std::mem::replace(&mut *binary.right, dummy));
                } else {
                    args.push(std::mem::replace(&mut *binary.right, dummy.clone()));
                    args.push(std::mem::replace(&mut *binary.left, dummy));
                }
                *expr = Expr::Call(ExprCall { attrs, func, paren_token, args });
            } else if let Some(eq) = big_eq {
                let attrs = std::mem::take(&mut binary.attrs);
                let func = parse_quote_spanned!(span => ::builtin::equal);
                let paren_token = Paren { span };
                let mut args = Punctuated::new();
                let dummy: Expr = parse_quote_spanned!(span => ());
                args.push(std::mem::replace(&mut *binary.left, dummy.clone()));
                args.push(std::mem::replace(&mut *binary.right, dummy));
                let call = Expr::Call(ExprCall { attrs, func, paren_token, args });
                if eq {
                    *expr = call;
                } else {
                    *expr = parse_quote_spanned!(span => ! #call);
                }
            }
        }
    }

    fn visit_item_fn_mut(&mut self, fun: &mut ItemFn) {
        visit_item_fn_mut(self, fun);
        let mode_attrs: Vec<Attribute> = match &fun.sig.mode {
            FnMode::Default => vec![],
            FnMode::Spec(token) => {
                vec![parse_quote_spanned!(token.spec_token.span => #[spec])]
            }
            FnMode::SpecChecked(token) => {
                vec![parse_quote_spanned!(token.spec_token.span => #[spec(checked)])]
            }
            FnMode::Proof(token) => {
                vec![parse_quote_spanned!(token.proof_token.span => #[proof])]
            }
            FnMode::Exec(token) => {
                vec![parse_quote_spanned!(token.exec_token.span => #[exec])]
            }
        };
        fun.attrs.extend(mode_attrs);
        fun.sig.mode = FnMode::Default;
    }
}

struct Items {
    items: Vec<Item>,
}

impl Parse for Items {
    fn parse(input_rev: ParseStream) -> syn_verus::parse::Result<Items> {
        let mut items = Vec::new();
        while !input_rev.is_empty() {
            items.push(input_rev.parse()?);
        }
        Ok(Items { items })
    }
}

pub(crate) fn rewrite_items(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let items: Items = parse_macro_input!(stream as Items);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {};
    for mut item in items.items {
        visitor.visit_item_mut(&mut item);
        item.to_tokens(&mut new_stream);
    }
    proc_macro::TokenStream::from(new_stream)
}
