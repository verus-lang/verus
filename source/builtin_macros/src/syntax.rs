use proc_macro2::TokenStream;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::punctuated::Punctuated;
use syn_verus::token::Paren;
use syn_verus::visit_mut::{visit_expr_mut, visit_item_fn_mut, VisitMut};
use syn_verus::{
    parse_macro_input, parse_quote_spanned, Attribute, BinOp, Expr, ExprBinary, ExprCall,
    FnArgKind, FnMode, Item, ItemFn, ReturnType, UnOp,
};

fn take_expr(expr: &mut Expr) -> Expr {
    let dummy: Expr = syn_verus::parse_quote!(());
    std::mem::replace(expr, dummy)
}

struct Visitor {}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        visit_expr_mut(self, expr);
        if let Expr::Unary(unary) = expr {
            use syn_verus::spanned::Spanned;
            let span = unary.span();
            let low_prec_op = match unary.op {
                UnOp::BigAnd(..) => true,
                UnOp::BigOr(..) => true,
                _ => false,
            };
            let mode_block = match unary.op {
                UnOp::Spec(..) | UnOp::Proof(..) => Some(false),
                UnOp::Tracked(..) => Some(true),
                _ => None,
            };

            if low_prec_op {
                *expr = take_expr(&mut *unary.expr);
            } else if let Some(mode_block) = mode_block {
                match (mode_block, &*unary.expr) {
                    (false, Expr::Paren(..)) => {
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[spec] { #inner });
                    }
                    (false, Expr::Block(..)) => {
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[spec] #inner);
                    }
                    (true, _) => {
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[proof] { #inner });
                    }
                    _ => panic!("internal error: unexpected mode block"),
                }
            }
        } else if let Expr::Binary(binary) = expr {
            use syn_verus::spanned::Spanned;
            let span = binary.span();
            let low_prec_op = match binary.op {
                BinOp::BigAnd(syn_verus::token::BigAnd { spans }) => {
                    let spans = [spans[0], spans[1]];
                    Some(BinOp::And(syn_verus::token::AndAnd { spans }))
                }
                BinOp::BigOr(syn_verus::token::BigOr { spans }) => {
                    let spans = [spans[0], spans[1]];
                    Some(BinOp::Or(syn_verus::token::OrOr { spans }))
                }
                BinOp::Equiv(syn_verus::token::Equiv { spans }) => {
                    let spans = [spans[1], spans[2]];
                    Some(BinOp::Eq(syn_verus::token::EqEq { spans }))
                }
                _ => None,
            };
            let ply = match binary.op {
                BinOp::Imply(_) => Some(true),
                BinOp::Exply(_) => Some(false),
                _ => None,
            };
            let big_eq = match binary.op {
                BinOp::BigEq(_) => Some(true),
                BinOp::BigNe(_) => Some(false),
                _ => None,
            };
            if let Some(op) = low_prec_op {
                let attrs = std::mem::take(&mut binary.attrs);
                let left = Box::new(take_expr(&mut *binary.left));
                let right = Box::new(take_expr(&mut *binary.right));
                let left = parse_quote_spanned!(span => (#left));
                let right = parse_quote_spanned!(span => (#right));
                let bin = ExprBinary { attrs, op, left, right };
                *expr = Expr::Binary(bin);
            } else if let Some(imply) = ply {
                let attrs = std::mem::take(&mut binary.attrs);
                let func = parse_quote_spanned!(span => ::builtin::imply);
                let paren_token = Paren { span };
                let mut args = Punctuated::new();
                if imply {
                    args.push(take_expr(&mut *binary.left));
                    args.push(take_expr(&mut *binary.right));
                } else {
                    args.push(take_expr(&mut *binary.right));
                    args.push(take_expr(&mut *binary.left));
                }
                *expr = Expr::Call(ExprCall { attrs, func, paren_token, args });
            } else if let Some(eq) = big_eq {
                let attrs = std::mem::take(&mut binary.attrs);
                let func = parse_quote_spanned!(span => ::builtin::equal);
                let paren_token = Paren { span };
                let mut args = Punctuated::new();
                args.push(take_expr(&mut *binary.left));
                args.push(take_expr(&mut *binary.right));
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
        fun.attrs.push(parse_quote_spanned!(fun.sig.fn_token.span => #[verifier(verus_macro)]));

        for arg in &mut fun.sig.inputs {
            match (arg.tracked, &mut arg.kind) {
                (None, _) => {}
                (Some(_), FnArgKind::Receiver(..)) => todo!("support tracked self"),
                (Some(token), FnArgKind::Typed(typed)) => {
                    typed.attrs.push(parse_quote_spanned!(token.span => #[proof]));
                }
            }
            arg.tracked = None;
        }
        match &mut fun.sig.output {
            ReturnType::Default => {}
            ReturnType::Type(_, ref mut tracked, _) => {
                if let Some(token) = tracked {
                    fun.attrs.push(parse_quote_spanned!(token.span => #[verifier(returns(proof))]));
                    *tracked = None;
                }
            }
        }

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
        visit_item_fn_mut(self, fun);
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
