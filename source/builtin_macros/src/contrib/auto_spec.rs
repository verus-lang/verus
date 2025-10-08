use verus_syn::visit_mut::VisitMut;
use verus_syn::{Block, Expr, ImplItem, Item, parse_quote_spanned, spanned::Spanned};

struct Visitor;

fn is_verus_proof_stmt(stmt: &verus_syn::Stmt) -> bool {
    // remove proof-related macros (similar to dual_spec macro)
    use verus_syn::{Expr, ExprUnary, UnOp};
    match stmt {
        verus_syn::Stmt::Expr(e, _) => match e {
            Expr::Assume(..) => true,
            Expr::Assert(..) => true,
            Expr::AssertForall(..) => true,
            Expr::Unary(ExprUnary { op: UnOp::Proof(..), .. }) => true,
            _ => false,
        },
        _ => false,
    }
}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        verus_syn::visit_mut::visit_expr_mut(self, expr);
        use verus_syn::{BinOp, Expr, ExprBinary};
        let span = expr.span();
        match expr {
            Expr::Binary(ExprBinary { op, left, right, .. }) => {
                match op {
                    BinOp::Add(_) => {
                        *expr = parse_quote_spanned_builtin!(builtin, span => #builtin::add(#left, #right));
                    }
                    BinOp::Sub(_) => {
                        *expr = parse_quote_spanned_builtin!(builtin, span => #builtin::sub(#left, #right));
                    }
                    BinOp::Mul(_) => {
                        *expr = parse_quote_spanned_builtin!(builtin, span => #builtin::mul(#left, #right));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        block.stmts.retain(|stmt| !is_verus_proof_stmt(stmt));
        verus_syn::visit_mut::visit_block_mut(self, block);
    }
}

fn auto_spec_fn(
    span: proc_macro2::Span,
    attrs: &mut Vec<verus_syn::Attribute>,
    sig: &mut verus_syn::Signature,
    mut block: Block,
) {
    attrs.push(parse_quote_spanned!(span => #[verifier::allow_in_spec]));
    Visitor.visit_block_mut(&mut block);
    sig.spec.returns = Some(parse_quote_spanned!(span => returns (#block)));
}

pub(crate) fn auto_spec_item(
    item: &mut Item,
    _args: Option<proc_macro2::TokenStream>,
    _new_items: &mut Vec<Item>,
) {
    if let Item::Fn(f) = item {
        let span = f.span();
        auto_spec_fn(span, &mut f.attrs, &mut f.sig, *f.block.clone());
    }
}

pub(crate) fn auto_spec_impl_item(
    item: &mut ImplItem,
    _args: Option<proc_macro2::TokenStream>,
    _new_items: &mut Vec<ImplItem>,
) {
    if let ImplItem::Fn(f) = item {
        let span = f.span();
        auto_spec_fn(span, &mut f.attrs, &mut f.sig, f.block.clone());
    }
}
