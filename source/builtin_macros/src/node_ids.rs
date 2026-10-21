//! Node ids for -V check-erasure (rust_verify passes `--cfg verus_check_erasure_ids` to both
//! rustc runs): give each expression written in a `verus!` invocation an identity that is the
//! same in the Keep and Erase expansions. The pass runs on the parsed input, before any rewriting
//! that depends on the erasure mode, and numbers expressions in source order; both expansions
//! parse the same tokens, so they number them the same way. The number is carried to HIR as
//! `#[verus_nid::n(N)]`, which rust_verify/src/erasure_check.rs uses as the node's key.
//!
//! Expressions that keep no id, and are keyed by source location instead:
//! - `if` and `let` expressions, the blocks of `if` branches and of `let ... else`, and
//!   expressions inside patterns, types and generic arguments: rustc rejects attributes there;
//! - parentheses: they are not in HIR, and rustc moves their attributes to the inner expression,
//!   which would then carry two ids;
//! - the callee path of a call: `(#[a] Tracked)(x)` no longer resolves as a constructor call
//!   (the call node records the callee);
//! - closure bodies: Verus puts the closure's requires/ensures header at their start;
//! - ranges and comparisons: Verus rewrites `s[a..b]` and chained comparisons by matching their
//!   syntax;
//! - quantifiers: spec code, and `exists|x| e` accepts no attribute on its closure.

use proc_macro2::Span;
use quote::quote_spanned;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{Attribute, Expr, ExprParen, Item, parse_quote_spanned, token::Paren};

#[cfg(verus_keep_ghost)]
pub(crate) fn enabled() -> bool {
    let ts: proc_macro::TokenStream =
        quote::quote! { ::core::cfg!(verus_check_erasure_ids) }.into();
    match ts.expand_expr() {
        Ok(b) => b.to_string() == "true",
        Err(_) => panic!("cfg verus_check_erasure_ids call failed"),
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn enabled() -> bool {
    false
}

struct Stamper {
    next: u64,
}

fn nid_attr(span: Span, n: u64) -> Attribute {
    let n = proc_macro2::Literal::u64_unsuffixed(n);
    parse_quote_spanned!(span => #[verus_nid::n(#n)])
}

fn stamp(expr: &mut Expr, n: u64) {
    let span = verus_syn::spanned::Spanned::span(expr);
    let mut attrs = expr.replace_attrs(vec![]);
    attrs.push(nid_attr(span, n));
    expr.replace_attrs(attrs);
}

impl VisitMut for Stamper {
    fn visit_pat_mut(&mut self, _: &mut verus_syn::Pat) {}

    fn visit_type_mut(&mut self, _: &mut verus_syn::Type) {}

    fn visit_generic_argument_mut(&mut self, _: &mut verus_syn::GenericArgument) {}

    fn visit_local_init_mut(&mut self, init: &mut verus_syn::LocalInit) {
        self.visit_expr_mut(&mut init.expr);
        if let Some((_, diverge)) = &mut init.diverge {
            // the `else` of a `let ... else` must be a plain block
            if let Expr::Block(b) = &mut **diverge {
                self.next += 1;
                self.visit_block_mut(&mut b.block);
            } else {
                self.visit_expr_mut(diverge);
            }
        }
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let n = self.next;
        self.next += 1;
        if let Expr::Unary(verus_syn::ExprUnary {
            op: verus_syn::UnOp::Forall(_) | verus_syn::UnOp::Exists(_) | verus_syn::UnOp::Choose(_),
            ..
        }) = expr
        {
            // spec code; the parser of `exists|x| e` accepts no attribute on the closure, and
            // Verus reparses the quantifiers of default_ensures
            return;
        }
        if let Expr::Call(c) = expr {
            if let Expr::Path(_) = &*c.func {
                self.next += 1;
                for arg in c.args.iter_mut() {
                    self.visit_expr_mut(arg);
                }
                stamp(expr, n);
                return;
            }
        }
        if let Expr::Closure(c) = expr {
            // the closure's body block must stay a plain block: Verus puts the closure's
            // requires/ensures header at its start
            if let Expr::Block(b) = &mut *c.body {
                self.next += 1;
                self.visit_block_mut(&mut b.block);
            } else {
                self.visit_expr_mut(&mut c.body);
            }
            stamp(expr, n);
            return;
        }
        if let Expr::If(e) = expr {
            // rustc rejects attributes on the branches of an `if`
            self.visit_expr_mut(&mut e.cond);
            self.next += 1;
            self.visit_block_mut(&mut e.then_branch);
            if let Some((_, els)) = &mut e.else_branch {
                if let Expr::Block(b) = &mut **els {
                    self.next += 1;
                    self.visit_block_mut(&mut b.block);
                } else {
                    self.visit_expr_mut(els);
                }
            }
            return;
        }
        verus_syn::visit_mut::visit_expr_mut(self, expr);
        // Verus rewrites chained comparisons (`a <= b < c`) and its own operators by matching
        // nested binary expressions: leave them unstamped
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp::*;
            if !matches!(
                b.op,
                Add(_)
                    | Sub(_)
                    | Mul(_)
                    | Div(_)
                    | Rem(_)
                    | BitXor(_)
                    | BitAnd(_)
                    | BitOr(_)
                    | Shl(_)
                    | Shr(_)
            ) {
                return;
            }
        }
        let span = verus_syn::spanned::Spanned::span(expr);
        match expr {
            // parentheses are not in HIR: rustc moves their attributes to the inner expression,
            // which would then carry two ids
            Expr::Paren(_) => {}
            // rustc rejects attributes on `if` and `let` expressions
            // Verus matches `s[a..b]` (Index of a Range) in spec code: leave ranges unstamped
            Expr::If(_) | Expr::Let(_) | Expr::Verbatim(_) | Expr::Infer(_) | Expr::Range(_) => {}
            // a leading attribute would bind to the left operand: `#[a] (e)` instead
            Expr::Binary(_) | Expr::Cast(_) | Expr::Assign(_) => {
                let inner = std::mem::replace(expr, Expr::Verbatim(quote_spanned!(span => )));
                *expr = Expr::Paren(ExprParen {
                    attrs: vec![nid_attr(span, n)],
                    paren_token: Paren(span),
                    expr: Box::new(inner),
                });
            }
            Expr::Array(_)
            | Expr::Async(_)
            | Expr::Await(_)
            | Expr::Block(_)
            | Expr::Break(_)
            | Expr::Call(_)
            | Expr::Closure(_)
            | Expr::Const(_)
            | Expr::Continue(_)
            | Expr::Field(_)
            | Expr::ForLoop(_)
            | Expr::Index(_)
            | Expr::Lit(_)
            | Expr::Loop(_)
            | Expr::Macro(_)
            | Expr::Match(_)
            | Expr::MethodCall(_)
            | Expr::Path(_)
            | Expr::RawAddr(_)
            | Expr::Reference(_)
            | Expr::Repeat(_)
            | Expr::Return(_)
            | Expr::Struct(_)
            | Expr::Try(_)
            | Expr::TryBlock(_)
            | Expr::Tuple(_)
            | Expr::Unary(_)
            | Expr::Unsafe(_)
            | Expr::While(_)
            | Expr::Yield(_) => {
                let mut attrs = expr.replace_attrs(vec![]);
                attrs.push(nid_attr(span, n));
                expr.replace_attrs(attrs);
            }
            // Verus-specific (spec) expressions: not exec code
            _ => {}
        }
    }
}

pub(crate) fn stamp_items(items: &mut [Item]) {
    let mut s = Stamper { next: 0 };
    for item in items.iter_mut() {
        s.visit_item_mut(item);
    }
}

pub(crate) fn stamp_impl_items(items: &mut [verus_syn::ImplItem]) {
    let mut s = Stamper { next: 0 };
    for item in items.iter_mut() {
        s.visit_impl_item_mut(item);
    }
}
