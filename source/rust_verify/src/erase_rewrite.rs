//! Rename any spans that we use during erasure to be unique,
//! so that there is no ambiguity between two expressions with the same span.

use rustc_ast::ast::{
    AssocItem, AssocItemKind, Expr, ExprKind, FnKind, ForeignItem, ForeignItemKind, Item, ItemKind,
    Param, Pat, Path,
};
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast::ptr::P;
use rustc_span::Span;
use smallvec::SmallVec;
use std::collections::HashSet;

pub(crate) struct Visitor {
    // All spans relevant to erasure, including renamed spans
    pub(crate) spans: HashSet<Span>,
}

fn fresh_span(span: Span) -> Span {
    span.with_ctxt(span.data().ctxt.clone_unique_id())
}

impl Visitor {
    pub(crate) fn new() -> Self {
        Visitor { spans: HashSet::new() }
    }

    fn freshen_span(&mut self, span: &mut Span) {
        *span = fresh_span(*span);
        self.spans.insert(*span);
    }
}

impl MutVisitor for Visitor {
    fn visit_path(&mut self, p: &mut Path) {
        self.freshen_span(&mut p.span);
        rustc_ast::mut_visit::noop_visit_path(p, self);
    }

    fn visit_pat(&mut self, p: &mut P<Pat>) {
        self.freshen_span(&mut p.span);
        rustc_ast::mut_visit::noop_visit_pat(p, self);
    }

    fn visit_expr(&mut self, e: &mut P<Expr>) {
        self.freshen_span(&mut e.span);
        match &mut e.kind {
            ExprKind::MethodCall(_, _, span) => {
                self.freshen_span(span);
            }
            _ => {}
        }
        rustc_ast::mut_visit::noop_visit_expr(e, self);
    }

    fn flat_map_param(&mut self, mut param: Param) -> SmallVec<[Param; 1]> {
        self.freshen_span(&mut param.span);
        rustc_ast::mut_visit::noop_flat_map_param(param, self)
    }

    fn visit_item_kind(&mut self, i: &mut ItemKind) {
        match i {
            ItemKind::Fn(box FnKind(_, sig, _generics, _body)) => {
                self.freshen_span(&mut sig.span);
            }
            _ => {}
        }
        rustc_ast::mut_visit::noop_visit_item_kind(i, self);
    }

    fn flat_map_foreign_item(&mut self, mut ni: P<ForeignItem>) -> SmallVec<[P<ForeignItem>; 1]> {
        use std::ops::DerefMut;
        match &mut ni.deref_mut().kind {
            ForeignItemKind::Fn(box FnKind(_, sig, _generics, _body)) => {
                self.freshen_span(&mut sig.span);
            }
            _ => {}
        }
        rustc_ast::mut_visit::noop_flat_map_foreign_item(ni, self)
    }

    fn flat_map_impl_item(&mut self, mut i: P<AssocItem>) -> SmallVec<[P<AssocItem>; 1]> {
        use std::ops::DerefMut;
        match &mut i.deref_mut().kind {
            AssocItemKind::Fn(box FnKind(_, sig, _generics, _body)) => {
                self.freshen_span(&mut sig.span);
            }
            _ => {}
        }
        rustc_ast::mut_visit::noop_flat_map_assoc_item(i, self)
    }

    fn flat_map_item(&mut self, mut i: P<Item>) -> SmallVec<[P<Item>; 1]> {
        use std::ops::DerefMut;
        self.freshen_span(&mut i.deref_mut().span);
        rustc_ast::mut_visit::noop_flat_map_item(i, self)
    }
}
