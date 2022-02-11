#![allow(unused_imports)]

use crate::parse_transition::parse_impl_item_method;
use crate::transitions::check_transitions;
use proc_macro2::Span;
use crate::ast::{
    Extras, Invariant, Lemma, LemmaPurpose, LemmaPurposeKind, ShardableType, Transition,
    TransitionKind, TransitionStmt, SM,
};
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, FieldsNamed, FnArg, Ident, ImplItemMethod, Meta,
    MetaList, NestedMeta, Receiver, Type,
};

pub struct IdentVisitor {
    pub error: syn::parse::Result<()>,
}

impl IdentVisitor {
    pub fn new() -> IdentVisitor {
        IdentVisitor { error: Ok(()) }
    }
}

impl<'ast> Visit<'ast> for IdentVisitor {
    fn visit_ident(&mut self, node: &'ast Ident) {
        if self.error.is_err() {
            return;
        }

        if node.to_string() == "post" {
            self.error = Err(Error::new(
                node.span(),
                format!("'post' is a reserved identifier in state machine definitions"),
            ));
        }
    }
}
