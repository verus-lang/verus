//! Owned token trees for rewriting passes over generated code.
//!
//! Inside a proc macro, every `TokenStream` operation (iterating a stream,
//! collecting tokens into one) goes through the proc-macro bridge to the
//! compiler. A pass that iterates a stream and rebuilds it pays this for
//! every group, so several passes over a large generated stream are
//! expensive. Converting the stream to `Tree`s once, running the passes on
//! them, and converting back once avoids this.

use proc_macro2::{Delimiter, Group, Ident, Span, TokenStream, TokenTree};

#[derive(Clone)]
pub enum Tree {
    /// An identifier, punctuation or literal (never a group).
    Token(TokenTree),
    /// A delimited group, with the span of its delimiters.
    Group(Delimiter, Span, Vec<Tree>),
}

impl Tree {
    pub fn ident(&self) -> Option<&Ident> {
        match self {
            Tree::Token(TokenTree::Ident(id)) => Some(id),
            _ => None,
        }
    }

    pub fn is_punct(&self, c: char) -> bool {
        matches!(self, Tree::Token(TokenTree::Punct(p)) if p.as_char() == c)
    }
}

pub fn to_trees(ts: TokenStream) -> Vec<Tree> {
    ts.into_iter()
        .map(|t| match t {
            TokenTree::Group(g) => Tree::Group(g.delimiter(), g.span(), to_trees(g.stream())),
            t => Tree::Token(t),
        })
        .collect()
}

/// Each group is built anew and given its delimiters' span with `set_span`.
pub fn from_trees(trees: Vec<Tree>) -> TokenStream {
    trees
        .into_iter()
        .map(|t| match t {
            Tree::Group(delimiter, span, inner) => {
                let mut g = Group::new(delimiter, from_trees(inner));
                g.set_span(span);
                TokenTree::Group(g)
            }
            Tree::Token(t) => t,
        })
        .collect()
}
