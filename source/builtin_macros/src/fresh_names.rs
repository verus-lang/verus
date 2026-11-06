//! Temporary names for generated Rust, where printed tokens lose macro hygiene.
use std::collections::HashSet;

use proc_macro2::{Ident, Span, TokenStream, TokenTree};

#[derive(Default)]
pub(crate) struct FreshNames {
    reserved: HashSet<String>,
}

impl FreshNames {
    pub(crate) fn reserve(&mut self, tokens: TokenStream) {
        for token in tokens {
            match token {
                TokenTree::Ident(id) => {
                    let name = id.to_string();
                    // Raw and ordinary spellings refer to the same Rust name.
                    self.reserved.insert(name.strip_prefix("r#").unwrap_or(&name).to_owned());
                }
                TokenTree::Group(group) => self.reserve(group.stream()),
                _ => {}
            }
        }
    }

    pub(crate) fn numbered(&mut self, base: &str, span: Span) -> Ident {
        let candidates = std::iter::once(base.to_owned())
            .chain((1usize..).map(|suffix| format!("{base}_{suffix}")));
        self.allocate(candidates, span)
    }

    pub(crate) fn underscored(&mut self, base: &str, span: Span) -> Ident {
        // Retain the atomic generator's existing spelling in snapshots.
        let candidates =
            std::iter::successors(Some(base.to_owned()), |name| Some(format!("{name}_")));
        self.allocate(candidates, span)
    }

    fn allocate(&mut self, mut candidates: impl Iterator<Item = String>, span: Span) -> Ident {
        let name = candidates
            .find(|name| self.reserved.insert(name.clone()))
            .expect("temporary-name sequences are infinite");
        Ident::new(&name, span)
    }
}
