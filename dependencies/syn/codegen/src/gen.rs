use crate::cfg;
use inflections::Inflect;
use proc_macro2::{Ident, Span, TokenStream};
use syn_codegen::{Data, Definitions, Features, Node};

pub const TERMINAL_TYPES: &[&str] = &["Span", "Ident"];

pub fn under_name(name: &str) -> Ident {
    Ident::new(&name.to_snake_case(), Span::call_site())
}

pub fn traverse(
    defs: &Definitions,
    node: fn(&mut TokenStream, &mut TokenStream, &Node, &Definitions),
) -> (TokenStream, TokenStream) {
    let mut types = defs.types.clone();
    for terminal in TERMINAL_TYPES {
        types.push(Node {
            ident: terminal.to_string(),
            features: Features::default(),
            data: Data::Private,
            exhaustive: true,
        });
    }
    types.sort_by(|a, b| a.ident.cmp(&b.ident));

    let mut traits = TokenStream::new();
    let mut impls = TokenStream::new();
    for s in types {
        if s.ident == "Reserved" {
            continue;
        }
        let features = cfg::features(&s.features);
        traits.extend(features.clone());
        impls.extend(features);
        node(&mut traits, &mut impls, &s, defs);
    }

    (traits, impls)
}
