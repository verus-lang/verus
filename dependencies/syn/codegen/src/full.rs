use crate::lookup;
use proc_macro2::TokenStream;
use quote::quote;
use syn_codegen::{Data, Definitions, Node, Type};

pub fn get_macro() -> TokenStream {
    quote! {
        #[cfg(feature = "full")]
        macro_rules! full {
            ($e:expr) => {
                $e
            };
        }

        #[cfg(all(feature = "derive", not(feature = "full")))]
        macro_rules! full {
            ($e:expr) => {
                unreachable!()
            };
        }
    }
}

/// Syntax tree enum that has some variants enabled in "derive" mode and the
/// rest enabled in "full" mode.
pub fn is_mixed_derive_full_enum(defs: &Definitions, node: &Node) -> bool {
    if !(node.features.any.contains("derive") && node.features.any.contains("full")) {
        return false;
    }

    let variants = match &node.data {
        Data::Enum(variants) => variants,
        Data::Private | Data::Struct(_) => return false,
    };

    let mut has_derive = false;
    let mut has_full = false;
    for fields in variants.values() {
        match classify_variant(defs, fields) {
            VariantAvailability::Derive => has_derive = true,
            VariantAvailability::Full => has_full = true,
            VariantAvailability::Other => {}
        }
    }
    has_derive && has_full
}

enum VariantAvailability {
    Derive,
    Full,
    Other,
}

fn classify_variant(defs: &Definitions, fields: &[Type]) -> VariantAvailability {
    let mut has_derive = false;
    let mut has_full = false;
    for field in fields {
        for_each_syn_type(field, &mut |ty| {
            let node = lookup::node(defs, ty);
            let derive = node.features.any.contains("derive");
            let full = node.features.any.contains("full");
            match (derive, full) {
                (false, false) => {}
                (false, true) => has_full = true,
                (true, false | true) => has_derive = true,
            }
        });
    }
    if has_full {
        VariantAvailability::Full
    } else if has_derive {
        VariantAvailability::Derive
    } else {
        VariantAvailability::Other
    }
}

fn for_each_syn_type(ty: &Type, f: &mut dyn FnMut(&str)) {
    match ty {
        Type::Syn(ty) => f(ty),
        Type::Std(_) | Type::Ext(_) | Type::Token(_) | Type::Group(_) => {}
        Type::Punctuated(punctuated) => for_each_syn_type(&punctuated.element, f),
        Type::Option(ty) | Type::Box(ty) | Type::Vec(ty) => for_each_syn_type(ty, f),
        Type::Tuple(elements) => {
            for ty in elements {
                for_each_syn_type(ty, f);
            }
        }
    }
}
