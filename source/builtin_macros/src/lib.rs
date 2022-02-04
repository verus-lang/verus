use synstructure::{decl_attribute, decl_derive};
mod is_variant;
mod structural;

decl_derive!([Structural] => structural::derive_structural);

decl_attribute!([is_variant] => is_variant::attribute_is_variant);
