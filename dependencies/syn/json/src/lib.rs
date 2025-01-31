//! # Data structures that describe Syn's syntax tree.
//!
//! The Syn syntax tree is made up of more than 200 types. Occasionally it can
//! come up that you need to implement some behavior across them all.
//!
//! - For example [the Rust integration for AST Explorer][astexplorer] wants to
//!   turn a syntax tree from Syn into a JavaScript value understood by the
//!   platform's existing cross-language syntax tree visualization code.
//!
//!   [astexplorer]: https://astexplorer.net/#/gist/388150a52f74d45a355d2b5e865ded96/0c6d563f28d900472f699c21a1845ad20ae9927f
//!
//! - As another example from within Syn itself, the traits and implementations
//!   of the [`visit`], [`visit_mut`], and [`fold`] modules can be generated
//!   programmatically from a description of the syntax tree.
//!
//!   [`visit`]: https://docs.rs/syn/2.0/syn/visit/index.html
//!   [`visit_mut`]: https://docs.rs/syn/2.0/syn/visit_mut/index.html
//!   [`fold`]: https://docs.rs/syn/2.0/syn/fold/index.html
//!
//! To make this type of code as easy as possible to implement in any language,
//! every Syn release comes with a machine-readable description of that version
//! of the syntax tree as a JSON file [syn.json]. This `syn-codegen` crate
//! provides the canonical data structures for parsing and making use of the
//! representation in syn.json from Rust code.
//!
//! [syn.json]: https://raw.githubusercontent.com/dtolnay/syn/master/syn.json
//!
//! ## Example
//!
//! ```
//! use syn_codegen::Definitions;
//!
//! # const IGNORE: &str = stringify! {
//! const SYN: &str = include_str!("syn.json");
//! # };
//! # const SYN: &str = include_str!("../../syn.json");
//!
//! fn main() {
//!     let defs: Definitions = serde_json::from_str(SYN).unwrap();
//!
//!     for node in &defs.types {
//!         println!("syn::{}", node.ident);
//!     }
//! }
//! ```

#![doc(html_root_url = "https://docs.rs/syn-codegen/0.4.2")]

use indexmap::IndexMap;
use semver::Version;
#[cfg(feature = "serde")]
use serde::de::{Deserialize, Deserializer};
#[cfg(feature = "serde")]
use serde_derive::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// Top-level content of the syntax tree description.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Definitions {
    /// The Syn version whose syntax tree is described by this data.
    pub version: Version,

    /// Syntax tree types defined by Syn.
    pub types: Vec<Node>,

    /// Token types defined by Syn (keywords as well as punctuation).
    ///
    /// The keys in the map are the Rust type name for the token. The values in
    /// the map are the printed token representation.
    ///
    /// These tokens are accessible in the Syn public API as `syn::token::#name`
    /// or alternatively `syn::Token![#repr]`.
    pub tokens: BTreeMap<String, String>,
}

/// Syntax tree type defined by Syn.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Node {
    /// Name of the type.
    ///
    /// This type is accessible in the Syn public API as `syn::#name`.
    pub ident: String,

    /// Features behind which this type is cfg gated.
    pub features: Features,

    /// Content of the data structure.
    #[cfg_attr(
        feature = "serde",
        serde(
            flatten,
            skip_serializing_if = "is_private",
            deserialize_with = "private_if_absent"
        )
    )]
    pub data: Data,

    #[cfg_attr(
        feature = "serde",
        serde(skip_serializing_if = "is_true", default = "bool_true")
    )]
    pub exhaustive: bool,
}

/// Content of a syntax tree data structure.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Data {
    /// This is an opaque type with no publicly accessible structure.
    Private,

    /// This type is a braced struct with named fields.
    #[cfg_attr(feature = "serde", serde(rename = "fields"))]
    Struct(Fields),

    /// This type is an enum.
    #[cfg_attr(feature = "serde", serde(rename = "variants"))]
    Enum(Variants),
}

/// Fields of a braced struct syntax tree node with named fields.
///
/// The keys in the map are the field names.
pub type Fields = IndexMap<String, Type>;

/// Variants of an enum syntax tree node.
///
/// The keys in the map are the variant names.
///
/// Variants are unit variants if they hold no data and tuple variants
/// otherwise. The Syn syntax tree does not make use of braced variants.
pub type Variants = IndexMap<String, Vec<Type>>;

/// Type of a struct field or tuple variant field in the syntax tree.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(rename_all = "lowercase")
)]
pub enum Type {
    /// Syntax tree type defined by Syn.
    ///
    /// This name will match the ident of some `Node`.
    Syn(String),

    /// Type defined by the Rust language or standard library.
    ///
    /// All such types used by Syn are accessible in the Rust prelude and can be
    /// used without a qualifying path in most Rust code.
    Std(String),

    /// Type defined by proc-macro2.
    ///
    /// The type is accessible in the proc-macro2 public API as
    /// `proc_macro2::#name`.
    #[cfg_attr(feature = "serde", serde(rename = "proc_macro2"))]
    Ext(String),

    /// Keyword or punctuation token type defined by Syn.
    ///
    /// This name will match one of the keys in the `tokens` map.
    Token(String),

    /// Grouping token defined by Syn.
    ///
    /// The type is accessible in the Syn public API as `syn::token::#name`.
    Group(String),

    /// Punctuated list.
    ///
    /// This refers to `syn::punctuated::Punctuated<T, P>` with the specified
    /// element type and punctuation.
    Punctuated(Punctuated),

    /// `std::option::Option`
    Option(Box<Type>),

    /// `std::boxed::Box`
    Box(Box<Type>),

    /// `std::vec::Vec`
    Vec(Box<Type>),

    /// Rust tuple with two or more fields.
    Tuple(Vec<Type>),
}

/// Type of a punctuated list.
///
/// This refers to `syn::punctuated::Punctuated<#element, #punct>`.
///
/// The punct string will match one of the keys in the `tokens` map.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Punctuated {
    pub element: Box<Type>,
    pub punct: String,
}

/// Features behind which a syntax tree type is cfg gated.
#[derive(Clone, Debug, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Features {
    /// Type is accessible if at least one of these features is enabled against
    /// the Syn dependency.
    pub any: BTreeSet<String>,
}

#[cfg(feature = "serde")]
fn is_private(data: &Data) -> bool {
    match data {
        Data::Private => true,
        Data::Struct(_) | Data::Enum(_) => false,
    }
}

#[cfg(feature = "serde")]
fn private_if_absent<'de, D>(deserializer: D) -> Result<Data, D::Error>
where
    D: Deserializer<'de>,
{
    let option = Option::deserialize(deserializer)?;
    Ok(option.unwrap_or(Data::Private))
}

#[cfg(feature = "serde")]
fn is_true(b: &bool) -> bool {
    *b
}

#[cfg(feature = "serde")]
fn bool_true() -> bool {
    true
}
