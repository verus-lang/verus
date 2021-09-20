use crate::ast_util::str_ident;
use air::ast::{Ident, Span};
use std::fmt::Debug;
use std::sync::Arc;

/*
In SMT-LIB format (used by Z3), symbols are built of letters, digits, and:
  ~ ! @ $ % ^ & * _ - + = < > . ? /
(although some words, like "pop" and "declare-fun", are reserved words.)
Symbols starting with . or @ are supposed to be reserved for the solver internals.
Z3 seems to like to introduce symbols with !
$ and % and & and ? are probably safe for prefixes and suffixes.
. and @ are safe for suffixes.
AIR uses @ as a suffix for versions of mutable variables (x@0, x@1, ...).

For VIR -> AIR, we use these suffixes:
- globals
    - x.
    - x.y.z
- locals inside functions
    - x@ (works well with AIR's mutable variable convention)
- shadowed locals inside functions
    - x$0, x$1, ...
- bindings inside expressions (e.g. let, forall)
    - x$
Other generated names:
- fuel_x for global name x
*/

// List of constant strings that can appear in generated AIR code
pub const SUFFIX_GLOBAL: &str = ".";
pub const SUFFIX_LOCAL: &str = "@";
pub const SUFFIX_TYPE_PARAM: &str = "&";
pub const SUFFIX_RENAME: &str = "!$";
pub const TYPE_PATH_SEPARATOR: &str = ".";
pub const VARIANT_SEPARATOR: &str = "/";
pub const PREFIX_FUEL_ID: &str = "fuel%";
pub const PREFIX_FUEL_NAT: &str = "fuel_nat%";
pub const PREFIX_REQUIRES: &str = "req%";
pub const PREFIX_ENSURES: &str = "ens%";
pub const PREFIX_RECURSIVE: &str = "rec%";
pub const PREFIX_TEMP_VAR: &str = "tmp%";
pub const FUEL_ID: &str = "FuelId";
pub const FUEL_TYPE: &str = "Fuel";
pub const ZERO: &str = "zero";
pub const SUCC: &str = "succ";
pub const FUEL_PARAM: &str = "fuel%";
pub const FUEL_LOCAL: &str = "fuel%@";
pub const FUEL_BOOL: &str = "fuel_bool";
pub const FUEL_BOOL_DEFAULT: &str = "fuel_bool_default";
pub const FUEL_DEFAULTS: &str = "fuel_defaults";
pub const RETURN_VALUE: &str = "%return";
pub const U_HI: &str = "uHi";
pub const I_LO: &str = "iLo";
pub const I_HI: &str = "iHi";
pub const U_CLIP: &str = "uClip";
pub const I_CLIP: &str = "iClip";
pub const NAT_CLIP: &str = "nClip";
pub const U_INV: &str = "uInv";
pub const I_INV: &str = "iInv";
pub const ARCH_SIZE: &str = "SZ";
pub const DECREASE_AT_ENTRY: &str = "decrease%init";
pub const SNAPSHOT_CALL: &str = "CALL";
pub const UNIT: &str = "Unit";
pub const POLY: &str = "Poly";
pub const BOX_UNIT: &str = "U";
pub const BOX_INT: &str = "I";
pub const BOX_BOOL: &str = "B";
pub const UNBOX_UNIT: &str = "%U";
pub const UNBOX_INT: &str = "%I";
pub const UNBOX_BOOL: &str = "%B";
pub const PREFIX_BOX: &str = "Poly%";
pub const PREFIX_UNBOX: &str = "%Poly%";
pub const TYPE: &str = "Type";
pub const TYPE_ID_UNIT: &str = "UNIT";
pub const TYPE_ID_BOOL: &str = "BOOL";
pub const TYPE_ID_INT: &str = "INT";
pub const TYPE_ID_NAT: &str = "NAT";
pub const TYPE_ID_UINT: &str = "UINT";
pub const TYPE_ID_SINT: &str = "SINT";
pub const PREFIX_TYPE_ID: &str = "TYPE%";
pub const HAS_TYPE: &str = "has_type";
pub const VARIANT_FIELD_SEPARATOR: &str = "/";

pub fn check_decrease_int() -> crate::ast::Path {
    Arc::new(vec![str_ident("check_decrease_int")])
}

pub fn suffix_global_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_GLOBAL)
}

pub fn suffix_local_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_LOCAL)
}

pub fn rm_suffix_local_id(ident: &Ident) -> Ident {
    let mut name = ident.to_string();
    if name.ends_with(SUFFIX_LOCAL) {
        name = name[..name.len() - SUFFIX_LOCAL.len()].to_string();
    }
    Arc::new(name)
}

pub fn suffix_typ_param_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_TYPE_PARAM)
}

pub fn suffix_rename(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_RENAME)
}

pub fn prefix_type_id(ident: &Ident) -> Ident {
    Arc::new(PREFIX_TYPE_ID.to_string() + ident)
}

pub fn prefix_box(ident: &Ident) -> Ident {
    Arc::new(PREFIX_BOX.to_string() + ident)
}

pub fn prefix_unbox(ident: &Ident) -> Ident {
    Arc::new(PREFIX_UNBOX.to_string() + ident)
}

pub fn prefix_fuel_id(ident: &Ident) -> Ident {
    Arc::new(PREFIX_FUEL_ID.to_string() + ident)
}

pub fn prefix_fuel_nat(ident: &Ident) -> Ident {
    Arc::new(PREFIX_FUEL_NAT.to_string() + ident)
}

pub fn prefix_requires(ident: &Ident) -> Ident {
    Arc::new(PREFIX_REQUIRES.to_string() + ident)
}

pub fn prefix_ensures(ident: &Ident) -> Ident {
    Arc::new(PREFIX_ENSURES.to_string() + ident)
}

pub fn prefix_recursive(ident: &Ident) -> Ident {
    Arc::new(PREFIX_RECURSIVE.to_string() + ident)
}

pub fn prefix_temp_var(n: u64) -> Ident {
    Arc::new(PREFIX_TEMP_VAR.to_string() + &n.to_string())
}

pub fn variant_ident(adt_name: &str, variant_name: &str) -> Ident {
    Arc::new(format!("{}{}{}", adt_name, VARIANT_SEPARATOR, variant_name))
}

pub fn variant_field_ident(variant_ident: &Ident, name: &str) -> Ident {
    Arc::new(format!("{}{}{}", variant_ident.as_str(), VARIANT_FIELD_SEPARATOR, name))
}

#[inline(always)]
pub fn variant_positional_field_ident(variant_ident: &Ident, idx: usize) -> Ident {
    variant_field_ident(variant_ident, format!("{}", idx).as_str())
}

/// For a given snapshot, does it represent the state
/// at the start of the corresponding span, the end, or the full span?
#[derive(Debug)]
pub enum SnapPos {
    Start(Ident),
    Full(Ident),
    End(Ident),
}

pub struct Spanned<X> {
    pub span: Span,
    pub x: X,
}

impl<X> Spanned<X> {
    pub fn new(span: Span, x: X) -> Arc<Spanned<X>> {
        Arc::new(Spanned { span: span, x: x })
    }
}

impl<X: Debug> Debug for Spanned<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_tuple("Spanned").field(&self.span.as_string).field(&self.x).finish()
    }
}
