use air::ast::{Ident, Span};
use std::fmt::Debug;
use std::rc::Rc;

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

pub const SUFFIX_GLOBAL: &str = ".";
pub const SUFFIX_LOCAL: &str = "@";
pub const PREFIX_FUEL_ID: &str = "fuel%";
pub const PREFIX_REQUIRES: &str = "req%";
pub const FUEL_ID: &str = "FuelId";
pub const FUEL_BOOL: &str = "fuel_bool";
pub const FUEL_BOOL_DEFAULT: &str = "fuel_bool_default";
pub const FUEL_DEFAULTS: &str = "fuel_defaults";

pub fn suffix_global_id(ident: &Ident) -> Ident {
    Rc::new(ident.to_string() + SUFFIX_GLOBAL)
}

pub fn suffix_local_id(ident: &Ident) -> Ident {
    Rc::new(ident.to_string() + SUFFIX_LOCAL)
}

pub fn prefix_fuel_id(ident: &Ident) -> Ident {
    Rc::new(PREFIX_FUEL_ID.to_string() + ident)
}

pub fn prefix_requires(ident: &Ident) -> Ident {
    Rc::new(PREFIX_REQUIRES.to_string() + ident)
}

pub struct Spanned<X> {
    pub span: Span,
    pub x: X,
}

impl<X> Spanned<X> {
    pub fn new(span: Span, x: X) -> Rc<Spanned<X>> {
        Rc::new(Spanned { span: span, x: x })
    }
}

impl<X: Debug> Debug for Spanned<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_tuple("Spanned").field(&self.span.as_string).field(&self.x).finish()
    }
}
