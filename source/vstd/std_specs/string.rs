//! PartialEq assume_specification for String ↔ &str (`'_0` binders).
//! Under `verus_!` so verusfmt can parse `'_0` (see `cmp.rs`); SpecImpls stay in `vstd/string.rs`.
use super::super::prelude::*;

use verus as verus_;

#[cfg(feature = "alloc")]
use alloc::string::String;

verus_! {

#[cfg(verus_keep_ghost)]
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification<'_0>[ <String as PartialEq<&str>>::eq ](s: &String, other: &&str) -> bool
;

#[cfg(verus_keep_ghost)]
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification<'_0>[ <&'_0 str as PartialEq<String>>::eq ](
    s: &&'_0 str,
    other: &String,
) -> bool
;

}
