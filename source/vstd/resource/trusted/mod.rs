//! Trusted interfaces for ghost resources.
//!
//! Primitive rules for monoid-based ghost state, including storage protocols.
//! To ensures soundness of these interfaces, the definitions and laws should
//! match [VerusBelt](https://github.com/verus-lang/verus-belt).
//!
//! Users should instead use the types defined in [`vstd::resource`](crate::resource).
pub mod protocol;
pub mod ra;
