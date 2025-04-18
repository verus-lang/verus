//! Type-level equality of Rust types.
//!
//! This module provides a `TypeEq` trait, that can be used in `where` clauses like `where A:
//! TypeEq<B>` which means that `A` and `B` are guaranteed to be the same Rust type.
use super::prelude::*;

verus! {

pub use sealed::TypeEq;

/// This (private) module provides a (sealed) trait `TypeEq`, that cannot be `impl`d by any other
/// crate, or even anywhere else in this crate. This guarantees that the only implementation of
/// `TypeEq` is by actual reflexivity.
mod sealed {
    // A private submodule, to allow restriction even within this crate.
    mod private {
        // A publicly-named never-re-exported trait, allowing for actual sealing.
        pub trait Sealed<B> {

        }

        // Implemented for all types, but only pointing each type to itself. Notably, no other
        // implementation exists in this module, or its super-module (which doesn't publicly
        // re-export the `Sealed` trait), and thus none can exist anywhere else.
        impl<T> Sealed<T> for T {

        }

    }

    /// Rust-type-level proof that `Self` and `B` are equal types.
    pub trait TypeEq<B>: Sized + private::Sealed<B> {
        /// A necessary trivial conversion from `Self` to `B`, to keep Rust's type system happy.
        spec fn reflexivity(self) -> B;
    }

    /// There is exactly one instance of it, via reflexivity.
    impl<T> TypeEq<Self> for T {
        #[verifier::inline]
        open spec fn reflexivity(self) -> Self {
            self
        }
    }

}

/// Heterogeneous equality that states that `a` and `b` are not only equal in type, but also equal
/// in value.
///
/// Note: this is slightly less powerful than "true" heterogeneous equality, in that it cannot even
/// be invoked if `a` and `b` cannot be proven (at compile time) to be the same type. At this
/// moment, it is unclear if one can even encode "true" heterogeneous equality in Rust, thus this is
/// the most general version we have. If a more general one is discovered, this function's
/// requirements could be relaxed.
///
/// Note: this equality is also known as "John Major equality", as effectly an inside joke about
/// British politics. Term is coined by Conor McBride, Dependently Typed Functional Programs and
/// their Proofs, PhD thesis (1999).
#[verifier::inline]
pub open spec fn heterogeneous_eq<A, B>(a: A, b: B) -> bool where A: TypeEq<B> {
    a.reflexivity() == b
}

} // verus!
