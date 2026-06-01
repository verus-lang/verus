use super::super::prelude::*;
use super::cmp::{
    OrdSpec, OrdSpecImpl, PartialEqSpec, PartialEqSpecImpl, PartialOrdSpec, PartialOrdSpecImpl,
};
use super::convert::FromSpecImpl;
use super::ops::{BitOrSpec, BitOrSpecImpl};
use core::cmp::Ordering;
use core::num::{NonZero, ZeroablePrimitive};
use core::ops::BitOr;

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(ZeroablePrimitiveSpec via ZeroablePrimitiveSpecImpl)]
#[verifier::external_trait_private_bound(core::num::nonzero::private::Sealed)]
pub trait ExZeroablePrimitive: Sized + Copy {
    type ExternalTraitSpecificationFor: ZeroablePrimitive;

    spec fn is_zero(self) -> bool;
}

macro_rules! impl_zeroable_primitive_spec_impl {
    ($($t:ty),*) => {
        $(
            verus! {
                impl ZeroablePrimitiveSpecImpl for $t {
                    open spec fn is_zero(self) -> bool {
                        self == 0
                    }
                }
            }
        )*
    };
}

// The implementators of `ZeroablePrimitive` coincide with `Integer`.
impl_zeroable_primitive_spec_impl!(char, u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExNonZero<T: ZeroablePrimitive>(NonZero<T>);

impl<T: ZeroablePrimitive> View for NonZero<T> {
    type V = T;

    uninterp spec fn view(&self) -> Self::V;
}

// Need this to define `BitOrSpecImpl`
pub uninterp spec fn nonzero_from_primitive<T: ZeroablePrimitive>(n: T) -> NonZero<T>;

pub broadcast axiom fn axiom_nonzero_from_primitive_view_eq<T: ZeroablePrimitive>(n: T)
    requires
        !n.is_zero(),
    ensures
        #[trigger] nonzero_from_primitive(n)@ == n,
;

pub broadcast axiom fn axiom_view_nonzero_from_primitive_eq<T: ZeroablePrimitive>(n: NonZero<T>)
    ensures
        #[trigger] nonzero_from_primitive(n@) == n,
;

pub broadcast axiom fn axiom_nonzero_is_not_zero<T: ZeroablePrimitive>(n: NonZero<T>)
    ensures
        !(#[trigger] n@).is_zero(),
;

pub assume_specification<T: ZeroablePrimitive>[ NonZero::<T>::new ](n: T) -> (ret: Option<
    NonZero<T>,
>)
    ensures
        match ret {
            Some(nz) => nz@ == n && !n.is_zero(),
            None => n.is_zero(),
        },
    opens_invariants none
    no_unwind
;

pub assume_specification<T: ZeroablePrimitive>[ NonZero::<T>::new_unchecked ](n: T) -> (ret:
    NonZero<T>)
    requires
        !n.is_zero(),
    ensures
        ret@ == n,
    opens_invariants none
    no_unwind
;

#[verifier::inline]
pub open spec fn nonzero_spec_get<T: ZeroablePrimitive>(n: NonZero<T>) -> T {
    n@
}

#[verifier::when_used_as_spec(nonzero_spec_get)]
pub assume_specification<T: ZeroablePrimitive>[ NonZero::<T>::get ](n: NonZero<T>) -> T
    returns
        n@,
    opens_invariants none
    no_unwind
;

impl<T: ZeroablePrimitive + PartialEqSpec> PartialEqSpecImpl for NonZero<T> {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.get().eq_spec(&other.get())
    }
}

pub assume_specification<T: ZeroablePrimitive + PartialEq>[ <NonZero<T> as PartialEq>::eq ](
    x: &NonZero<T>,
    y: &NonZero<T>,
) -> bool
;

// Ord is not implemented because of the [`Destruct`](https://doc.rust-lang.org/std/marker/trait.Destruct.html) trait bound.
impl<T: ZeroablePrimitive + PartialOrdSpec> PartialOrdSpecImpl for NonZero<T> {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<Ordering> {
        self.get().partial_cmp_spec(&other.get())
    }
}

pub assume_specification<T: ZeroablePrimitive + PartialOrd>[ <NonZero<
    T,
> as PartialOrd>::partial_cmp ](x: &NonZero<T>, y: &NonZero<T>) -> Option<Ordering>
;

pub assume_specification<T: ZeroablePrimitive + PartialOrd>[ <NonZero<T> as PartialOrd>::lt ](
    x: &NonZero<T>,
    y: &NonZero<T>,
) -> bool
;

pub assume_specification<T: ZeroablePrimitive + PartialOrd>[ <NonZero<T> as PartialOrd>::le ](
    x: &NonZero<T>,
    y: &NonZero<T>,
) -> bool
;

pub assume_specification<T: ZeroablePrimitive + PartialOrd>[ <NonZero<T> as PartialOrd>::gt ](
    x: &NonZero<T>,
    y: &NonZero<T>,
) -> bool
;

pub assume_specification<T: ZeroablePrimitive + PartialOrd>[ <NonZero<T> as PartialOrd>::ge ](
    x: &NonZero<T>,
    y: &NonZero<T>,
) -> bool
;

impl<T: ZeroablePrimitive + BitOrSpec<Output = T>> BitOrSpecImpl<T> for NonZero<T> {
    open spec fn obeys_bitor_spec() -> bool {
        true
    }

    open spec fn bitor_req(self, rhs: T) -> bool {
        self.get().bitor_req(rhs)
    }

    open spec fn bitor_spec(self, rhs: T) -> Self::Output {
        nonzero_from_primitive(self.get().bitor_spec(rhs))
    }
}

pub assume_specification<T: ZeroablePrimitive + BitOr<Output = T>>[ <NonZero<T> as BitOr<
    T,
>>::bitor ](x: NonZero<T>, y: T) -> <NonZero<T> as BitOr<T>>::Output
;

impl<T: ZeroablePrimitive + BitOrSpec<Output = T>> BitOrSpecImpl<NonZero<T>> for NonZero<T> {
    open spec fn obeys_bitor_spec() -> bool {
        true
    }

    open spec fn bitor_req(self, rhs: NonZero<T>) -> bool {
        self.get().bitor_req(rhs.get())
    }

    open spec fn bitor_spec(self, rhs: NonZero<T>) -> Self::Output {
        nonzero_from_primitive(self.get().bitor_spec(rhs.get()))
    }
}

pub assume_specification<T: ZeroablePrimitive + BitOr<Output = T>>[ <NonZero<T> as BitOr<
    NonZero<T>,
>>::bitor ](x: NonZero<T>, y: NonZero<T>) -> <NonZero<T> as BitOr<NonZero<T>>>::Output
;

impl<T: ZeroablePrimitive> FromSpecImpl<NonZero<T>> for T {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(nz: NonZero<T>) -> Self {
        nz.get()
    }
}

pub assume_specification<T: ZeroablePrimitive>[ <T as From<NonZero<T>>>::from ](nz: NonZero<T>) -> T
;

pub assume_specification<T: ZeroablePrimitive>[ <NonZero<T> as Clone>::clone ](
    nz: &NonZero<T>,
) -> NonZero<T>
    returns
        nz,
;

pub broadcast group group_nonzero_axioms {
    axiom_nonzero_from_primitive_view_eq,
    axiom_view_nonzero_from_primitive_eq,
    axiom_nonzero_is_not_zero,
}

} // verus!
