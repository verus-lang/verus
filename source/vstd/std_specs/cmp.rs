// Provide comparison specifications.
use super::super::prelude::*;

verus! {

use core::cmp::Ordering;

#[verifier::external_type_specification]
pub struct ExOrdering(Ordering);

pub broadcast group group_cmp_axioms {
    axiom_partial_eq,
    axiom_partial_cmp,
    axiom_obey_cmp_model,
}

//
// https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html
// The methods of this trait must be consistent with each other and with those of PartialEq.
// The following conditions must hold:
// a == b if and only if partial_cmp(a, b) == Some(Equal).
// a < b if and only if partial_cmp(a, b) == Some(Less)
// a > b if and only if partial_cmp(a, b) == Some(Greater)
// a <= b if and only if a < b || a == b
// a >= b if and only if a > b || a == b
// a != b if and only if !(a == b).
//
// By implementing SpecPartialOrdOp + SpecPartialEq, it assumes that the type follow the above cmp model.
pub open spec fn obeys_comparison_model<Lhs: ?Sized, Rhs: ?Sized>() -> bool;

pub open spec fn spec_partial_cmp<Lhs: ?Sized, Rhs: ?Sized>(lhs: &Lhs, rhs: &Rhs) -> Option<
    Ordering,
>;

pub open spec fn spec_partial_eq<T1: ?Sized, T2: ?Sized>(v1: &T1, rhs: &T2) -> bool;

#[verifier(inline)]
pub open spec fn spec_lt<Lhs: ?Sized, Rhs: ?Sized>(lhs: &Lhs, rhs: &Rhs) -> bool {
    spec_partial_cmp(lhs, rhs) == Some(Ordering::Less)
}

#[verifier(inline)]
pub open spec fn spec_gt<Lhs: ?Sized, Rhs: ?Sized>(lhs: &Lhs, rhs: &Rhs) -> bool {
    spec_partial_cmp(lhs, rhs) == Some(Ordering::Greater)
}

#[verifier(inline)]
pub open spec fn spec_le<Lhs: ?Sized, Rhs: ?Sized>(lhs: &Lhs, rhs: &Rhs) -> bool {
    spec_lt(lhs, rhs) || spec_partial_eq(lhs, rhs)
}

#[verifier(inline)]
pub open spec fn spec_ge<Lhs: ?Sized, Rhs: ?Sized>(lhs: &Lhs, rhs: &Rhs) -> bool {
    spec_gt(lhs, rhs) || spec_partial_eq(lhs, rhs)
}

// Implement SpecObeyCmpModel for unverified code that obeys the comparison model.
pub broadcast proof fn axiom_obey_cmp_model<
    Lhs: SpecPartialOrdOp<Rhs> + SpecPartialEqOp<Rhs>,
    Rhs,
>()
    ensures
        #[trigger] obeys_comparison_model::<Lhs, Rhs>() == true,
{
    admit()
}

pub trait SpecPartialOrdOp<Rhs> {
    spec fn spec_partial_cmp(&self, rhs: &Rhs) -> Option<Ordering>;
}

pub broadcast proof fn axiom_partial_cmp<Lhs: SpecPartialOrdOp<Rhs>, Rhs>(lhs: &Lhs, rhs: &Rhs)
    ensures
        #[trigger] spec_partial_cmp(lhs, rhs) == lhs.spec_partial_cmp(rhs),
{
    admit()
}

pub trait SpecPartialEqOp<T: ?Sized> {
    spec fn spec_partial_eq(&self, rhs: &T) -> bool;
}

pub broadcast proof fn axiom_partial_eq<T1: ?Sized + SpecPartialEqOp<T2>, T2: ?Sized>(
    v: &T1,
    rhs: &T2,
)
    ensures
        v.spec_partial_eq(rhs) == #[trigger] spec_partial_eq(v, rhs),
{
    admit()
}

#[verifier::external_trait_specification]
pub trait ExPartialEq<Rhs: ?Sized> {
    type ExternalTraitSpecificationFor: core::cmp::PartialEq<Rhs>;

    // Required method
    fn eq(&self, other: &Rhs) -> (ret: bool)
        ensures
            ret == spec_partial_eq(self, other),
    ;
}

#[verifier::external_trait_specification]
pub trait ExPartialOrd<Rhs: ?Sized>: PartialEq<Rhs> {
    type ExternalTraitSpecificationFor: core::cmp::PartialOrd<Rhs>;

    fn partial_cmp(&self, other: &Rhs) -> (ret: Option<Ordering>)
        ensures
            obeys_comparison_model::<Self, Rhs>() ==> ret === spec_partial_cmp(self, other),
    ;

    fn lt(&self, other: &Rhs) -> (ret: bool)
        ensures
            obeys_comparison_model::<Self, Rhs>() ==> ret == spec_lt(self, other),
    ;

    fn le(&self, other: &Rhs) -> (ret: bool)
        ensures
            obeys_comparison_model::<Self, Rhs>() ==> ret == spec_le(self, other),
    ;

    fn gt(&self, other: &Rhs) -> (ret: bool)
        ensures
            obeys_comparison_model::<Self, Rhs>() ==> ret == spec_gt(self, other),
    ;

    fn ge(&self, other: &Rhs) -> (ret: bool)
        ensures
            obeys_comparison_model::<Self, Rhs>() ==> ret == spec_ge(self, other),
    ;
}

} // verus!
macro_rules! spec_cmp {
    ($($ty: ty)*) => {
        verus!{
        $(
            impl SpecPartialOrdOp<$ty> for $ty {
                open spec fn spec_partial_cmp(&self, rhs: &$ty) -> Option<Ordering> {
                    if *self < *rhs {
                        Some(Ordering::Less)
                    } else if *self > *rhs {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            }
        )*
    }
    };
}

spec_cmp! {u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128}

macro_rules! def_partial_eq_for {
    ($($ty: ty)*) => {
        verus!{
            $(
                impl SpecPartialEqOp<$ty> for $ty {
                    open spec fn spec_partial_eq(&self, rhs: &$ty) -> bool {
                        *self == *rhs
                    }
                }
            )*
        }
    };
}
def_partial_eq_for!(
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
);
