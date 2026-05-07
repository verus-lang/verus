use super::super::prelude::*;

use verus as verus_;

use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use core::marker::PointeeSized;

verus_! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PartialEqSpec via PartialEqSpecImpl)]
pub trait ExPartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    type ExternalTraitSpecificationFor: PartialEq<Rhs>;

    spec fn obeys_eq_spec() -> bool;

    spec fn eq_spec(&self, other: &Rhs) -> bool;

    fn eq(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_eq_spec() ==> r == self.eq_spec(other);

    fn ne(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_eq_spec() ==> r == !self.eq_spec(other),
        default_ensures
            call_ensures(Self::eq, (self, other), !r);
}

#[verifier::external_trait_specification]
pub trait ExEq: PartialEq + PointeeSized {
    type ExternalTraitSpecificationFor: Eq;
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExAssertParamIsEq<T: Eq + PointeeSized>(core::cmp::AssertParamIsEq<T>);

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PartialOrdSpec via PartialOrdSpecImpl)]
pub trait ExPartialOrd<Rhs: PointeeSized = Self>: PartialEq<Rhs> + PointeeSized {
    type ExternalTraitSpecificationFor: PartialOrd<Rhs>;

    spec fn obeys_partial_cmp_spec() -> bool;

    spec fn partial_cmp_spec(&self, other: &Rhs) -> Option<Ordering>;

    fn partial_cmp(&self, other: &Rhs) -> (r: Option<Ordering>)
        ensures
            Self::obeys_partial_cmp_spec() ==> r == self.partial_cmp_spec(other);

    fn lt(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) == Some(Ordering::Less)),
        default_ensures
            exists|o: Option<Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o == Some(Ordering::Less)
                }
    ;

    fn le(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) matches Some(
                    Ordering::Less
                    | Ordering::Equal,
                )),
        default_ensures
            exists|o: Option<Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o matches Some(
                        Ordering::Less
                        | Ordering::Equal,
                    )
                }
    ;

    fn gt(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) == Some(Ordering::Greater)),
        default_ensures
            exists|o: Option<Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o == Some(Ordering::Greater)
                }
    ;

    fn ge(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) matches Some(
                    Ordering::Greater
                    | Ordering::Equal,
                )),
        default_ensures
            exists|o: Option<Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o matches Some(
                        Ordering::Greater
                        | Ordering::Equal,
                    )
                }
    ;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(OrdSpec via OrdSpecImpl)]
pub trait ExOrd: Eq + PartialOrd + PointeeSized {
    type ExternalTraitSpecificationFor: Ord;

    spec fn obeys_cmp_spec() -> bool;

    spec fn cmp_spec(&self, other: &Self) -> Ordering;

    fn cmp(&self, other: &Self) -> (r: Ordering)
        ensures
            Self::obeys_cmp_spec() ==> r == self.cmp_spec(other);

    fn max(self, other: Self) -> (r: Self)
        ensures
            Self::obeys_cmp_spec() ==> match other.cmp_spec(&self) {
                Ordering::Less => r == self,
                Ordering::Equal => r == other,
                Ordering::Greater => r == other,
            }
        default_ensures
            exists|b: bool|
                {
                    &&& #[trigger] call_ensures(Self::lt, (&other, &self), b)
                    &&& b ==> r == self
                    &&& !b ==> r == other
                }
    ;

    fn min(self, other: Self) -> (r: Self)
        ensures
            Self::obeys_cmp_spec() ==> match other.cmp_spec(&self) {
                Ordering::Less => r == other,
                Ordering::Equal => r == self,
                Ordering::Greater => r == self,
            }
        default_ensures
            exists|b: bool|
                {
                    &&& #[trigger] call_ensures(Self::lt, (&other, &self), b)
                    &&& b ==> r == other
                    &&& !b ==> r == self
                }
    ;

    fn clamp(self, min: Self, max: Self) -> (r: Self)
        requires
            // There's an "assert!(min <= max)" in the provided clamp that must succeed, so:
            Self::obeys_partial_cmp_spec(),
            min.partial_cmp_spec(&max) matches Some(
                Ordering::Less
                | Ordering::Equal,
            ),
        ensures
            Self::obeys_cmp_spec() ==> match (self.cmp_spec(&min), self.cmp_spec(&max)) {
                (Ordering::Less, _) => r == min,
                (_, Ordering::Greater) => r == max,
                _ => r == self,
            }
        default_ensures
            exists|b1: bool|
                {
                    &&& #[trigger] call_ensures(Self::lt, (&self, &min), b1)
                    &&& b1 ==> r == min
                    &&& !b1 ==> exists|b2: bool|
                        {
                            &&& #[trigger] call_ensures(Self::gt, (&self, &max), b2)
                            &&& b2 ==> r == max
                            &&& !b2 ==> r == self
                        }
                }
    ;
}

pub trait PartialEqIs<Rhs: PointeeSized = Self>: PartialEq<Rhs> + PointeeSized {
    spec fn is_eq(&self, other: &Rhs) -> bool;

    spec fn is_ne(&self, other: &Rhs) -> bool;
}

pub trait PartialOrdIs<Rhs: PointeeSized = Self>: PartialOrd<Rhs> + PointeeSized {
    spec fn is_lt(&self, other: &Rhs) -> bool;

    spec fn is_le(&self, other: &Rhs) -> bool;

    spec fn is_gt(&self, other: &Rhs) -> bool;

    spec fn is_ge(&self, other: &Rhs) -> bool;
}

impl<A: PointeeSized + PartialEq<Rhs>, Rhs: PointeeSized> PartialEqIs<Rhs> for A {
    #[verifier::inline]
    open spec fn is_eq(&self, other: &Rhs) -> bool {
        self.eq_spec(other)
    }

    #[verifier::inline]
    open spec fn is_ne(&self, other: &Rhs) -> bool {
        !self.eq_spec(other)
    }
}

impl<A: PointeeSized + PartialOrd<Rhs>, Rhs: PointeeSized> PartialOrdIs<Rhs> for A {
    #[verifier::inline]
    open spec fn is_lt(&self, other: &Rhs) -> bool {
        self.partial_cmp_spec(other) == Some(Ordering::Less)
    }

    #[verifier::inline]
    open spec fn is_le(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp_spec(other), Some(Ordering::Less | Ordering::Equal))
    }

    #[verifier::inline]
    open spec fn is_gt(&self, other: &Rhs) -> bool {
        self.partial_cmp_spec(other) == Some(Ordering::Greater)
    }

    #[verifier::inline]
    open spec fn is_ge(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp_spec(other), Some(Ordering::Greater | Ordering::Equal))
    }
}

/* bool */

impl PartialEqSpecImpl for bool {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &bool) -> bool {
        *self == *other
    }
}

pub assume_specification[ <bool as PartialEq<bool>>::eq ](x: &bool, y: &bool) -> bool;

pub assume_specification[ <bool as PartialEq<bool>>::ne ](x: &bool, y: &bool) -> bool;

/* floating point */

/*
// Note: we do not assume that floating point types have obeys_*_spec() == true
// because Rust floating point operations are not guaranteed to be deterministic.
// (See https://github.com/rust-lang/rfcs/blob/master/text/3514-float-semantics.md )
// Instead, we ensure an uninterpreted function about the result,
// which can be used to trigger user-supplied axioms.
*/

pub uninterp spec fn eq_ensures<A>(x: A, y: A, o: bool) -> bool;

pub uninterp spec fn ne_ensures<A>(x: A, y: A, o: bool) -> bool;

pub uninterp spec fn partial_cmp_ensures<A>(x: A, y: A, o: Option<Ordering>) -> bool;

pub uninterp spec fn lt_ensures<A>(x: A, y: A, o: bool) -> bool;

pub uninterp spec fn le_ensures<A>(x: A, y: A, o: bool) -> bool;

pub uninterp spec fn gt_ensures<A>(x: A, y: A, o: bool) -> bool;

pub uninterp spec fn ge_ensures<A>(x: A, y: A, o: bool) -> bool;

// Warning: floating-point eq is not the same as spec ==
pub assume_specification[ <f32 as PartialEq<f32>>::eq ](x: &f32, y: &f32) -> (o: bool)
    ensures
        eq_ensures::<f32>(*x, *y, o),
;

// Warning: floating-point ne is not the same as spec !=
pub assume_specification[ <f32 as PartialEq<f32>>::ne ](x: &f32, y: &f32) -> (o: bool)
    ensures
        ne_ensures::<f32>(*x, *y, o),
;

pub assume_specification[ <f32 as PartialOrd<f32>>::partial_cmp ](x: &f32, y: &f32) -> (o: Option<Ordering>)
    ensures
        partial_cmp_ensures::<f32>(*x, *y, o),
;

pub assume_specification[ <f32 as PartialOrd<f32>>::lt ](x: &f32, y: &f32) -> (o: bool)
    ensures
        lt_ensures::<f32>(*x, *y, o),
;

pub assume_specification[ <f32 as PartialOrd<f32>>::le ](x: &f32, y: &f32) -> (o: bool)
    ensures
        le_ensures::<f32>(*x, *y, o),
;

pub assume_specification[ <f32 as PartialOrd<f32>>::gt ](x: &f32, y: &f32) -> (o: bool)
    ensures
        gt_ensures::<f32>(*x, *y, o),
;

pub assume_specification[ <f32 as PartialOrd<f32>>::ge ](x: &f32, y: &f32) -> (o: bool)
    ensures
        ge_ensures::<f32>(*x, *y, o),
;

// Warning: floating-point eq is not the same as spec ==
pub assume_specification[ <f64 as PartialEq<f64>>::eq ](x: &f64, y: &f64) -> (o: bool)
    ensures
        eq_ensures::<f64>(*x, *y, o),
;

// Warning: floating-point ne is not the same as spec !=
pub assume_specification[ <f64 as PartialEq<f64>>::ne ](x: &f64, y: &f64) -> (o: bool)
    ensures
        ne_ensures::<f64>(*x, *y, o),
;

pub assume_specification[ <f64 as PartialOrd<f64>>::partial_cmp ](x: &f64, y: &f64) -> (o: Option<Ordering>)
    ensures
        partial_cmp_ensures::<f64>(*x, *y, o),
;

pub assume_specification[ <f64 as PartialOrd<f64>>::lt ](x: &f64, y: &f64) -> (o: bool)
    ensures
        lt_ensures::<f64>(*x, *y, o),
;

pub assume_specification[ <f64 as PartialOrd<f64>>::le ](x: &f64, y: &f64) -> (o: bool)
    ensures
        le_ensures::<f64>(*x, *y, o),
;

pub assume_specification[ <f64 as PartialOrd<f64>>::gt ](x: &f64, y: &f64) -> (o: bool)
    ensures
        gt_ensures::<f64>(*x, *y, o),
;

pub assume_specification[ <f64 as PartialOrd<f64>>::ge ](x: &f64, y: &f64) -> (o: bool)
    ensures
        ge_ensures::<f64>(*x, *y, o),
;

/* reference types & */

impl<A: PointeeSized, B: PointeeSized> PartialEqSpecImpl<&B> for &A
where
    A: PartialEq<B>,
{
    open spec fn obeys_eq_spec() -> bool {
        <A as PartialEqSpec<B>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &&B) -> bool {
        <A as PartialEqSpec<B>>::eq_spec(*self, *other)
    }
}

pub assume_specification<'_0, 'a, A: PointeeSized, B: PointeeSized>[ <&'a A as PartialEq<&B>>::eq ](
    a: &&'a A,
    b: &&B,
) -> bool
where
    A: PartialEq<B>,
;

pub assume_specification<'_0, 'a, A: PointeeSized, B: PointeeSized>[ <&'a A as PartialEq<&B>>::ne ](
    a: &&'a A,
    b: &&B,
) -> bool
where
    A: PartialEq<B>,
;

impl<A: PointeeSized, B: PointeeSized> PartialOrdSpecImpl<&B> for &A
where
    A: PartialOrd<B>,
{
    open spec fn obeys_partial_cmp_spec() -> bool {
        <A as PartialOrdSpec<B>>::obeys_partial_cmp_spec()
    }

    open spec fn partial_cmp_spec(&self, other: &&B) -> Option<core::cmp::Ordering> {
        <A as PartialOrdSpec<B>>::partial_cmp_spec(*self, *other)
    }
}

pub assume_specification<'_0, 'a, A: PointeeSized, B: PointeeSized>[ <&'a A as PartialOrd<&B>>::partial_cmp ](
    a: &&'a A,
    b: &&B,
) -> Option<core::cmp::Ordering>
where
    A: PartialOrd<B>,
;

pub assume_specification<'_0, 'a, A: PointeeSized, B: PointeeSized>[ <&'a A as PartialOrd<&B>>::lt ](
    a: &&'a A,
    b: &&B,
) -> bool
where
    A: PartialOrd<B>,
;

pub assume_specification<'_0, 'a, A: PointeeSized, B: PointeeSized>[ <&'a A as PartialOrd<&B>>::le ](
    a: &&'a A,
    b: &&B,
) -> bool
where
    A: PartialOrd<B>,
;

pub assume_specification<'_0, 'a, A: PointeeSized, B: PointeeSized>[ <&'a A as PartialOrd<&B>>::gt ](
    a: &&'a A,
    b: &&B,
) -> bool
where
    A: PartialOrd<B>,
;

pub assume_specification<'_0, 'a, A: PointeeSized, B: PointeeSized>[ <&'a A as PartialOrd<&B>>::ge ](
    a: &&'a A,
    b: &&B,
) -> bool
where
    A: PartialOrd<B>,
;

impl<A: PointeeSized + Ord> OrdSpecImpl for &A {
    open spec fn obeys_cmp_spec() -> bool {
        A::obeys_cmp_spec()
    }

    open spec fn cmp_spec(&self, other: &Self) -> core::cmp::Ordering {
        A::cmp_spec(*self, *other)
    }
}

pub assume_specification<'a, A: PointeeSized + Ord>[ <&'a A as Ord>::cmp ](
    a: &&'a A,
    b: &&'a A,
) -> core::cmp::Ordering
;

} // verus!

macro_rules! tuple_cmp_impl {
    ($($idx:tt $T:ident, )+) => {
        verus! {
        impl<$($T: PartialEq + PartialEqSpec),+> PartialEqSpecImpl for ($($T,)+)
        {
            open spec fn obeys_eq_spec() -> bool {
                $(&&& $T::obeys_eq_spec())+
            }

            open spec fn eq_spec(&self, other: &($($T,)+)) -> bool {
                $(&&& $T::eq_spec(&self.$idx, &other.$idx ))+
            }
        }

        impl<$($T: PartialOrd + PartialOrdSpec),+> PartialOrdSpecImpl for ($($T,)+)
        {
            open spec fn obeys_partial_cmp_spec() -> bool {
                $(&&& $T::obeys_partial_cmp_spec())+
            }

            open spec fn partial_cmp_spec(&self, other: &($($T,)+)) -> Option<core::cmp::Ordering> {
                lexical_partial_cmp_spec!($( self.$idx, other.$idx ),+)
            }
        }

        impl<$($T: Ord + OrdSpec),+> OrdSpecImpl for ($($T,)+)
        {
            open spec fn obeys_cmp_spec() -> bool {
                $(&&& $T::obeys_cmp_spec())+
            }

            open spec fn cmp_spec(&self, other: &($($T,)+)) -> core::cmp::Ordering {
                lexical_cmp_spec!($( self.$idx, other.$idx ),+)
            }
        }

        }
    };
}

#[allow(unused)]
macro_rules! lexical_partial_cmp_spec {
    ($a:expr, $b:expr, $($rest_a:expr, $rest_b:expr),+) => {
        match ($a).partial_cmp_spec(&$b) {
            Some(core::cmp::Ordering::Equal) => lexical_partial_cmp_spec!($($rest_a, $rest_b),+),
            ordering => ordering
        }
    };
    ($a:expr, $b:expr) => { ($a).partial_cmp_spec(&$b) };
}

#[allow(unused)]
macro_rules! lexical_cmp_spec {
    ($a:expr, $b:expr, $($rest_a:expr, $rest_b:expr),+) => {
        match ($a).cmp_spec(&$b) {
            core::cmp::Ordering::Equal => lexical_cmp_spec!($($rest_a, $rest_b),+),
            ordering => ordering
        }
    };
    ($a:expr, $b:expr) => { ($a).cmp_spec(&$b) };
}

tuple_cmp_impl!(0 T, );
tuple_cmp_impl!(0 U, 1 T, );
tuple_cmp_impl!(0 V, 1 U, 2 T, );
tuple_cmp_impl!(0 W, 1 V, 2 U, 3 T, );
tuple_cmp_impl!(0 X, 1 W, 2 V, 3 U, 4 T, );
tuple_cmp_impl!(0 Y, 1 X, 2 W, 3 V, 4 U, 5 T, );
tuple_cmp_impl!(0 Z, 1 Y, 2 X, 3 W, 4 V, 5 U, 6 T, );
tuple_cmp_impl!(0 A, 1 Z, 2 Y, 3 X, 4 W, 5 V, 6 U, 7 T, );
tuple_cmp_impl!(0 B, 1 A, 2 Z, 3 Y, 4 X, 5 W, 6 V, 7 U, 8 T, );
tuple_cmp_impl!(0 C, 1 B, 2 A, 3 Z, 4 Y, 5 X, 6 W, 7 V, 8 U, 9 T, );
tuple_cmp_impl!(0 D, 1 C, 2 B, 3 A, 4 Z, 5 Y, 6 X, 7 W, 8 V, 9 U, 10 T, );
tuple_cmp_impl!(0 E, 1 D, 2 C, 3 B, 4 A, 5 Z, 6 Y, 7 X, 8 W, 9 V, 10 U, 11 T, );
