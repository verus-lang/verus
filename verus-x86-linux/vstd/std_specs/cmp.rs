use super::super::prelude::*;

use verus as verus_;

use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};

verus_! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PartialEqSpec via PartialEqSpecImpl)]
pub trait ExPartialEq<Rhs: ?Sized = Self> {
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
pub trait ExEq: PartialEq {
    type ExternalTraitSpecificationFor: Eq;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PartialOrdSpec via PartialOrdSpecImpl)]
pub trait ExPartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
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
pub trait ExOrd: Eq + PartialOrd {
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

pub trait PartialEqIs<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    spec fn is_eq(&self, other: &Rhs) -> bool;

    spec fn is_ne(&self, other: &Rhs) -> bool;
}

pub trait PartialOrdIs<Rhs: ?Sized = Self>: PartialOrd<Rhs> {
    spec fn is_lt(&self, other: &Rhs) -> bool;

    spec fn is_le(&self, other: &Rhs) -> bool;

    spec fn is_gt(&self, other: &Rhs) -> bool;

    spec fn is_ge(&self, other: &Rhs) -> bool;
}

impl<A: ?Sized + PartialEq<Rhs>, Rhs: ?Sized> PartialEqIs<Rhs> for A {
    #[verifier::inline]
    open spec fn is_eq(&self, other: &Rhs) -> bool {
        self.eq_spec(other)
    }

    #[verifier::inline]
    open spec fn is_ne(&self, other: &Rhs) -> bool {
        !self.eq_spec(other)
    }
}

impl<A: ?Sized + PartialOrd<Rhs>, Rhs: ?Sized> PartialOrdIs<Rhs> for A {
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

} // verus!
