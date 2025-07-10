use super::super::prelude::*;

use verus as verus_;

verus_! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PartialEqSpec via PartialEqSpecImpl)]
pub trait ExPartialEq<Rhs: ?Sized = Self> {
    type ExternalTraitSpecificationFor: core::cmp::PartialEq<Rhs>;

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
    type ExternalTraitSpecificationFor: core::cmp::Eq;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PartialOrdSpec via PartialOrdSpecImpl)]
pub trait ExPartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    type ExternalTraitSpecificationFor: core::cmp::PartialOrd<Rhs>;

    spec fn obeys_partial_cmp_spec() -> bool;

    spec fn partial_cmp_spec(&self, other: &Rhs) -> Option<core::cmp::Ordering>;

    fn partial_cmp(&self, other: &Rhs) -> (r: Option<core::cmp::Ordering>)
        ensures
            Self::obeys_partial_cmp_spec() ==> r == self.partial_cmp_spec(other);

    fn lt(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) == Some(core::cmp::Ordering::Less)),
        default_ensures
            exists|o: Option<core::cmp::Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o == Some(core::cmp::Ordering::Less)
                }
    ;

    fn le(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) matches Some(
                    core::cmp::Ordering::Less
                    | core::cmp::Ordering::Equal,
                )),
        default_ensures
            exists|o: Option<core::cmp::Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o matches Some(
                        core::cmp::Ordering::Less
                        | core::cmp::Ordering::Equal,
                    )
                }
    ;

    fn gt(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) == Some(core::cmp::Ordering::Greater)),
        default_ensures
            exists|o: Option<core::cmp::Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o == Some(core::cmp::Ordering::Greater)
                }
    ;

    fn ge(&self, other: &Rhs) -> (r: bool)
        ensures
            Self::obeys_partial_cmp_spec() ==>
                (r <==> self.partial_cmp_spec(other) matches Some(
                    core::cmp::Ordering::Greater
                    | core::cmp::Ordering::Equal,
                )),
        default_ensures
            exists|o: Option<core::cmp::Ordering>|
                {
                    &&& #[trigger] call_ensures(Self::partial_cmp, (self, other), o)
                    &&& r <==> o matches Some(
                        core::cmp::Ordering::Greater
                        | core::cmp::Ordering::Equal,
                    )
                }
    ;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(OrdSpec via OrdSpecImpl)]
pub trait ExOrd: Eq + PartialOrd {
    type ExternalTraitSpecificationFor: Ord;

    spec fn obeys_cmp_spec() -> bool;

    spec fn cmp_spec(&self, other: &Self) -> core::cmp::Ordering;

    fn cmp(&self, other: &Self) -> (r: core::cmp::Ordering)
        ensures
            Self::obeys_cmp_spec() ==> r == self.cmp_spec(other);

    fn max(self, other: Self) -> (r: Self)
        ensures
            Self::obeys_cmp_spec() ==> match other.cmp_spec(&self) {
                core::cmp::Ordering::Less => r == self,
                core::cmp::Ordering::Equal => r == other,
                core::cmp::Ordering::Greater => r == other,
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
                core::cmp::Ordering::Less => r == other,
                core::cmp::Ordering::Equal => r == self,
                core::cmp::Ordering::Greater => r == self,
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
                core::cmp::Ordering::Less
                | core::cmp::Ordering::Equal,
            ),
        ensures
            Self::obeys_cmp_spec() ==> match (self.cmp_spec(&min), self.cmp_spec(&max)) {
                (core::cmp::Ordering::Less, _) => r == min,
                (_, core::cmp::Ordering::Greater) => r == max,
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
