#![allow(unused_imports)]
use super::super::prelude::*;

use core::option::Option;
use core::option::Option::None;
use core::option::Option::Some;

verus! {

impl<T> View for Option<T> {
    type V = Option<T>;

    open spec fn view(&self) -> Option<T> {
        *self
    }
}

impl<T: DeepView> DeepView for Option<T> {
    type V = Option<T::V>;

    open spec fn deep_view(&self) -> Option<T::V> {
        match self {
            Some(t) => Some(t.deep_view()),
            None => None,
        }
    }
}

////// Add is_variant-style spec functions
pub trait OptionAdditionalFns<T>: Sized {
    #[deprecated(note = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn is_Some(&self) -> bool;

    #[deprecated(note = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn get_Some_0(&self) -> T;

    #[deprecated(note = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn is_None(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn arrow_Some_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn arrow_0(&self) -> T;

    /// Auxilliary spec function for the spec of `tracked_unwrap`, `tracked_borrow`, and `tracked_take`.
    spec fn tracked_is_some(&self) -> bool;

    proof fn tracked_unwrap(tracked self) -> (tracked t: T)
        requires
            self.tracked_is_some(),
        ensures
            t == self->0,
    ;

    proof fn tracked_expect(tracked self, msg: &str) -> (tracked t: T)
        requires
            self.tracked_is_some(),
        ensures
            t == self->0,
    ;

    proof fn tracked_borrow(tracked &self) -> (tracked t: &T)
        requires
            self.tracked_is_some(),
        ensures
            t == self->0,
    ;

    proof fn tracked_take(tracked &mut self) -> (tracked t: T)
        requires
            old(self).tracked_is_some(),
        ensures
            t == old(self)->0,
            !self.tracked_is_some(),
    ;
}

impl<T> OptionAdditionalFns<T> for Option<T> {
    #[verifier::inline]
    open spec fn is_Some(&self) -> bool {
        is_variant(self, "Some")
    }

    #[verifier::inline]
    open spec fn get_Some_0(&self) -> T {
        get_variant_field(self, "Some", "0")
    }

    #[verifier::inline]
    open spec fn is_None(&self) -> bool {
        is_variant(self, "None")
    }

    #[verifier::inline]
    open spec fn arrow_Some_0(&self) -> T {
        get_variant_field(self, "Some", "0")
    }

    #[verifier::inline]
    open spec fn arrow_0(&self) -> T {
        get_variant_field(self, "Some", "0")
    }

    open spec fn tracked_is_some(&self) -> bool {
        is_variant(self, "Some")
    }

    proof fn tracked_unwrap(tracked self) -> (tracked t: T) {
        match self {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        }
    }

    proof fn tracked_expect(tracked self, msg: &str) -> (tracked t: T) {
        match self {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        }
    }

    proof fn tracked_borrow(tracked &self) -> (tracked t: &T) {
        match self {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        }
    }

    /// Similar to `Option::take`
    proof fn tracked_take(tracked &mut self) -> (tracked t: T) {
        let tracked mut x = None::<T>;
        super::super::modes::tracked_swap(self, &mut x);
        x.tracked_unwrap()
    }
}

////// Specs for std methods
// is_some
#[verifier::inline]
pub open spec fn is_some<T>(option: &Option<T>) -> bool {
    is_variant(option, "Some")
}

#[verifier::when_used_as_spec(is_some)]
pub assume_specification<T>[ Option::<T>::is_some ](option: &Option<T>) -> (b: bool)
    ensures
        b == is_some(option),
;

// is_none
#[verifier::inline]
pub open spec fn is_none<T>(option: &Option<T>) -> bool {
    is_variant(option, "None")
}

#[verifier::when_used_as_spec(is_none)]
pub assume_specification<T>[ Option::<T>::is_none ](option: &Option<T>) -> (b: bool)
    ensures
        b == is_none(option),
;

// as_ref
pub assume_specification<T>[ Option::<T>::as_ref ](option: &Option<T>) -> (a: Option<&T>)
    ensures
        a is Some <==> option is Some,
        a is Some ==> option->0 == a->0,
;

// unwrap
#[verifier::inline]
pub open spec fn spec_unwrap<T>(option: Option<T>) -> T
    recommends
        option is Some,
{
    option->0
}

#[verifier::when_used_as_spec(spec_unwrap)]
pub assume_specification<T>[ Option::<T>::unwrap ](option: Option<T>) -> (t: T)
    requires
        option is Some,
    ensures
        t == spec_unwrap(option),
;

// unwrap_or
#[verifier::inline]
pub open spec fn spec_unwrap_or<T>(option: Option<T>, default: T) -> T {
    match option {
        Some(t) => t,
        None => default,
    }
}

#[verifier::when_used_as_spec(spec_unwrap_or)]
pub assume_specification<T>[ Option::<T>::unwrap_or ](option: Option<T>, default: T) -> (t: T)
    ensures
        t == spec_unwrap_or(option, default),
;

// expect
#[verifier::inline]
pub open spec fn spec_expect<T>(option: Option<T>, msg: &str) -> T
    recommends
        option is Some,
{
    option->0
}

#[verifier::when_used_as_spec(spec_expect)]
pub assume_specification<T>[ Option::<T>::expect ](option: Option<T>, msg: &str) -> (t: T)
    requires
        option is Some,
    ensures
        t == spec_expect(option, msg),
;

// take
pub assume_specification<T>[ Option::<T>::take ](option: &mut Option<T>) -> (t: Option<T>)
    ensures
        t == old(option),
        *option is None,
;

// map
pub assume_specification<T, U, F: FnOnce(T) -> U>[ Option::<T>::map ](a: Option<T>, f: F) -> (ret:
    Option<U>)
    requires
        a.is_some() ==> f.requires((a.unwrap(),)),
    ensures
        ret.is_some() == a.is_some(),
        ret.is_some() ==> f.ensures((a.unwrap(),), ret.unwrap()),
;

// clone
pub assume_specification<T: Clone>[ <Option<T> as Clone>::clone ](opt: &Option<T>) -> (res: Option<
    T,
>)
    ensures
        opt.is_none() ==> res.is_none(),
        opt.is_some() ==> res.is_some() && cloned::<T>(opt.unwrap(), res.unwrap()),
;

// ok_or
#[verifier::inline]
pub open spec fn spec_ok_or<T, E>(option: Option<T>, err: E) -> Result<T, E> {
    match option {
        Some(t) => Ok(t),
        None => Err(err),
    }
}

#[verifier::when_used_as_spec(spec_ok_or)]
pub assume_specification<T, E>[ Option::ok_or ](option: Option<T>, err: E) -> (res: Result<T, E>)
    ensures
        res == spec_ok_or(option, err),
;

} // verus!
