#![allow(unused_imports)]
use super::super::prelude::*;

use core::option::Option;

verus! {

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

    #[allow(deprecated)]
    proof fn tracked_unwrap(tracked self) -> (tracked t: T)
        requires
            self.is_Some(),
        ensures
            t == self->0,
    ;

    #[allow(deprecated)]
    proof fn tracked_expect(tracked self, msg: &str) -> (tracked t: T)
        requires
            self.is_Some(),
        ensures
            t == self->0,
    ;

    #[allow(deprecated)]
    proof fn tracked_borrow(tracked &self) -> (tracked t: &T)
        requires
            self.is_Some(),
        ensures
            t == self->0,
    ;

    #[allow(deprecated)]
    proof fn tracked_take(tracked &mut self) -> (tracked t: T)
        requires
            old(self).is_Some(),
        ensures
            t == old(self)->0,
            self.is_None(),
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
        t == *old(option),
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

// cloned
pub assume_specification<'a, T: Clone>[ Option::<&'a T>::cloned ](opt: Option<&'a T>) -> (res:
    Option<T>)
    ensures
        opt.is_none() ==> res.is_none(),
        opt.is_some() ==> res.is_some() && cloned::<T>(*opt.unwrap(), res.unwrap()),
;

// and_then
pub assume_specification<T, U, F: FnOnce(T) -> Option<U>>[ Option::<T>::and_then ](
    option: Option<T>,
    f: F,
) -> (res: Option<U>)
    requires
        option.is_some() ==> f.requires((option.unwrap(),)),
    ensures
        option.is_none() ==> res.is_none(),
        option.is_some() ==> f.ensures((option.unwrap(),), res),
;

// ok_or_else
pub assume_specification<T, E, F: FnOnce() -> E>[ Option::<T>::ok_or_else ](
    option: Option<T>,
    err: F,
) -> (res: Result<T, E>)
    requires
        option.is_none() ==> err.requires(()),
    ensures
        option.is_some() ==> res == Ok::<T, E>(option.unwrap()),
        option.is_none() ==> {
            &&& res.is_err()
            &&& err.ensures((), res->Err_0)
        },
;

// unwrap_or_default
pub assume_specification<T: core::default::Default>[ Option::<T>::unwrap_or_default ](
    option: Option<T>,
) -> (res: T)
    ensures
        option.is_some() ==> res == option.unwrap(),
        option.is_none() ==> T::default.ensures((), res),
;

// unwrap_or_else
pub assume_specification<T, F: FnOnce() -> T>[ Option::<T>::unwrap_or_else ](
    option: Option<T>,
    f: F,
) -> (res: T)
    requires
        option.is_none() ==> f.requires(()),
    ensures
        option.is_some() ==> res == option.unwrap(),
        option.is_none() ==> f.ensures((), res),
;

// clone
pub assume_specification<T: Clone>[ <Option<T> as Clone>::clone ](opt: &Option<T>) -> (res: Option<
    T,
>)
    ensures
        opt.is_none() ==> res.is_none(),
        opt.is_some() ==> res.is_some() && cloned::<T>(opt.unwrap(), res.unwrap()),
;

impl<T: super::cmp::PartialEqSpec> super::cmp::PartialEqSpecImpl for Option<T> {
    open spec fn obeys_eq_spec() -> bool {
        T::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &Option<T>) -> bool {
        match (self, other) {
            (None, None) => true,
            (Some(x), Some(y)) => x.eq_spec(y),
            _ => false,
        }
    }
}

pub assume_specification<T: PartialEq>[ <Option<T> as PartialEq>::eq ](
    x: &Option<T>,
    y: &Option<T>,
) -> bool
;

impl<T: super::cmp::PartialOrdSpec> super::cmp::PartialOrdSpecImpl for Option<T> {
    open spec fn obeys_partial_cmp_spec() -> bool {
        T::obeys_partial_cmp_spec()
    }

    open spec fn partial_cmp_spec(&self, other: &Option<T>) -> Option<core::cmp::Ordering> {
        match (self, other) {
            (None, None) => Some(core::cmp::Ordering::Equal),
            (None, Some(_)) => Some(core::cmp::Ordering::Less),
            (Some(_), None) => Some(core::cmp::Ordering::Greater),
            (Some(x), Some(y)) => x.partial_cmp_spec(y),
        }
    }
}

pub assume_specification<T: PartialOrd>[ <Option<T> as PartialOrd>::partial_cmp ](
    x: &Option<T>,
    y: &Option<T>,
) -> Option<core::cmp::Ordering>
;

impl<T: super::cmp::OrdSpec> super::cmp::OrdSpecImpl for Option<T> {
    open spec fn obeys_cmp_spec() -> bool {
        T::obeys_cmp_spec()
    }

    open spec fn cmp_spec(&self, other: &Option<T>) -> core::cmp::Ordering {
        match (self, other) {
            (None, None) => core::cmp::Ordering::Equal,
            (None, Some(_)) => core::cmp::Ordering::Less,
            (Some(_), None) => core::cmp::Ordering::Greater,
            (Some(x), Some(y)) => x.cmp_spec(y),
        }
    }
}

pub assume_specification<T: Ord>[ <Option<T> as Ord>::cmp ](
    x: &Option<T>,
    y: &Option<T>,
) -> core::cmp::Ordering
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

#[doc(hidden)]
#[verifier::ignore_outside_new_mut_ref_experiment]
pub assume_specification<T>[ Option::as_mut ](option: &mut Option<T>) -> (res: Option<&mut T>)
    ensures
        (match *option {
            None => fin(option).is_none() && res.is_none(),
            Some(r) => fin(option).is_some() && res.is_some() && *res.unwrap() === r && *fin(
                res.unwrap(),
            ) === fin(option).unwrap(),
        }),
;

pub assume_specification<T>[ Option::as_slice ](option: &Option<T>) -> (res: &[T])
    ensures
        res@ == (match *option {
            Some(x) => seq![x],
            None => seq![],
        }),
;

#[doc(hidden)]
#[verifier::ignore_outside_new_mut_ref_experiment]
pub assume_specification<T>[ Option::as_mut_slice ](option: &mut Option<T>) -> (res: &mut [T])
    ensures
        res@ == (match *option {
            Some(x) => seq![x],
            None => seq![],
        }),
        fin(res)@.len() == res@.len(),  // TODO this should be broadcast for all `&mut [T]`
        fin(option)@ == (match *option {
            Some(_) => Some(fin(res)@[0]),
            None => None,
        }),
;

#[doc(hidden)]
#[verifier::ignore_outside_new_mut_ref_experiment]
pub assume_specification<T>[ Option::insert ](option: &mut Option<T>, value: T) -> (res: &mut T)
    ensures
        *res == value,
        *fin(option) == Some(*fin(res)),
;

#[doc(hidden)]
#[verifier::ignore_outside_new_mut_ref_experiment]
pub assume_specification<T>[ Option::get_or_insert ](option: &mut Option<T>, value: T) -> (res:
    &mut T)
    ensures
        *res == (match *option {
            Some(x) => x,
            None => value,
        }),
        *fin(option) == Some(*fin(res)),
;

} // verus!
