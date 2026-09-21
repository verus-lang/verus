#![allow(unused_imports)]
use super::super::prelude::*;

use core::option::Option;

verus! {

////// Add is_variant-style spec functions
pub trait OptionAdditionalFns<T>: Sized {
    #[cfg_attr(not(verus_verify_core), deprecated = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn is_Some(&self) -> bool;

    #[cfg_attr(not(verus_verify_core), deprecated = "get_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
    #[allow(non_snake_case)]
    spec fn get_Some_0(&self) -> T;

    #[cfg_attr(not(verus_verify_core), deprecated = "is_Variant is deprecated - use `->` or `matches` instead: https://verus-lang.github.io/verus/guide/datatypes_enum.html")]
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
    #[verifier::tracked_take_option_primitive]
    proof fn tracked_take(tracked &mut self) -> (tracked t: T)
        requires
            old(self).is_Some(),
        ensures
            t == old(self)->0,
            final(self).is_None(),
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
    #[verifier::tracked_take_option_primitive]
    axiom fn tracked_take(tracked &mut self) -> (tracked t: T);
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
    no_unwind
;

// is_some_and
pub assume_specification<T, F: FnOnce(T) -> bool>[ Option::<T>::is_some_and ](
    option: Option<T>,
    f: F,
) -> (res: bool)
    requires
        option is Some ==> f.requires((option->0,)),
    ensures
        option is None ==> !res,
        option is Some ==> f.ensures((option->0,), res),
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
    no_unwind
;

// is_none_or
pub assume_specification<T, F: FnOnce(T) -> bool>[ Option::<T>::is_none_or ](
    option: Option<T>,
    f: F,
) -> (res: bool)
    requires
        option is Some ==> f.requires((option->0,)),
    ensures
        option is None ==> res,
        option is Some ==> f.ensures((option->0,), res),
;

// as_ref
pub assume_specification<T>[ Option::<T>::as_ref ](option: &Option<T>) -> (a: Option<&T>)
    ensures
        a is Some <==> option is Some,
        a is Some ==> option->0 == a->0,
    no_unwind
;

// as_deref
pub assume_specification<T: core::ops::Deref>[ Option::<T>::as_deref ](option: &Option<T>) -> (res:
    Option<&T::Target>)
    ensures
        res is Some <==> option is Some,
        option is Some ==> call_ensures(T::deref, (&option->0,), res->0),
;

// as_deref_mut
pub assume_specification<T: core::ops::DerefMut>[ Option::<T>::as_deref_mut ](
    option: &mut Option<T>,
) -> (res: Option<&mut T::Target>)
    ensures
        match *old(option) {
            None => final(option).is_none() && res.is_none(),
            Some(value) => {
                &&& final(option).is_some()
                &&& res.is_some()
                &&& exists|inner: &mut T|
                    {
                        &&& *inner == value
                        &&& *final(inner) == final(option)->0
                        &&& call_ensures(T::deref_mut, (inner,), res->0)
                    }
            },
        },
;

// From<T> for Option<T>
pub assume_specification<T>[ <Option<T> as core::convert::From<T>>::from ](value: T) -> (res:
    Option<T>)
    ensures
        res == Some(value),
;

// From<&Option<T>> for Option<&T>
pub assume_specification<'a, T>[ <Option<&'a T> as core::convert::From<&'a Option<T>>>::from ](
    option: &'a Option<T>,
) -> (res: Option<&'a T>)
    ensures
        res is Some <==> option is Some,
        res is Some ==> option->0 == res->0,
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

// unwrap_unchecked
pub assume_specification<T>[ Option::<T>::unwrap_unchecked ](option: Option<T>) -> (t: T)
    requires
        option is Some,
    ensures
        t == option->0,
    no_unwind
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
    no_unwind
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
        *final(option) is None,
    no_unwind
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

// inspect
pub assume_specification<T, F: FnOnce(&T)>[ Option::<T>::inspect ](option: Option<T>, f: F) -> (res:
    Option<T>)
    requires
        option is Some ==> f.requires((&option->0,)),
    ensures
        res is Some <==> option is Some,
        res is None <==> option is None,
        option is Some ==> f.ensures((&option->0,), ()),
;

// map_or
pub assume_specification<T, U, F: FnOnce(T) -> U>[ Option::<T>::map_or ](
    option: Option<T>,
    default: U,
    f: F,
) -> (res: U)
    requires
        option is Some ==> f.requires((option->0,)),
    ensures
        option is Some ==> exists|output: U| f.ensures((option->0,), output),
;

// map_or_else
pub assume_specification<T, U, D: FnOnce() -> U, F: FnOnce(T) -> U>[ Option::<T>::map_or_else ](
    option: Option<T>,
    default: D,
    f: F,
) -> (res: U)
    requires
        option is None ==> default.requires(()),
        option is Some ==> f.requires((option->0,)),
    ensures
        option is None ==> exists|output: U| default.ensures((), output),
        option is Some ==> exists|output: U| f.ensures((option->0,), output),
;

// filter
pub assume_specification<T, P: FnOnce(&T) -> bool>[ Option::<T>::filter ](
    option: Option<T>,
    predicate: P,
) -> (res: Option<T>)
    requires
        option is Some ==> predicate.requires((&option->0,)),
    ensures
        option is None ==> res is None,
        option is Some ==> {
            ||| res is Some && predicate.ensures((&option->0,), true)
            ||| res is None && predicate.ensures((&option->0,), false)
        },
;

// cloned
pub assume_specification<'a, T: Clone>[ Option::<&'a T>::cloned ](opt: Option<&'a T>) -> (res:
    Option<T>)
    ensures
        opt.is_none() ==> res.is_none(),
        opt.is_some() ==> res.is_some() && cloned::<T>(*opt.unwrap(), res.unwrap()),
;

// copied (Option<&T>)
pub assume_specification<'a, T: Copy>[ Option::<&'a T>::copied ](opt: Option<&'a T>) -> (res:
    Option<T>)
    ensures
        opt.is_none() ==> res.is_none(),
        opt.is_some() ==> res == Some(*opt.unwrap()),
    no_unwind
;

// copied (Option<&mut T>)
pub assume_specification<'a, T: Copy>[ Option::<&'a mut T>::copied ](
    opt: Option<&'a mut T>,
) -> (res: Option<T>)
    ensures
        opt.is_none() ==> res.is_none(),
        opt.is_some() ==> res == Some(*opt.unwrap()) && *final(opt.unwrap()) == *opt.unwrap(),
    no_unwind
;

// cloned (Option<&mut T>)
pub assume_specification<'a, T: Clone>[ Option::<&'a mut T>::cloned ](
    opt: Option<&'a mut T>,
) -> (res: Option<T>)
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

// PartialEq and Eq
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

// PartialOrd and Ord
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
pub assume_specification<T>[ Option::as_mut ](option: &mut Option<T>) -> (res: Option<&mut T>)
    ensures
        (match *old(option) {
            None => final(option).is_none() && res.is_none(),
            Some(r) => final(option).is_some() && res.is_some() && *res.unwrap() == r
                && *final(res.unwrap()) == final(option).unwrap(),
        }),
;

// From<&mut Option<T>> for Option<&mut T>
pub assume_specification<'a, T>[ <Option<&'a mut T> as core::convert::From<
    &'a mut Option<T>,
>>::from ](option: &'a mut Option<T>) -> (res: Option<&'a mut T>)
    ensures
        (match *old(option) {
            None => final(option).is_none() && res.is_none(),
            Some(r) => final(option).is_some() && res.is_some() && *res.unwrap() == r
                && *final(res.unwrap()) == final(option).unwrap(),
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
pub assume_specification<T>[ Option::as_mut_slice ](option: &mut Option<T>) -> (res: &mut [T])
    ensures
        res@ == (match *old(option) {
            Some(x) => seq![x],
            None => seq![],
        }),
        final(res)@.len() == res@.len(),  // TODO this should be broadcast for all `&mut [T]`
        final(option)@ == (match *old(option) {
            Some(_) => Some(final(res)@[0]),
            None => None,
        }),
;

#[doc(hidden)]
pub assume_specification<T>[ Option::insert ](option: &mut Option<T>, value: T) -> (res: &mut T)
    ensures
        *res == value,
        *final(option) == Some(*final(res)),
;

#[doc(hidden)]
pub assume_specification<T>[ Option::get_or_insert ](option: &mut Option<T>, value: T) -> (res:
    &mut T)
    ensures
        *res == (match *old(option) {
            Some(x) => x,
            None => value,
        }),
        *final(option) == Some(*final(res)),
;

#[doc(hidden)]
pub assume_specification<T, F: FnOnce() -> T>[ Option::<T>::get_or_insert_with ](
    option: &mut Option<T>,
    f: F,
) -> (res: &mut T)
    requires
        *old(option) is None ==> f.requires(()),
    ensures
        *old(option) is None ==> f.ensures((), *res),
        *final(option) == Some(*final(res)),
;

#[doc(hidden)]
pub assume_specification<T: core::default::Default>[ Option::<T>::get_or_insert_default ](
    option: &mut Option<T>,
) -> (res: &mut T)
    ensures
        old(option).is_some() ==> *res == old(option)->0,
        old(option).is_none() ==> T::default.ensures((), *res),
        *final(option) == Some(*final(res)),
;

// and
pub assume_specification<T, U>[ Option::<T>::and ](option: Option<T>, optb: Option<U>) -> (res:
    Option<U>)
    ensures
        option is None ==> res is None,
        option is Some ==> res == optb,
;

// or
pub assume_specification<T>[ Option::<T>::or ](option: Option<T>, optb: Option<T>) -> (res: Option<
    T,
>)
    ensures
        option is Some ==> res == option,
        option is None ==> res == optb,
;

// or_else
pub assume_specification<T, F: FnOnce() -> Option<T>>[ Option::<T>::or_else ](
    option: Option<T>,
    f: F,
) -> (res: Option<T>)
    requires
        option is None ==> f.requires(()),
    ensures
        option is Some ==> res is Some,
        option is None ==> f.ensures((), res),
;

// xor
pub assume_specification<T>[ Option::<T>::xor ](option: Option<T>, optb: Option<T>) -> (res: Option<
    T,
>)
    ensures
        (option is Some && optb is None) ==> res == option,
        (option is None && optb is Some) ==> res == optb,
        (option is None && optb is None) ==> res is None,
        (option is Some && optb is Some) ==> res is None,
;

// replace
pub assume_specification<T>[ Option::<T>::replace ](option: &mut Option<T>, value: T) -> (res:
    Option<T>)
    ensures
        res == *old(option),
        *final(option) == Some(value),
    no_unwind
;

// take_if
pub assume_specification<T, P: FnOnce(&mut T) -> bool>[ Option::<T>::take_if ](
    option: &mut Option<T>,
    predicate: P,
) -> (res: Option<T>)
    requires
        *old(option) is Some ==> forall|value: &mut T|
            *value == old(option)->0 ==> #[trigger] predicate.requires((value,)),
    ensures
        *old(option) is None ==> res is None && final(option).is_none(),
        *old(option) is Some ==> exists|value: &mut T, take: bool|
            {
                &&& *value == old(option)->0
                &&& predicate.ensures((value,), take)
                &&& if take {
                    res == Some(*final(value)) && final(option).is_none()
                } else {
                    res is None && *final(option) == Some(*final(value))
                }
            },
;

// zip
pub assume_specification<T, U>[ Option::<T>::zip ](option: Option<T>, other: Option<U>) -> (res:
    Option<(T, U)>)
    ensures
        (option is Some && other is Some) ==> res == Some((option->0, other->0)),
        (option is None || other is None) ==> res is None,
;

// unzip
pub assume_specification<T, U>[ Option::<(T, U)>::unzip ](option: Option<(T, U)>) -> (res: (
    Option<T>,
    Option<U>,
))
    ensures
        option is Some ==> res == (Some((option->0).0), Some((option->0).1)),
        option is None ==> res == (None::<T>, None::<U>),
    no_unwind
;

// flatten
pub assume_specification<T>[ Option::<Option<T>>::flatten ](option: Option<Option<T>>) -> (res:
    Option<T>)
    ensures
        option is Some ==> res == option->0,
        option is None ==> res is None,
    no_unwind
;

// transpose (Option<Result<T, E>>)
pub assume_specification<T, E>[ Option::<Result<T, E>>::transpose ](
    option: Option<Result<T, E>>,
) -> (res: Result<Option<T>, E>)
    ensures
        option is None ==> res == Ok(None::<T>),
        (option is Some && option->0 is Ok) ==> res == Ok(Some(option->0->Ok_0)),
        (option is Some && option->0 is Err) ==> res == Err(option->0->Err_0),
    no_unwind
;

////// Lemmas
/// Converting an option to a result and projecting the success value is a round trip.
pub proof fn lemma_spec_ok_or_ok_round_trip<T, E>(option: Option<T>, err: E)
    ensures
        super::result::ok(spec_ok_or(option, err)) == option,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// Projecting a result and restoring its error reconstructs the original result.
pub proof fn lemma_spec_ok_or_result_round_trip<T, E>(result: Result<T, E>, fallback: E)
    ensures
        spec_ok_or(
            super::result::ok(result),
            match result {
                Ok(_) => fallback,
                Err(err) => err,
            },
        ) == result,
{
    match result {
        Ok(_) => {},
        Err(_) => {},
    }
}

/// Unzipping and then zipping an optional pair reconstructs the original option.
pub proof fn lemma_unzip_zip_round_trip<T, U>(
    option: Option<(T, U)>,
    unzipped: (Option<T>, Option<U>),
    rezipped: Option<(T, U)>,
)
    requires
        call_ensures(Option::<(T, U)>::unzip, (option,), unzipped),
        call_ensures(Option::<T>::zip::<U>, (unzipped.0, unzipped.1), rezipped),
    ensures
        rezipped == option,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// Zipping commutes up to swapping the pair components.
pub proof fn lemma_zip_commutes<T, U>(
    left: Option<T>,
    right: Option<U>,
    left_right: Option<(T, U)>,
    right_left: Option<(U, T)>,
)
    requires
        call_ensures(Option::<T>::zip::<U>, (left, right), left_right),
        call_ensures(Option::<U>::zip::<T>, (right, left), right_left),
    ensures
        left_right == match right_left {
            Some((right_value, left_value)) => Some((left_value, right_value)),
            None => None,
        },
{
    match left {
        Some(_) => match right {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// Nested zips agree up to reassociating their tuple payload.
pub proof fn lemma_zip_associative<T, U, V>(
    first: Option<T>,
    second: Option<U>,
    third: Option<V>,
    first_second: Option<(T, U)>,
    left: Option<((T, U), V)>,
    second_third: Option<(U, V)>,
    right: Option<(T, (U, V))>,
)
    requires
        call_ensures(Option::<T>::zip::<U>, (first, second), first_second),
        call_ensures(Option::<(T, U)>::zip::<V>, (first_second, third), left),
        call_ensures(Option::<U>::zip::<V>, (second, third), second_third),
        call_ensures(Option::<T>::zip::<(U, V)>, (first, second_third), right),
    ensures
        left == match right {
            Some((first_value, (second_value, third_value))) => {
                Some(((first_value, second_value), third_value))
            },
            None => None,
        },
{
    match first {
        Some(_) => match second {
            Some(_) => match third {
                Some(_) => {},
                None => {},
            },
            None => {},
        },
        None => {},
    }
}

/// Option conjunction is associative.
pub proof fn lemma_and_associative<T, U, V>(
    first: Option<T>,
    second: Option<U>,
    third: Option<V>,
    first_second: Option<U>,
    left: Option<V>,
    second_third: Option<V>,
    right: Option<V>,
)
    requires
        call_ensures(Option::<T>::and::<U>, (first, second), first_second),
        call_ensures(Option::<U>::and::<V>, (first_second, third), left),
        call_ensures(Option::<U>::and::<V>, (second, third), second_third),
        call_ensures(Option::<T>::and::<V>, (first, second_third), right),
    ensures
        left == right,
{
    match first {
        Some(_) => match second {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// Option disjunction is associative.
pub proof fn lemma_or_associative<T>(
    first: Option<T>,
    second: Option<T>,
    third: Option<T>,
    first_second: Option<T>,
    left: Option<T>,
    second_third: Option<T>,
    right: Option<T>,
)
    requires
        call_ensures(Option::<T>::or, (first, second), first_second),
        call_ensures(Option::<T>::or, (first_second, third), left),
        call_ensures(Option::<T>::or, (second, third), second_third),
        call_ensures(Option::<T>::or, (first, second_third), right),
    ensures
        left == right,
{
    match first {
        Some(_) => {},
        None => match second {
            Some(_) => {},
            None => {},
        },
    }
}

/// Exclusive option choice is commutative.
pub proof fn lemma_xor_commutes<T>(
    left: Option<T>,
    right: Option<T>,
    left_right: Option<T>,
    right_left: Option<T>,
)
    requires
        call_ensures(Option::<T>::xor, (left, right), left_right),
        call_ensures(Option::<T>::xor, (right, left), right_left),
    ensures
        left_right == right_left,
{
    match left {
        Some(_) => match right {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// Exclusive option choice cancels identical operands.
pub proof fn lemma_xor_self<T>(option: Option<T>, result: Option<T>)
    requires
        call_ensures(Option::<T>::xor, (option, option), result),
    ensures
        result is None,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// Constructing an option from a value and projecting its payload is a round trip.
pub proof fn lemma_from_value_unwrap_round_trip<T>(value: T, option: Option<T>)
    requires
        call_ensures(<Option<T> as core::convert::From<T>>::from, (value,), option),
    ensures
        spec_unwrap(option) == value,
{
}

/// The borrowed `From` conversion agrees with `Option::as_ref`.
pub proof fn lemma_from_ref_agrees_with_as_ref<'a, T>(
    option: &'a Option<T>,
    from_result: Option<&'a T>,
    as_ref_result: Option<&'a T>,
)
    requires
        call_ensures(
            <Option<&'a T> as core::convert::From<&'a Option<T>>>::from,
            (option,),
            from_result,
        ),
        call_ensures(Option::<T>::as_ref, (option,), as_ref_result),
    ensures
        from_result == as_ref_result,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// `unwrap` and `expect` return the same payload on a present option.
pub proof fn lemma_expect_agrees_with_unwrap<T>(
    option: Option<T>,
    msg: &str,
    unwrap_result: T,
    expect_result: T,
)
    requires
        option is Some,
        call_ensures(Option::<T>::unwrap, (option,), unwrap_result),
        call_ensures(Option::<T>::expect, (option, msg), expect_result),
    ensures
        expect_result == unwrap_result,
{
}

/// The default argument does not affect `unwrap_or` on a present option.
pub proof fn lemma_unwrap_or_agrees_with_unwrap<T>(
    option: Option<T>,
    default: T,
    unwrap_result: T,
    unwrap_or_result: T,
)
    requires
        option is Some,
        call_ensures(Option::<T>::unwrap, (option,), unwrap_result),
        call_ensures(Option::<T>::unwrap_or, (option, default), unwrap_or_result),
    ensures
        unwrap_or_result == unwrap_result,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// A present left operand is the left identity for option conjunction.
pub proof fn lemma_and_some_left_identity<T, U>(marker: T, option: Option<U>, result: Option<U>)
    requires
        call_ensures(Option::<T>::and::<U>, (Some(marker), option), result),
    ensures
        result == option,
{
}

/// `None` is the right identity for option disjunction.
pub proof fn lemma_or_none_right_identity<T>(option: Option<T>, result: Option<T>)
    requires
        call_ensures(Option::<T>::or, (option, None), result),
    ensures
        result == option,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// Option disjunction is idempotent.
pub proof fn lemma_or_idempotent<T>(option: Option<T>, result: Option<T>)
    requires
        call_ensures(Option::<T>::or, (option, option), result),
    ensures
        result == option,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// `None` is the right identity for exclusive option choice.
pub proof fn lemma_xor_none_right_identity<T>(option: Option<T>, result: Option<T>)
    requires
        call_ensures(Option::<T>::xor, (option, None), result),
    ensures
        result == option,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// Zipping and then unzipping preserves operands with matching presence.
pub proof fn lemma_zip_unzip_round_trip<T, U>(
    left: Option<T>,
    right: Option<U>,
    zipped: Option<(T, U)>,
    unzipped: (Option<T>, Option<U>),
)
    requires
        (left is Some) == (right is Some),
        call_ensures(Option::<T>::zip::<U>, (left, right), zipped),
        call_ensures(Option::<(T, U)>::unzip, (zipped,), unzipped),
    ensures
        unzipped == (left, right),
{
    match left {
        Some(_) => match right {
            Some(_) => {},
            None => {},
        },
        None => match right {
            Some(_) => {},
            None => {},
        },
    }
}

/// Mapping with a callback that returns its input preserves the option.
pub proof fn lemma_map_identity<T, F: FnOnce(T) -> T>(option: Option<T>, f: F, mapped: Option<T>)
    requires
        forall|input: T, output: T| #[trigger] f.ensures((input,), output) ==> output == input,
        call_ensures(Option::<T>::map::<T, F>, (option, f), mapped),
    ensures
        mapped == option,
{
    match option {
        Some(_) => match mapped {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// Two consecutive maps agree with one map by the composed callback model.
pub proof fn lemma_map_composition<
    T,
    U,
    V,
    F: FnOnce(T) -> U,
    G: FnOnce(U) -> V,
    H: FnOnce(T) -> V,
>(
    option: Option<T>,
    first_model: spec_fn(T) -> U,
    second_model: spec_fn(U) -> V,
    first_f: F,
    second_f: G,
    composed_f: H,
    first_mapped: Option<U>,
    consecutively_mapped: Option<V>,
    directly_mapped: Option<V>,
)
    requires
        forall|input: T, output: U| #[trigger]
            first_f.ensures((input,), output) ==> output == first_model(input),
        forall|input: U, output: V| #[trigger]
            second_f.ensures((input,), output) ==> output == second_model(input),
        forall|input: T, output: V| #[trigger]
            composed_f.ensures((input,), output) ==> output == second_model(first_model(input)),
        call_ensures(Option::<T>::map::<U, F>, (option, first_f), first_mapped),
        call_ensures(Option::<U>::map::<V, G>, (first_mapped, second_f), consecutively_mapped),
        call_ensures(Option::<T>::map::<V, H>, (option, composed_f), directly_mapped),
    ensures
        consecutively_mapped == directly_mapped,
{
    match option {
        Some(_) => match first_mapped {
            Some(_) => match consecutively_mapped {
                Some(_) => match directly_mapped {
                    Some(_) => {},
                    None => {},
                },
                None => {},
            },
            None => {},
        },
        None => {},
    }
}

/// Binding with a callback that rewraps its input preserves the option.
pub proof fn lemma_and_then_right_identity<T, F: FnOnce(T) -> Option<T>>(
    option: Option<T>,
    f: F,
    result: Option<T>,
)
    requires
        forall|input: T, output: Option<T>| #[trigger]
            f.ensures((input,), output) ==> output == Some(input),
        call_ensures(Option::<T>::and_then::<T, F>, (option, f), result),
    ensures
        result == option,
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// Binding agrees with mapping the same optional callback result and flattening.
pub proof fn lemma_and_then_agrees_with_map_then_flatten<
    T,
    U,
    F: FnOnce(T) -> Option<U>,
    G: FnOnce(T) -> Option<U>,
>(
    option: Option<T>,
    model: spec_fn(T) -> Option<U>,
    and_then_f: F,
    map_f: G,
    bound: Option<U>,
    mapped: Option<Option<U>>,
    flattened: Option<U>,
)
    requires
        forall|input: T, output: Option<U>| #[trigger]
            and_then_f.ensures((input,), output) ==> output == model(input),
        forall|input: T, output: Option<U>| #[trigger]
            map_f.ensures((input,), output) ==> output == model(input),
        call_ensures(Option::<T>::and_then::<U, F>, (option, and_then_f), bound),
        call_ensures(Option::<T>::map::<Option<U>, G>, (option, map_f), mapped),
        call_ensures(Option::<Option<U>>::flatten, (mapped,), flattened),
    ensures
        bound == flattened,
{
    match option {
        Some(_) => match mapped {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// Flattening nested options is associative.
pub proof fn lemma_flatten_associative<T, F: FnOnce(Option<Option<T>>) -> Option<T>>(
    option: Option<Option<Option<T>>>,
    flatten_f: F,
    left_middle: Option<Option<T>>,
    left: Option<T>,
    right_middle: Option<Option<T>>,
    right: Option<T>,
)
    requires
        forall|input: Option<Option<T>>, output: Option<T>| #[trigger]
            flatten_f.ensures((input,), output) ==> output == match input {
                Some(inner) => inner,
                None => None,
            },
        call_ensures(Option::<Option<Option<T>>>::flatten, (option,), left_middle),
        call_ensures(Option::<Option<T>>::flatten, (left_middle,), left),
        call_ensures(
            Option::<Option<Option<T>>>::map::<Option<T>, F>,
            (option, flatten_f),
            right_middle,
        ),
        call_ensures(Option::<Option<T>>::flatten, (right_middle,), right),
    ensures
        left == right,
{
    match option {
        Some(inner) => match inner {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// `is_some_and` agrees with whether filtering by the same predicate keeps a value.
pub proof fn lemma_is_some_and_agrees_with_filter_presence<
    T,
    F: FnOnce(T) -> bool,
    P: FnOnce(&T) -> bool,
>(
    option: Option<T>,
    predicate: spec_fn(T) -> bool,
    owned_predicate: F,
    borrowed_predicate: P,
    is_some_and_result: bool,
    filtered: Option<T>,
)
    requires
        forall|input: T, output: bool| #[trigger]
            owned_predicate.ensures((input,), output) ==> output == predicate(input),
        forall|input: &T, output: bool| #[trigger]
            borrowed_predicate.ensures((input,), output) ==> output == predicate(*input),
        call_ensures(Option::<T>::is_some_and, (option, owned_predicate), is_some_and_result),
        call_ensures(Option::<T>::filter::<P>, (option, borrowed_predicate), filtered),
    ensures
        is_some_and_result == (filtered is Some),
{
    match option {
        Some(_) => match filtered {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// `is_none_or` is the disjunction of absence and `is_some_and` for the same model.
pub proof fn lemma_is_none_or_agrees_with_is_some_and<
    T,
    F: FnOnce(T) -> bool,
    G: FnOnce(T) -> bool,
>(
    option: Option<T>,
    predicate: spec_fn(T) -> bool,
    is_some_and_f: F,
    is_none_or_f: G,
    present: bool,
    is_some_and_result: bool,
    is_none_or_result: bool,
)
    requires
        forall|input: T, output: bool| #[trigger]
            is_some_and_f.ensures((input,), output) ==> output == predicate(input),
        forall|input: T, output: bool| #[trigger]
            is_none_or_f.ensures((input,), output) ==> output == predicate(input),
        call_ensures(Option::<T>::is_some, (&option,), present),
        call_ensures(Option::<T>::is_some_and, (option, is_some_and_f), is_some_and_result),
        call_ensures(Option::<T>::is_none_or, (option, is_none_or_f), is_none_or_result),
    ensures
        is_none_or_result == (!present || is_some_and_result),
{
    match option {
        Some(_) => {},
        None => {},
    }
}

/// Inspection preserves the result of testing whether the option is present.
pub proof fn lemma_inspect_preserves_is_some<T, F: FnOnce(&T)>(
    option: Option<T>,
    f: F,
    inspected: Option<T>,
    before: bool,
    after: bool,
)
    requires
        call_ensures(Option::<T>::inspect::<F>, (option, f), inspected),
        call_ensures(Option::<T>::is_some, (&option,), before),
        call_ensures(Option::<T>::is_some, (&inspected,), after),
    ensures
        after == before,
{
    match option {
        Some(_) => match inspected {
            Some(_) => {},
            None => {},
        },
        None => {},
    }
}

/// Eager and lazy disjunction agree on presence when their fallbacks have the same shape.
pub proof fn lemma_or_agrees_with_or_else_presence<T, F: FnOnce() -> Option<T>>(
    option: Option<T>,
    fallback: Option<T>,
    f: F,
    or_result: Option<T>,
    or_else_result: Option<T>,
)
    requires
        forall|output: Option<T>| #[trigger]
            f.ensures((), output) ==> (output is Some) == (fallback is Some),
        call_ensures(Option::<T>::or, (option, fallback), or_result),
        call_ensures(Option::<T>::or_else::<F>, (option, f), or_else_result),
    ensures
        (or_result is Some) == (or_else_result is Some),
{
    match option {
        Some(_) => {},
        None => match fallback {
            Some(_) => {},
            None => {},
        },
    }
}

/// Viewing an option as a slice gives cardinality zero or one according to `is_some`.
pub proof fn lemma_as_slice_len_agrees_with_is_some<T>(
    option: &Option<T>,
    slice: &[T],
    present: bool,
)
    requires
        call_ensures(Option::<T>::as_slice, (option,), slice),
        call_ensures(Option::<T>::is_some, (option,), present),
    ensures
        slice@.len() == if present {
            1nat
        } else {
            0nat
        },
{
    broadcast use crate::seq::lemma_seq_empty;

    match *option {
        Some(value) => {
            crate::seq::lemma_seq_push_len(Seq::<T>::empty(), value);
            assert(is_some(option));
            assert(slice@ == seq![value]);
            assert(slice@.len() == 1nat);
        },
        None => {
            assert(!is_some(option));
            assert(slice@ == seq![]);
            assert(slice@.len() == 0nat);
        },
    }
}

} // verus!
