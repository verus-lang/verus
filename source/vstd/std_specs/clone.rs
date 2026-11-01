use super::super::prelude::*;
use core::clone::Clone;

verus! {

#[verifier::external_trait_specification]
pub trait ExClone: Sized {
    type ExternalTraitSpecificationFor: core::clone::Clone;

    fn clone(&self) -> Self;

    fn clone_from(&mut self, source: &Self)
        default_ensures
            call_ensures(Self::clone, (source,), *final(self)),
    ;
}

#[verifier::external_trait_specification]
pub trait ExCopy: Clone {
    type ExternalTraitSpecificationFor: core::marker::Copy;
}

pub assume_specification[ <bool as Clone>::clone ](b: &bool) -> (res: bool)
    returns
        b,
;

pub assume_specification[ <char as Clone>::clone ](c: &char) -> (res: char)
    returns
        c,
;

#[allow(suspicious_double_ref_op)]
pub assume_specification<'b, T: core::marker::PointeeSized, 'a>[ <&'b T as Clone>::clone ](
    b: &'a &'b T,
) -> (res: &'b T)
    ensures
        res == b,
;

pub assume_specification<T: Clone, const N: usize>[ <[T; N] as Clone>::clone ](a: &[T; N]) -> (res:
    [T; N])
    ensures
        forall|i| #![all_triggers] 0 <= i < N ==> cloned::<T>(a@[i], res@[i]),
        a@ =~= res@ ==> a@ == res@,
;

// Elements are updated with T::clone_from, or copied when T: TrivialClone,
// so only the non-strict relation holds.
pub assume_specification<T: Clone, const N: usize>[ <[T; N] as Clone>::clone_from ](
    dest: &mut [T; N],
    source: &[T; N],
)
    ensures
        forall|i|
            #![all_triggers]
            0 <= i < N ==> cloned_from::<T>(source@[i], old(dest)@[i], final(dest)@[i]),
        source@ =~= final(dest)@ ==> source@ == final(dest)@,
;

// Cloning a Tracked copies the underlying ghost T
pub assume_specification<T: Copy>[ <Tracked<T> as Clone>::clone ](b: &Tracked<T>) -> (res: Tracked<
    T,
>)
    ensures
        res == b,
;

pub assume_specification<T>[ <Ghost<T> as Clone>::clone ](b: &Ghost<T>) -> (res: Ghost<T>)
    ensures
        res == b,
;

} // verus!
