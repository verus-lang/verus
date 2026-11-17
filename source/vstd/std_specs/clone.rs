use super::super::prelude::*;
use core::clone::Clone;

verus! {

#[verifier::external_trait_specification]
pub trait ExClone: Sized {
    type ExternalTraitSpecificationFor: core::clone::Clone;

    fn clone(&self) -> Self;
}

#[verifier::external_trait_specification]
pub trait ExCopy: Clone {
    type ExternalTraitSpecificationFor: core::marker::Copy;
}

// The safety obligation of `TrivialClone` (that `clone` is equivalent to a copy)
// is special-cased internally by Verus:
// for each `TrivialClone` impl, Verus adds `ensures ret == self`
// to the corresponding `Clone::clone` implementation.
#[verifier::external_trait_specification]
pub unsafe trait ExTrivialClone: Clone {
    type ExternalTraitSpecificationFor: core::clone::TrivialClone;
}

/*
#[verifier::external_fn_specification]
pub fn ex_clone_clone_from<T: Clone>(a: &mut T, b: &T)
{
    a.clone_from(b)
}
*/

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

/*
#[verifier::external_fn_specification]
pub fn ex_bool_clone_from(dest: &mut bool, source: &bool)
    ensures *dest == source,
{
    dest.clone_from(source)
}
*/

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

// The `Clone` impls of tuples are built into the compiler, so they have no item an
// `assume_specification` could name. Verus lowers `Clone::clone` on a tuple whose components
// are not all copies to a call of `clone_tupleN`, which clones component-wise, as rustc's
// clone shim does.
#[doc(hidden)]
#[verusfmt::skip]
pub fn clone_tuple1<A: Clone>(x: &(A,)) -> (r: (A,))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
{
    (x.0.clone(),)
}

#[doc(hidden)]
pub fn clone_tuple2<A: Clone, B: Clone>(x: &(A, B)) -> (r: (A, B))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
{
    (x.0.clone(), x.1.clone())
}

#[doc(hidden)]
pub fn clone_tuple3<A: Clone, B: Clone, C: Clone>(x: &(A, B, C)) -> (r: (A, B, C))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
{
    (x.0.clone(), x.1.clone(), x.2.clone())
}

#[doc(hidden)]
pub fn clone_tuple4<A: Clone, B: Clone, C: Clone, D: Clone>(x: &(A, B, C, D)) -> (r: (A, B, C, D))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
{
    (x.0.clone(), x.1.clone(), x.2.clone(), x.3.clone())
}

#[doc(hidden)]
pub fn clone_tuple5<A: Clone, B: Clone, C: Clone, D: Clone, E: Clone>(x: &(A, B, C, D, E)) -> (r: (
    A,
    B,
    C,
    D,
    E,
))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
{
    (x.0.clone(), x.1.clone(), x.2.clone(), x.3.clone(), x.4.clone())
}

#[doc(hidden)]
pub fn clone_tuple6<A: Clone, B: Clone, C: Clone, D: Clone, E: Clone, F: Clone>(
    x: &(A, B, C, D, E, F),
) -> (r: (A, B, C, D, E, F))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
        super::super::pervasive::strictly_cloned(x.5, r.5),
{
    (x.0.clone(), x.1.clone(), x.2.clone(), x.3.clone(), x.4.clone(), x.5.clone())
}

#[doc(hidden)]
pub fn clone_tuple7<A: Clone, B: Clone, C: Clone, D: Clone, E: Clone, F: Clone, G: Clone>(
    x: &(A, B, C, D, E, F, G),
) -> (r: (A, B, C, D, E, F, G))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
        super::super::pervasive::strictly_cloned(x.5, r.5),
        super::super::pervasive::strictly_cloned(x.6, r.6),
{
    (x.0.clone(), x.1.clone(), x.2.clone(), x.3.clone(), x.4.clone(), x.5.clone(), x.6.clone())
}

#[doc(hidden)]
pub fn clone_tuple8<A: Clone, B: Clone, C: Clone, D: Clone, E: Clone, F: Clone, G: Clone, H: Clone>(
    x: &(A, B, C, D, E, F, G, H),
) -> (r: (A, B, C, D, E, F, G, H))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
        super::super::pervasive::strictly_cloned(x.5, r.5),
        super::super::pervasive::strictly_cloned(x.6, r.6),
        super::super::pervasive::strictly_cloned(x.7, r.7),
{
    (
        x.0.clone(),
        x.1.clone(),
        x.2.clone(),
        x.3.clone(),
        x.4.clone(),
        x.5.clone(),
        x.6.clone(),
        x.7.clone(),
    )
}

#[doc(hidden)]
pub fn clone_tuple9<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
>(x: &(A, B, C, D, E, F, G, H, I)) -> (r: (A, B, C, D, E, F, G, H, I))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
        super::super::pervasive::strictly_cloned(x.5, r.5),
        super::super::pervasive::strictly_cloned(x.6, r.6),
        super::super::pervasive::strictly_cloned(x.7, r.7),
        super::super::pervasive::strictly_cloned(x.8, r.8),
{
    (
        x.0.clone(),
        x.1.clone(),
        x.2.clone(),
        x.3.clone(),
        x.4.clone(),
        x.5.clone(),
        x.6.clone(),
        x.7.clone(),
        x.8.clone(),
    )
}

#[doc(hidden)]
pub fn clone_tuple10<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
    J: Clone,
>(x: &(A, B, C, D, E, F, G, H, I, J)) -> (r: (A, B, C, D, E, F, G, H, I, J))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
        super::super::pervasive::strictly_cloned(x.5, r.5),
        super::super::pervasive::strictly_cloned(x.6, r.6),
        super::super::pervasive::strictly_cloned(x.7, r.7),
        super::super::pervasive::strictly_cloned(x.8, r.8),
        super::super::pervasive::strictly_cloned(x.9, r.9),
{
    (
        x.0.clone(),
        x.1.clone(),
        x.2.clone(),
        x.3.clone(),
        x.4.clone(),
        x.5.clone(),
        x.6.clone(),
        x.7.clone(),
        x.8.clone(),
        x.9.clone(),
    )
}

#[doc(hidden)]
pub fn clone_tuple11<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
    J: Clone,
    K: Clone,
>(x: &(A, B, C, D, E, F, G, H, I, J, K)) -> (r: (A, B, C, D, E, F, G, H, I, J, K))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
        super::super::pervasive::strictly_cloned(x.5, r.5),
        super::super::pervasive::strictly_cloned(x.6, r.6),
        super::super::pervasive::strictly_cloned(x.7, r.7),
        super::super::pervasive::strictly_cloned(x.8, r.8),
        super::super::pervasive::strictly_cloned(x.9, r.9),
        super::super::pervasive::strictly_cloned(x.10, r.10),
{
    (
        x.0.clone(),
        x.1.clone(),
        x.2.clone(),
        x.3.clone(),
        x.4.clone(),
        x.5.clone(),
        x.6.clone(),
        x.7.clone(),
        x.8.clone(),
        x.9.clone(),
        x.10.clone(),
    )
}

#[doc(hidden)]
pub fn clone_tuple12<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
    J: Clone,
    K: Clone,
    L: Clone,
>(x: &(A, B, C, D, E, F, G, H, I, J, K, L)) -> (r: (A, B, C, D, E, F, G, H, I, J, K, L))
    ensures
        super::super::pervasive::strictly_cloned(x.0, r.0),
        super::super::pervasive::strictly_cloned(x.1, r.1),
        super::super::pervasive::strictly_cloned(x.2, r.2),
        super::super::pervasive::strictly_cloned(x.3, r.3),
        super::super::pervasive::strictly_cloned(x.4, r.4),
        super::super::pervasive::strictly_cloned(x.5, r.5),
        super::super::pervasive::strictly_cloned(x.6, r.6),
        super::super::pervasive::strictly_cloned(x.7, r.7),
        super::super::pervasive::strictly_cloned(x.8, r.8),
        super::super::pervasive::strictly_cloned(x.9, r.9),
        super::super::pervasive::strictly_cloned(x.10, r.10),
        super::super::pervasive::strictly_cloned(x.11, r.11),
{
    (
        x.0.clone(),
        x.1.clone(),
        x.2.clone(),
        x.3.clone(),
        x.4.clone(),
        x.5.clone(),
        x.6.clone(),
        x.7.clone(),
        x.8.clone(),
        x.9.clone(),
        x.10.clone(),
        x.11.clone(),
    )
}

// The built-in clone of a tuple clones its components (rustc's clone shim), so a tuple is
// strictly cloned exactly when each component is. Without this, a nested tuple's clone (a
// generic `B::clone` inside `clone_tupleN`) says nothing. Not in the default group, since it
// slows down unrelated proofs: `broadcast use vstd::std_specs::clone::group_clone_tuple_axioms;`
// where nested tuples are cloned.
#[verusfmt::skip]
pub broadcast axiom fn axiom_strictly_cloned_tuple1<A: Clone>(x: (A,), r: (A,))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r)
            <==> super::super::pervasive::strictly_cloned(x.0, r.0),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple2<A: Clone, B: Clone>(x: (A, B), r: (A, B))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple3<A: Clone, B: Clone, C: Clone>(
    x: (A, B, C),
    r: (A, B, C),
)
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple4<A: Clone, B: Clone, C: Clone, D: Clone>(
    x: (A, B, C, D),
    r: (A, B, C, D),
)
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple5<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
>(x: (A, B, C, D, E), r: (A, B, C, D, E))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple6<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
>(x: (A, B, C, D, E, F), r: (A, B, C, D, E, F))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)
            && super::super::pervasive::strictly_cloned(x.5, r.5)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple7<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
>(x: (A, B, C, D, E, F, G), r: (A, B, C, D, E, F, G))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)
            && super::super::pervasive::strictly_cloned(x.5, r.5)
            && super::super::pervasive::strictly_cloned(x.6, r.6)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple8<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
>(x: (A, B, C, D, E, F, G, H), r: (A, B, C, D, E, F, G, H))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)
            && super::super::pervasive::strictly_cloned(x.5, r.5)
            && super::super::pervasive::strictly_cloned(x.6, r.6)
            && super::super::pervasive::strictly_cloned(x.7, r.7)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple9<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
>(x: (A, B, C, D, E, F, G, H, I), r: (A, B, C, D, E, F, G, H, I))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)
            && super::super::pervasive::strictly_cloned(x.5, r.5)
            && super::super::pervasive::strictly_cloned(x.6, r.6)
            && super::super::pervasive::strictly_cloned(x.7, r.7)
            && super::super::pervasive::strictly_cloned(x.8, r.8)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple10<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
    J: Clone,
>(x: (A, B, C, D, E, F, G, H, I, J), r: (A, B, C, D, E, F, G, H, I, J))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)
            && super::super::pervasive::strictly_cloned(x.5, r.5)
            && super::super::pervasive::strictly_cloned(x.6, r.6)
            && super::super::pervasive::strictly_cloned(x.7, r.7)
            && super::super::pervasive::strictly_cloned(x.8, r.8)
            && super::super::pervasive::strictly_cloned(x.9, r.9)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple11<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
    J: Clone,
    K: Clone,
>(x: (A, B, C, D, E, F, G, H, I, J, K), r: (A, B, C, D, E, F, G, H, I, J, K))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)
            && super::super::pervasive::strictly_cloned(x.5, r.5)
            && super::super::pervasive::strictly_cloned(x.6, r.6)
            && super::super::pervasive::strictly_cloned(x.7, r.7)
            && super::super::pervasive::strictly_cloned(x.8, r.8)
            && super::super::pervasive::strictly_cloned(x.9, r.9)
            && super::super::pervasive::strictly_cloned(x.10, r.10)),
;

pub broadcast axiom fn axiom_strictly_cloned_tuple12<
    A: Clone,
    B: Clone,
    C: Clone,
    D: Clone,
    E: Clone,
    F: Clone,
    G: Clone,
    H: Clone,
    I: Clone,
    J: Clone,
    K: Clone,
    L: Clone,
>(x: (A, B, C, D, E, F, G, H, I, J, K, L), r: (A, B, C, D, E, F, G, H, I, J, K, L))
    ensures
        #[trigger] super::super::pervasive::strictly_cloned(x, r) <==> (
        super::super::pervasive::strictly_cloned(x.0, r.0)
            && super::super::pervasive::strictly_cloned(x.1, r.1)
            && super::super::pervasive::strictly_cloned(x.2, r.2)
            && super::super::pervasive::strictly_cloned(x.3, r.3)
            && super::super::pervasive::strictly_cloned(x.4, r.4)
            && super::super::pervasive::strictly_cloned(x.5, r.5)
            && super::super::pervasive::strictly_cloned(x.6, r.6)
            && super::super::pervasive::strictly_cloned(x.7, r.7)
            && super::super::pervasive::strictly_cloned(x.8, r.8)
            && super::super::pervasive::strictly_cloned(x.9, r.9)
            && super::super::pervasive::strictly_cloned(x.10, r.10)
            && super::super::pervasive::strictly_cloned(x.11, r.11)),
;

pub broadcast group group_clone_tuple_axioms {
    axiom_strictly_cloned_tuple1,
    axiom_strictly_cloned_tuple2,
    axiom_strictly_cloned_tuple3,
    axiom_strictly_cloned_tuple4,
    axiom_strictly_cloned_tuple5,
    axiom_strictly_cloned_tuple6,
    axiom_strictly_cloned_tuple7,
    axiom_strictly_cloned_tuple8,
    axiom_strictly_cloned_tuple9,
    axiom_strictly_cloned_tuple10,
    axiom_strictly_cloned_tuple11,
    axiom_strictly_cloned_tuple12,
}

} // verus!
