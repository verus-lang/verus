#![allow(unused_imports)]
use crate::seq::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub trait ArrayAdditionalSpecFns<T> {
    spec fn view(&self) -> Seq<T>;

    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

#[verifier::external]
pub trait ArrayAdditionalExecFns<T> {
    fn set(&mut self, idx: usize, t: T);
}

impl<T, const N: usize> ArrayAdditionalSpecFns<T> for [T; N] {
    spec fn view(&self) -> Seq<T>;

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

impl<T, const N: usize> ArrayAdditionalExecFns<T> for [T; N] {
    #[verifier::external_body]
    fn set(&mut self, idx: usize, t: T)
        requires
            0 <= idx < N,
        ensures
            self@ == old(self)@.update(idx as int, t),
    {
        self[idx] = t;
    }
}

#[verifier(external_body)]
pub exec fn array_index_get<T, const N: usize>(ar: &[T; N], i: usize) -> (out: &T)
    requires
        0 <= i < N,
    ensures
        *out == ar@.index(i as int),
{
    &ar[i]
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn array_len_matches_n<T, const N: usize>(ar: &[T; N])
    ensures
        (#[trigger] ar@.len()) == N,
{
}

// Referenced by Verus' internal encoding for array literals
#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "vstd::array::array_index")]
pub open spec fn array_index<T, const N: usize>(ar: &[T; N], i: int) -> T {
    ar.view().index(i)
}

} // verus!
