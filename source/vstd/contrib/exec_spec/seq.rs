//! This module contains [`Seq`]-specific method implementations.

use crate::prelude::*;
use crate::contrib::exec_spec::*;

verus! {

//
// Trait definitions for methods
//

/// Spec for executable version of [`Seq::drop_first`].
pub trait ExecSpecDropFirst<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_drop_first(self) -> Self
        requires
            self.deep_view().len() >= 1
    ;
}

/// Spec for executable version of [`Seq::drop_last`].
pub trait ExecSpecDropLast<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_drop_last(self) -> Self
        requires
            self.deep_view().len() >= 1
    ;
}

/// Spec for executable version of [`Seq::add`].
pub trait ExecSpecAdd<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    fn exec_add(self, rhs: Self) -> Out;
}

/// Spec for executable version of [`Seq::push`].
pub trait ExecSpecPush<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Elem: DeepView + DeepViewClone;

    fn exec_push(self, a: Self::Elem) -> Out;
}

/// Spec for executable version of [`Seq::update`].
pub trait ExecSpecUpdate<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Elem: DeepView + DeepViewClone;

    fn exec_update(self, i: usize, a: Self::Elem) -> Out;
}

/// Spec for executable version of [`Seq::subrange`].
pub trait ExecSpecSubrange<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_subrange(self, start_inclusive: usize, end_exclusive: usize) -> Self
        requires
            0 <= start_inclusive <= end_exclusive <= self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::empty`].
pub trait ExecSpecEmpty: Sized {
    fn exec_empty() -> Self;
}

/// Spec for executable version of [`Seq::new`].
pub trait ExecSpecNew: Sized {
    type Elem: DeepView;

    fn exec_new<F: Fn(usize) -> Self::Elem + 'static>(len: usize, f: F) -> Self;
}

/// Spec for executable version of [`Seq::to_multiset`].
pub trait ExecSpecToMultiset<'a>: Sized {
    type Elem: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq;

    fn exec_to_multiset(self) -> ExecMultiset<Self::Elem>;
}

// todo(nneamtu):
// The implementations here for interp Seq methods (e.g. take) could be streamlined.
// Currently, I am coping the spec definition and translating it to the exec version by hand.
// This is because the exec_spec! macro does not support methods right now (it only supports functions).
// A more concise approach would be to apply the exec_spec! macro directly to the spec fns on Seq.

/// Spec for executable version of [`Seq::take`].
pub trait ExecSpecTake<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_take(self, n: usize) -> Self
        requires
            0 <= n <= self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::skip`].
pub trait ExecSpecSkip<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_skip(self, n: usize) -> Self
        requires
            0 <= n <= self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::last`].
pub trait ExecSpecLast<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_last(self) -> Self::Elem
        requires
            0 < self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::last`].
pub trait ExecSpecFirst<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_first(self) -> Self::Elem
        requires
            0 < self.deep_view().len(),
    ;
}

//
// Implementations for Vec and slices
//

impl<'a, T: DeepView> ExecSpecDropFirst<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_drop_first(self) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().drop_first(),
    {
        &self[1..]
    }
}

impl<'a, T: DeepView> ExecSpecDropLast<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_drop_last(self) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().drop_last(),
    {
        &self[..self.len()-1]
    }
}

impl<'a, T: DeepView + DeepViewClone> ExecSpecAdd<'a, Vec<T>> for &'a [T] {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_add(self, rhs: Self) -> (res: Vec<T>)
        ensures
            res.deep_view() =~= self.deep_view().add(rhs.deep_view()),
    {
        self.iter().map(|x| x.deep_clone()).chain(rhs.iter().map(|x| x.deep_clone())).collect()
    }
}

impl<'a, T: DeepView + DeepViewClone> ExecSpecPush<'a, Vec<T>> for &'a [T] {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_push(self, a: Self::Elem) -> (res: Vec<T>)
        ensures
            res.deep_view() =~= self.deep_view().push(a.deep_view()),
    {
        let v = vec![a];
        self.iter().map(|x| x.deep_clone()).chain(v.iter().map(|x| x.deep_clone())).collect()
    }
}

impl<'a, T: DeepView + DeepViewClone> ExecSpecUpdate<'a, Vec<T>> for &'a [T] {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_update(self, i: usize, a: Self::Elem) -> (res: Vec<T>)
        ensures
            res.deep_view() =~= self.deep_view().update(i as int, a.deep_view()),
    {
        let mut v: Vec<T> = self.iter().map(|x| x.deep_clone()).collect();
        v[i] = a.deep_clone();
        v
    }
}

impl<'a, T: DeepView> ExecSpecSubrange<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_subrange(self, start_inclusive: usize, end_exclusive: usize) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().subrange(start_inclusive as int, end_exclusive as int),
    {
        &self[start_inclusive..end_exclusive]
    }
}

impl<T: DeepView> ExecSpecEmpty for Vec<T> {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_empty() -> (res: Self)
        ensures
            res.deep_view() =~= Seq::empty(),
    {
        Vec::new()
    }
}

// todo(nneamtu):
// The support for `Seq::new` is quite incomplete and hacky.
// 1) We don't currently convert the type of the closure `f`. This is problematic because `Seq::new` expects `F: SpecFn(int) -> T`, 
// but `exec_new` expects `F: Fn(usize) -> T`. 
// The current workaround is just to leave off type annotations for the argument in `f`, as in `|i| i as usize`.
// 2) The postcondition on `exec_new` is trivial. Verus complains when trying to use the non-spec function `f` in the postcondition.
impl<T: DeepView> ExecSpecNew for Vec<T> {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_new<F: Fn(usize) -> Self::Elem + 'static>(len: usize, f: F) -> (res: Self)
        ensures
            true
            //res.deep_view() =~= Seq::new(len as nat, |i| f(i as usize).deep_view()),
    {
        (0..len).map(|i| f(i)).collect()
    }
}

impl<'a, T: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ExecSpecToMultiset<'a> for &'a [T] {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_to_multiset(self) -> (res: ExecMultiset<Self::Elem>)
        ensures
            res.deep_view() =~= self.deep_view().to_multiset(),
    {
        let mut mset = ExecMultiset { m: HashMap::new() };
        for e in self.iter() {
            match mset.m.remove_entry(e) {
                Some((k, c)) => {
                    mset.m.insert(k, c + 1);
                },
                None => {
                    mset.m.insert(e.deep_clone(), 1);
                }
            }
        }
        mset
    }
}

impl<'a, T: DeepView> ExecSpecTake<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_take(self, n: usize) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().take(n as int),
    {
        self.exec_subrange(0, n)
    }
}

impl<'a, T: DeepView> ExecSpecSkip<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_skip(self, n: usize) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().skip(n as int),
    {
        self.exec_subrange(n, self.exec_len())
    }
}

impl<'a, T: DeepView> ExecSpecLast<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_last(self) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view().last(),
    {
        &self[self.len() - 1]
    }
}

impl<'a, T: DeepView> ExecSpecFirst<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_first(self) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view().first(),
    {
        &self[0]
    }
}

}