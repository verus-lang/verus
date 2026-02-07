//! This module contains [`Seq`]-specific method implementations.
use crate::contrib::exec_spec::*;
use crate::prelude::*;

verus! {

// Note: the exec translations which use iterators are unverified.
broadcast use crate::group_vstd_default;

/// Impls for shared traits
/// NOTE: can't implement [`ExecSpecType`] for [`Seq<T>`]
/// since it conflicts with [`SpecString`] (i.e., [`Seq<char>`]).
impl<'a, T: DeepView> ToRef<&'a [T]> for &'a Vec<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a [T] {
        self.as_slice()
    }
}

impl<'a, T: DeepView + DeepViewClone> ToOwned<Vec<T>> for &'a [T] {
    /// TODO: verify this
    #[verifier::external_body]
    #[inline(always)]
    fn get_owned(self) -> Vec<T> {
        self.iter().map(|x| x.deep_clone()).collect()
    }
}

impl<T: DeepViewClone> DeepViewClone for Vec<T> {
    /// TODO: verify this
    #[verifier::external_body]
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        self.iter().map(|x| x.deep_clone()).collect()
    }
}

impl<'a, T: DeepView> ExecSpecEq<'a> for &'a [T] where &'a T: ExecSpecEq<'a, Other = &'a T> {
    type Other = &'a [T];

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this.len() == other.len() && this.iter().zip(other.iter()).all(
            |(a, b)| <&'a T>::exec_eq(a, b),
        )
    }
}

impl<'a, T: DeepView> ExecSpecEq<'a> for &'a Vec<T> where &'a T: ExecSpecEq<'a, Other = &'a T> {
    type Other = &'a Vec<T>;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this.len() == other.len() && this.iter().zip(other.iter()).all(
            |(a, b)| <&'a T>::exec_eq(a, b),
        )
    }
}

impl<'a, T: DeepView> ExecSpecLen for &'a [T] {
    #[inline(always)]
    fn exec_len(self) -> (res: usize)
        ensures
            res == self.deep_view().len(),
    {
        self.len()
    }
}

impl<'a, T: DeepView> ExecSpecIndex<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_index(self, index: usize) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view()[index as int],
    {
        self.get(index).unwrap()
    }
}

//
// Trait definitions for methods
//
/// Spec for executable version of [`Seq::add`].
pub trait ExecSpecSeqAdd<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    fn exec_add(self, rhs: Self) -> Out;
}

/// Spec for executable version of [`Seq::push`].
pub trait ExecSpecSeqPush<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Elem: DeepView + DeepViewClone;

    fn exec_push(self, a: Self::Elem) -> Out;
}

/// Spec for executable version of [`Seq::update`].
pub trait ExecSpecSeqUpdate<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Elem: DeepView + DeepViewClone;

    fn exec_update(self, i: usize, a: Self::Elem) -> Out;
}

/// Spec for executable version of [`Seq::subrange`].
pub trait ExecSpecSeqSubrange<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_subrange(self, start_inclusive: usize, end_exclusive: usize) -> Self
        requires
            0 <= start_inclusive <= end_exclusive <= self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::empty`].
pub trait ExecSpecSeqEmpty: Sized {
    fn exec_empty() -> Self;
}

/// Spec for executable version of [`Seq::to_multiset`].
pub trait ExecSpecSeqToMultiset<'a>: Sized {
    type Elem: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq;

    fn exec_to_multiset(self) -> ExecMultiset<Self::Elem>;
}

// todo(nneamtu):
// The implementations here for interp Seq methods (e.g. take) could be streamlined.
// Currently, I am coping the spec definition and translating it to the exec version by hand.
// This is because the exec_spec! macro does not support methods right now (it only supports functions).
// A more concise approach would be to apply the exec_spec! macro directly to the spec fns on Seq.
/// Spec for executable version of [`Seq::drop_first`].
pub trait ExecSpecSeqDropFirst<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_drop_first(self) -> Self
        requires
            self.deep_view().len() >= 1,
    ;
}

/// Spec for executable version of [`Seq::drop_last`].
pub trait ExecSpecSeqDropLast<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_drop_last(self) -> Self
        requires
            self.deep_view().len() >= 1,
    ;
}

/// Spec for executable version of [`Seq::take`].
pub trait ExecSpecSeqTake<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_take(self, n: usize) -> Self
        requires
            0 <= n <= self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::skip`].
pub trait ExecSpecSeqSkip<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_skip(self, n: usize) -> Self
        requires
            0 <= n <= self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::last`].
pub trait ExecSpecSeqLast<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_last(self) -> Self::Elem
        requires
            0 < self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::last`].
pub trait ExecSpecSeqFirst<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_first(self) -> Self::Elem
        requires
            0 < self.deep_view().len(),
    ;
}

/// Spec for executable version of [`Seq::is_prefix_of`].
pub trait ExecSpecSeqIsPrefixOf<'a>: DeepView + Sized {
    type Other: DeepView<V = Self::V>;

    fn exec_is_prefix_of(self, other: Self::Other) -> (res: bool);
}

/// Spec for executable version of [`Seq::is_suffix_of`].
pub trait ExecSpecSeqIsSuffixOf<'a>: DeepView + Sized {
    type Other: DeepView<V = Self::V>;

    fn exec_is_suffix_of(self, other: Self::Other) -> (res: bool);
}

/// Spec for executable version of [`Seq::contains`].
pub trait ExecSpecSeqContains<'a>: Sized + DeepView {
    type Elem: DeepView;

    fn exec_contains(self, needle: Self::Elem) -> bool;
}

/// Spec for executable version of [`Seq::index_of`].
pub trait ExecSpecSeqIndexOf<'a>: Sized + DeepView {
    type Elem: DeepView;

    fn exec_index_of(self, needle: Self::Elem) -> usize;
}

/// Spec for executable version of [`Seq::index_of_first`].
pub trait ExecSpecSeqIndexOfFirst<'a>: Sized + DeepView {
    type Elem: DeepView;

    fn exec_index_of_first(self, needle: Self::Elem) -> Option<usize>;
}

/// Spec for executable version of [`Seq::index_of_last`].
pub trait ExecSpecSeqIndexOfLast<'a>: Sized + DeepView {
    type Elem: DeepView;

    fn exec_index_of_last(self, needle: Self::Elem) -> Option<usize>;
}

//
// Implementations for Vec and slices
//
impl<'a, T: DeepView + DeepViewClone> ExecSpecSeqAdd<'a, Vec<T>> for &'a [T] {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_add(self, rhs: Self) -> (res: Vec<T>)
        ensures
            res.deep_view() =~= self.deep_view().add(rhs.deep_view()),
    {
        self.get_owned().into_iter().chain(rhs.get_owned()).collect()
    }
}

impl<'a, T: DeepView + DeepViewClone> ExecSpecSeqPush<'a, Vec<T>> for &'a [T] {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_push(self, a: Self::Elem) -> (res: Vec<T>)
        ensures
            res.deep_view() =~= self.deep_view().push(a.deep_view()),
    {
        let v = vec![a];
        self.get_owned().into_iter().chain(v).collect()
    }
}

impl<'a, T: DeepView + DeepViewClone> ExecSpecSeqUpdate<'a, Vec<T>> for &'a [T] {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_update(self, i: usize, a: Self::Elem) -> (res: Vec<T>)
        ensures
            res.deep_view() =~= self.deep_view().update(i as int, a.deep_view()),
    {
        let mut v: Vec<T> = self.get_owned();
        v[i] = a.deep_clone();
        v
    }
}

impl<'a, T: DeepView> ExecSpecSeqSubrange<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_subrange(self, start_inclusive: usize, end_exclusive: usize) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().subrange(
                start_inclusive as int,
                end_exclusive as int,
            ),
    {
        &self[start_inclusive..end_exclusive]
    }
}

impl<T: DeepView> ExecSpecSeqEmpty for Vec<T> {
    #[inline(always)]
    fn exec_empty() -> (res: Self)
        ensures
            res.deep_view() =~= Seq::empty(),
    {
        Vec::new()
    }
}

impl<'a, T: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ExecSpecSeqToMultiset<
    'a,
> for &'a [T] {
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
                },
            }
        }
        mset
    }
}

impl<'a, T: DeepView> ExecSpecSeqDropFirst<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_drop_first(self) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().drop_first(),
    {
        self.exec_subrange(1, self.exec_len())
    }
}

impl<'a, T: DeepView> ExecSpecSeqDropLast<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_drop_last(self) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().drop_last(),
    {
        self.exec_subrange(0, self.exec_len() - 1)
    }
}

impl<'a, T: DeepView> ExecSpecSeqTake<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_take(self, n: usize) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().take(n as int),
    {
        self.exec_subrange(0, n)
    }
}

impl<'a, T: DeepView> ExecSpecSeqSkip<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_skip(self, n: usize) -> (res: Self)
        ensures
            res.deep_view() =~= self.deep_view().skip(n as int),
    {
        self.exec_subrange(n, self.exec_len())
    }
}

impl<'a, T: DeepView> ExecSpecSeqLast<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_last(self) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view().last(),
    {
        &self.exec_index(self.len() - 1)
    }
}

impl<'a, T: DeepView> ExecSpecSeqFirst<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_first(self) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view().first(),
    {
        &self.exec_index(0)
    }
}

impl<'a, T: DeepView> ExecSpecSeqIsPrefixOf<'a> for &'a [T] where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
    &'a [T]: DeepView<V = Seq<<&'a T as DeepView>::V>>,
 {
    type Other = &'a [T];

    #[verifier::external_body]
    #[inline(always)]
    fn exec_is_prefix_of(self, other: Self::Other) -> (res: bool)
        ensures
            res == self.deep_view().is_prefix_of(other.deep_view()),
    {
        self.exec_len() <= other.exec_len() && (<&[T]>::exec_eq(
            self,
            other.exec_subrange(0, self.exec_len()),
        ))
    }
}

impl<'a, T: DeepView> ExecSpecSeqIsSuffixOf<'a> for &'a [T] where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
    &'a [T]: DeepView<V = Seq<<&'a T as DeepView>::V>>,
 {
    type Other = &'a [T];

    #[inline(always)]
    fn exec_is_suffix_of(self, other: Self::Other) -> (res: bool)
        ensures
            res == self.deep_view().is_suffix_of(other.deep_view()),
    {
        self.exec_len() <= other.exec_len() && (<&[T]>::exec_eq(
            self,
            other.exec_subrange(other.exec_len() - self.exec_len(), other.exec_len()),
        ))
    }
}

impl<'a, T: DeepView + PartialEq> ExecSpecSeqContains<'a> for &'a [T] where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
 {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_contains(self, needle: Self::Elem) -> (res: bool)
        ensures
            res == self.deep_view().contains(needle.deep_view()),
    {
        // todo(nneamtu): should this use <&T>::exec_eq to do the equality check instead?
        self.contains(&needle)
    }
}

impl<'a, T: DeepView + PartialEq> ExecSpecSeqIndexOf<'a> for &'a [T] where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
 {
    type Elem = T;

    // hard to verify - index_of contains a choose operator
    #[verifier::external_body]
    #[inline(always)]
    fn exec_index_of(self, needle: Self::Elem) -> (res: usize)
        ensures
            0 <= res < self.len() ==> res as int == self.deep_view().index_of(needle.deep_view()),
    {
        // todo(nneamtu): should this use <&T>::exec_eq to do the equality check instead?
        // hard to convert to correct type for argument, e.g. if Self::Elem is Vec
        for i in 0..self.exec_len() {
            if self[i] == needle {
                return i;
            }
        }
        self.exec_len()
    }
}

impl<'a, T: DeepView + PartialEq> ExecSpecSeqIndexOfFirst<'a> for &'a [T] where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
 {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_index_of_first(self, needle: Self::Elem) -> (res: Option<usize>)
        ensures
            match res {
                Some(i) => i as int == self.deep_view().index_of_first(needle.deep_view())->0,
                None => self.deep_view().index_of_first(needle.deep_view()) == None::<int>,
            },
    {
        // todo(nneamtu): should this use <&T>::exec_eq to do the equality check instead?
        for i in 0..self.exec_len() {
            if self[i] == needle {
                return Some(i);
            }
        }
        None
    }
}

impl<'a, T: DeepView + PartialEq> ExecSpecSeqIndexOfLast<'a> for &'a [T] where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
 {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_index_of_last(self, needle: Self::Elem) -> (res: Option<usize>)
        ensures
            match res {
                Some(i) => i as int == self.deep_view().index_of_last(needle.deep_view())->0,
                None => self.deep_view().index_of_last(needle.deep_view()) == None::<int>,
            },
    {
        // todo(nneamtu): should this use <&T>::exec_eq to do the equality check instead?
        for i in (0..self.exec_len()).rev() {
            if self[i] == needle {
                return Some(i);
            }
        }
        None
    }
}

} // verus!
