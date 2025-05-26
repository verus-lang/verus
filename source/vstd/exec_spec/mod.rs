#![cfg(feature = "alloc")]

use super::prelude::*;

verus! {

/// `ToRef` and `ToOwned` are almost the same trait
/// but separated to avoid type inference ambiguities
pub trait ToRef<T: Sized + DeepView>: Sized + DeepView<V = T::V> {
    fn get_ref(self) -> (res: T)
        ensures res.deep_view() == self.deep_view();
}

pub trait ToOwned<T: Sized + DeepView>: Sized + DeepView<V = T::V> {
    fn get_owned(self) -> (res: T)
        ensures res.deep_view() == self.deep_view();
}

/// Cloned object have the same deep view
pub trait DeepViewClone: Sized + DeepView {
    fn deep_clone(&self) -> (res: Self)
        ensures res.deep_view() == self.deep_view();
}

/// Any spec types used in exec_spec! macro
/// must implement this trait to indicate
/// the corresponding exec type (owned and borrowed versions)
pub trait ExecSpecType where
    for <'a> &'a Self::ExecOwnedType: ToRef<Self::ExecRefType<'a>>,
    for <'a> Self::ExecRefType<'a>: ToOwned<Self::ExecOwnedType>,
{
    /// Owned version of the exec type
    type ExecOwnedType: DeepView<V = Self>;

    /// Reference version of the exec type
    type ExecRefType<'a>: DeepView<V = Self>;
}

/// Spec for executable version of equality
pub trait ExecSpecEq<'a>: DeepView + Sized {
    type Other<'b>: DeepView<V = Self::V>;

    fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> (res: bool)
        ensures res == (this.deep_view() =~~= other.deep_view());
}

/// Spec for executable version of Seq::len
pub trait ExecSpecLen {
    fn exec_len(&self) -> usize;
}

/// Spec for executable version of Seq indexing
pub trait ExecSpecIndex<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;
    fn exec_index(self, index: usize) -> Self::Elem
        requires 0 <= index < self.deep_view().len();
}

/// Implement various traits for primitive arithmetic types
macro_rules! impl_primitives {
    ($(,)?) => {};
    ($t:ty $(,$rest:ty)* $(,)?) => {
        verus! {
            impl ExecSpecType for $t {
                type ExecOwnedType = $t;
                type ExecRefType<'a> = $t;
            }

            impl<'a> ToRef<$t> for &'a $t {
                #[inline(always)]
                fn get_ref(self) -> $t {
                    *self
                }
            }

            impl ToOwned<$t> for $t {
                #[inline(always)]
                fn get_owned(self) -> $t {
                    self
                }
            }

            impl DeepViewClone for $t {
                #[inline(always)]
                fn deep_clone(&self) -> Self {
                    *self
                }
            }

            impl<'a> ExecSpecEq<'a> for $t {
                type Other<'b> = $t;

                #[inline(always)]
                fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
                    this == other
                }
            }

            // For cases like comparing Seq<u32> and Seq<u32>
            impl<'a> ExecSpecEq<'a> for &'a $t {
                type Other<'b> = &'b $t;

                #[inline(always)]
                fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
                    this == other
                }
            }
        }

        impl_primitives!($($rest),*);
    };
}

impl_primitives! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
    bool, char,
}

/// Impls for Option<T>
impl<'a, T: Sized + DeepView> ToRef<&'a Option<T>> for &'a Option<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a Option<T> {
        self
    }
}

impl<'a, T: DeepView + DeepViewClone> ToOwned<Option<T>> for &'a Option<T> {
    #[inline(always)]
    fn get_owned(self) -> Option<T> {
        self.deep_clone()
    }
}

impl<T: DeepViewClone> DeepViewClone for Option<T> {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        match self {
            Some(t) => Some(t.deep_clone()),
            None => None,
        }
    }
}

/// TODO: currently not supported by verusfmt
impl<'a, T: DeepView> ExecSpecEq<'a> for &'a Option<T> where
    &'a T: for <'c> ExecSpecEq<'a, Other<'c> = &'c T>,
{
    type Other<'b> = &'a Option<T>;

    #[inline(always)]
    fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
        match (this, other) {
            (Some(t1), Some(t2)) => <&'a T>::exec_eq(t1, t2),
            (None, None) => true,
            _ => false,
        }
    }
}

/// Impls for pairs (a, b)
/// TODO: generalize to more tuple types
impl<'a, T1: Sized + DeepView, T2: Sized + DeepView> ToRef<&'a (T1, T2)> for &'a (T1, T2) {
    #[inline(always)]
    fn get_ref(self) -> &'a (T1, T2) {
        self
    }
}

impl<'a, T1: DeepView + DeepViewClone, T2: DeepView + DeepViewClone> ToOwned<(T1, T2)> for &'a (T1, T2) {
    #[inline(always)]
    fn get_owned(self) -> (T1, T2) {
        self.deep_clone()
    }
}

impl<T1: DeepViewClone, T2: DeepViewClone> DeepViewClone for (T1, T2) {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        (self.0.deep_clone(), self.1.deep_clone())
    }
}

impl<'a, T1: DeepView, T2: DeepView> ExecSpecEq<'a> for &'a (T1, T2) where
    &'a T1: for <'c> ExecSpecEq<'a, Other<'c> = &'c T1>,
    &'a T2: for <'c> ExecSpecEq<'a, Other<'c> = &'c T2>,
{
    type Other<'b> = &'a (T1, T2);

    #[inline(always)]
    fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
        <&T1>::exec_eq(&this.0, &other.0) && <&T2>::exec_eq(&this.1, &other.1)
    }
}

/// In order for Seq<char> to be compiled to String,
/// this special alias has to be used
pub type SpecString = Seq<char>;

impl ExecSpecType for SpecString {
    type ExecOwnedType = String;
    type ExecRefType<'a> = &'a str;
}

impl<'a> ToRef<&'a str> for &'a String {
    #[inline(always)]
    fn get_ref(self) -> &'a str {
        self.as_str()
    }
}

impl<'a> ToOwned<String> for &'a str {
    #[inline(always)]
    fn get_owned(self) -> String {
        self.to_string()
    }
}

impl DeepViewClone for String {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        self.clone()
    }
}

impl<'a> ExecSpecEq<'a> for &'a str {
    type Other<'b> = &'b str;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
        this == other
    }
}

/// Required for comparing, e.g., `Vec<String>`'s
impl<'a> ExecSpecEq<'a> for &'a String {
    type Other<'b> = &'b String;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
        this == other
    }
}

impl<'a> ExecSpecLen for &'a str {
    #[inline(always)]
    fn exec_len(&self) -> (res: usize)
        ensures res == self.deep_view().len()
    {
        self.unicode_len()
    }
}

impl<'a> ExecSpecIndex<'a> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_index(self, index: usize) -> (res: Self::Elem)
        ensures res == self.deep_view()[index as int]
    {
        self.get_char(index)
    }
}

/// NOTE: can't implement ExecSpecType for Seq<T>
/// since it conflicts with SpecString = Seq<char>
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

impl<'a, T: DeepView> ExecSpecEq<'a> for &'a [T] where
    &'a T: for <'c> ExecSpecEq<'a, Other<'c> = &'c T>,
{
    type Other<'b> = &'a [T];

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
        this.len() == other.len() &&
        this.iter().zip(other.iter()).all(|(a, b)| <&'a T>::exec_eq(a, b))
    }
}

impl<'a, T: DeepView> ExecSpecEq<'a> for &'a Vec<T> where
    &'a T: for <'c> ExecSpecEq<'a, Other<'c> = &'c T>,
{
    type Other<'b> = &'a Vec<T>;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq<'b>(this: Self, other: Self::Other<'b>) -> bool {
        this.len() == other.len() &&
        this.iter().zip(other.iter()).all(|(a, b)| <&'a T>::exec_eq(a, b))
    }
}

impl<'a, T: DeepView> ExecSpecLen for &'a [T] {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_len(&self) -> (res: usize)
        ensures res == self.deep_view().len()
    {
        self.len()
    }
}

impl<'a, T: DeepView> ExecSpecIndex<'a> for &'a [T] {
    type Elem = &'a T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_index(self, index: usize) -> (res: Self::Elem)
        ensures res.deep_view() == self.deep_view()[index as int]
    {
        self.get(index).unwrap()
    }
}

}
