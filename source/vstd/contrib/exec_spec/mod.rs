//! This module provides runtime utilities for the compiled
//! executable code of [`verus_builtin_macros::exec_spec_verified`]
//! and [`verus_builtin_macros::exec_spec_unverified`].
#![cfg(all(feature = "alloc", feature = "std"))]

use crate::multiset::*;
use crate::prelude::*;
use std::collections::HashMap;
use std::collections::HashSet;
pub use verus_builtin_macros::exec_spec_unverified;
pub use verus_builtin_macros::exec_spec_verified;

mod map;
pub use map::*;
mod multiset;
pub use multiset::*;
mod option;
pub use option::*;
mod seq;
pub use seq::*;
mod set;
pub use set::*;
mod string;
pub use string::*;

verus! {

/// [`ToRef`] and [`ToOwned`] are almost the same trait
/// but separated to avoid type inference ambiguities.
pub trait ToRef<T: Sized + DeepView>: Sized + DeepView<V = T::V> {
    fn get_ref(self) -> (res: T)
        ensures
            res.deep_view() == self.deep_view(),
    ;
}

pub trait ToOwned<T: Sized + DeepView>: Sized + DeepView<V = T::V> {
    fn get_owned(self) -> (res: T)
        ensures
            res.deep_view() == self.deep_view(),
    ;
}

/// Cloned objects have the same deep view
pub trait DeepViewClone: Sized + DeepView {
    fn deep_clone(&self) -> (res: Self)
        ensures
            res.deep_view() == self.deep_view(),
    ;
}

/// Any spec types used in [`exec_spec_verified`] or [`exec_spec_unverified`] macros
/// must implement this trait to indicate
/// the corresponding exec type (owned and borrowed versions).
pub trait ExecSpecType where
    for <'a>&'a Self::ExecOwnedType: ToRef<Self::ExecRefType<'a>>,
    for <'a>Self::ExecRefType<'a>: ToOwned<Self::ExecOwnedType>,
 {
    /// Owned version of the exec type.
    type ExecOwnedType: DeepView<V = Self>;

    /// Reference version of the exec type.
    type ExecRefType<'a>: DeepView<V = Self>;
}

/// Spec for the executable version of equality.
pub trait ExecSpecEq<'a>: DeepView + Sized {
    type Other: DeepView<V = Self::V>;

    fn exec_eq(this: Self, other: Self::Other) -> (res: bool)
        ensures
            res == (this.deep_view() =~~= other.deep_view()),
    ;
}

/// Spec for executable version of [`Seq`] and [`str`] indexing.
pub trait ExecSpecIndex<'a>: Sized + DeepView<V = Seq<<Self::Elem as DeepView>::V>> {
    type Elem: DeepView;

    fn exec_index(self, index: usize) -> Self::Elem
        requires
            0 <= index < self.deep_view().len(),
    ;
}

/// Spec for executable version of `len`.
pub trait ExecSpecLen {
    fn exec_len(self) -> usize;
}

/// A macro to implement various traits for primitive arithmetic types.
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
                type Other = $t;

                #[inline(always)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
                    this == other
                }
            }

            // For cases like comparing Seq<u32> and Seq<u32>
            impl<'a> ExecSpecEq<'a> for &'a $t {
                type Other = &'a $t;

                #[inline(always)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
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
// impl on tuples up to size 4, to match the impls of View in vstd


macro_rules! impl_exec_spec_tuple {
    ([$(
        ($T:ident, $n:tt)
    ),*])=> {
        verus! {

            impl<'a, $($T: Sized + DeepView),*> ToRef<&'a ($($T,)*)> for &'a ($($T,)*) {
                #[inline(always)]
                fn get_ref(self) -> &'a ($($T,)*) {
                    self
                }
            }

            impl<'a, $($T: DeepView + DeepViewClone),*> ToOwned<($($T,)*)> for &'a ($($T,)*) {
                #[inline(always)]
                fn get_owned(self) -> ($($T,)*) {
                    self.deep_clone()
                }
            }

            impl<$($T: DeepViewClone),*> DeepViewClone for ($($T,)*) {
                #[inline(always)]
                #[allow(non_snake_case)]
                fn deep_clone(&self) -> Self {
                    ($(self.$n.deep_clone(),)*)
                }
            }

            impl<'a, $($T: DeepView),*> ExecSpecEq<'a> for &'a ($($T,)*)
            where
                $( &'a $T: ExecSpecEq<'a, Other = &'a $T>, )*
            {
                type Other = &'a ($($T,)*);

                #[inline(always)]
                #[allow(non_snake_case)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
                    $( <&$T>::exec_eq(&this.$n, &other.$n) )&&*
                }
            }

        }
    };
}

impl_exec_spec_tuple!([(T0, 0)]);

impl_exec_spec_tuple!([(T0, 0), (T1, 1)]);

impl_exec_spec_tuple!([(T0, 0), (T1, 1), (T2, 2)]);

impl_exec_spec_tuple!([(T0, 0), (T1, 1), (T2, 2), (T3, 3)]);

} // verus!
