#![allow(unused_imports)]

use core::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI8, AtomicIsize, AtomicPtr, AtomicU16, AtomicU32,
    AtomicU8, AtomicUsize, Ordering,
};

#[cfg(target_has_atomic = "64")]
use core::sync::atomic::{AtomicI64, AtomicU64};

use super::modes::*;
use super::pervasive::*;
use super::prelude::*;
use super::view::*;

macro_rules! make_unsigned_integer_atomic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
        // TODO we could support `std::intrinsics::wrapping_add`
        // and use that instead.

        verus! {

        pub open spec fn $wrap_add(a: int, b: int) -> int {
            if a + b > (<$value_ty>::MAX as int) {
                a + b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a + b
            }
        }

        pub open spec fn $wrap_sub(a: int, b: int) -> int {
            if a - b < (<$value_ty>::MIN as int) {
                a - b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a - b
            }
        }

        } // verus!
        atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty, []);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub);
        }
    };
}

macro_rules! make_signed_integer_atomic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
        verus! {

        pub open spec fn $wrap_add(a: int, b: int) -> int {
            if a + b > (<$value_ty>::MAX as int) {
                a + b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else if a + b < (<$value_ty>::MIN as int) {
                a + b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a + b
            }
        }

        pub open spec fn $wrap_sub(a: int, b: int) -> int {
            if a - b > (<$value_ty>::MAX as int) {
                a - b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else if a - b < (<$value_ty>::MIN as int) {
                a - b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a - b
            }
        }

        } // verus!
        atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty, []);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub);
        }
    };
}

macro_rules! make_bool_atomic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty, []);
            atomic_bool_methods!($at_ident, $p_ident, $rust_ty, $value_ty);
        }
    };
}

macro_rules! atomic_types {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        verus! {

        #[verifier::external_body] /* vattr */
        pub struct $at_ident {
            ato: $rust_ty,
        }

        #[verifier::external_body] /* vattr */
        pub tracked struct $p_ident {
            no_copy: NoCopy,
            unused: $value_ty,
        }

        pub ghost struct $p_data_ident {
            pub patomic: int,
            pub value: $value_ty,
        }

        impl $p_ident {
            #[verifier::external_body] /* vattr */
            pub uninterp spec fn view(self) -> $p_data_ident;

            #[doc(hidden)]
            #[verifier::external_body] /* vattr */
            pub uninterp spec fn view_inverse_for_eq(data: $p_data_ident) -> Self;

            pub open spec fn is_for(&self, patomic: $at_ident) -> bool {
                self.view().patomic == patomic.id()
            }

            pub open spec fn points_to(&self, v: $value_ty) -> bool {
                self.view().value == v
            }

            #[verifier::inline]
            pub open spec fn value(&self) -> $value_ty {
                self.view().value
            }

            #[verifier::inline]
            pub open spec fn id(&self) -> AtomicCellId {
                self.view().patomic
            }

            /// Implies that `a@ == b@ ==> a == b`.
            pub broadcast axiom fn view_bijective(self)
                ensures
                    Self::view_inverse_for_eq(#[trigger] self@) == self,
            ;
        }

        }
    };
}

macro_rules! atomic_types_generic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        verus! {

        #[verifier::accept_recursive_types(T)]
        #[verifier::external_body] /* vattr */
        pub struct $at_ident <T> {
            ato: $rust_ty,
        }

        #[verifier::accept_recursive_types(T)]
        #[verifier::external_body] /* vattr */
        pub tracked struct $p_ident <T> {
            no_copy: NoCopy,
            unusued: $value_ty,
        }

        #[verifier::accept_recursive_types(T)]
        pub ghost struct $p_data_ident <T> {
            pub patomic: int,
            pub value: $value_ty,
        }

        impl<T> $p_ident <T> {
            #[verifier::external_body] /* vattr */
            pub uninterp spec fn view(self) -> $p_data_ident <T>;

            pub open spec fn is_for(&self, patomic: $at_ident <T>) -> bool {
                self.view().patomic == patomic.id()
            }

            pub open spec fn points_to(&self, v: $value_ty) -> bool {
                self.view().value == v
            }

            #[verifier::inline]
            pub open spec fn value(&self) -> $value_ty {
                self.view().value
            }

            #[verifier::inline]
            pub open spec fn id(&self) -> AtomicCellId {
                self.view().patomic
            }
        }

        }
    };
}

pub type AtomicCellId = int;

macro_rules! atomic_common_methods {
    ($at_ident: ty, $p_ident: ty, $p_data_ident: ty, $rust_ty: ty, $value_ty: ty, [ $($addr:tt)* ]) => {
        verus_impl!{

        pub uninterp spec fn id(&self) -> int;

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        pub const fn new(i: $value_ty) -> (res: ($at_ident, Tracked<$p_ident>))
            ensures
                equal(res.1@.view(), $p_data_ident{ patomic: res.0.id(), value: i }),
        {
            let p = $at_ident { ato: <$rust_ty>::new(i) };
            (p, Tracked::assume_new())
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn load(&self, Tracked(perm): Tracked<&$p_ident>) -> (ret: $value_ty)
            requires
                equal(self.id(), perm.view().patomic),
            ensures equal(perm.view().value, ret),
            opens_invariants none
            no_unwind
        {
            return self.ato.load(Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn store(&self, Tracked(perm): Tracked<&mut $p_ident>, v: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures equal(perm.view().value, v) && equal(self.id(), perm.view().patomic),
            opens_invariants none
            no_unwind
        {
            self.ato.store(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn compare_exchange(&self, Tracked(perm): Tracked<&mut $p_ident>, current: $value_ty, new: $value_ty) -> (ret: Result<$value_ty, $value_ty>)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(self.id(), perm.view().patomic)
                && match ret {
                    Result::Ok(r) =>
                           current $($addr)* == old(perm).view().value $($addr)*
                        && equal(perm.view().value, new)
                        && equal(r, old(perm).view().value),
                    Result::Err(r) =>
                           current $($addr)* != old(perm).view().value $($addr)*
                        && equal(perm.view().value, old(perm).view().value)
                        && equal(r, old(perm).view().value),
                },
            opens_invariants none
            no_unwind
        {
            match self.ato.compare_exchange(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn compare_exchange_weak(&self, Tracked(perm): Tracked<&mut $p_ident>, current: $value_ty, new: $value_ty) -> (ret: Result<$value_ty, $value_ty>)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(self.id(), perm.view().patomic)
                && match ret {
                    Result::Ok(r) =>
                           current $($addr)* == old(perm).view().value $($addr)*
                        && equal(perm.view().value, new)
                        && equal(r, old(perm).view().value),
                    Result::Err(r) =>
                           equal(perm.view().value, old(perm).view().value)
                        && equal(r, old(perm).view().value),
                },
            opens_invariants none
            no_unwind
        {
            match self.ato.compare_exchange_weak(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn swap(&self, Tracked(perm): Tracked<&mut $p_ident>, v: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                   equal(perm.view().value, v)
                && equal(old(perm).view().value, ret)
                && equal(self.id(), perm.view().patomic),
            opens_invariants none
            no_unwind
        {
            return self.ato.swap(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        pub fn into_inner(self, Tracked(perm): Tracked<$p_ident>) -> (ret: $value_ty)
            requires
                equal(self.id(), perm.view().patomic),
            ensures equal(perm.view().value, ret),
            opens_invariants none
            no_unwind
        {
            return self.ato.into_inner();
        }

        }
    };
}

macro_rules! atomic_integer_methods {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
        verus_impl!{

        // Note that wrapping-on-overflow is the defined behavior for fetch_add and fetch_sub
        // for Rust's atomics (in contrast to ordinary arithmetic)

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_add_wrapping(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value as int == $wrap_add(old(perm).view().value as int, n as int),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_add(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_sub_wrapping(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value as int == $wrap_sub(old(perm).view().value as int, n as int),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_sub(n, Ordering::SeqCst);
        }

        // fetch_add and fetch_sub are more natural in the common case that you
        // don't expect wrapping

        #[inline(always)]
        #[verifier::atomic] /* vattr */
        pub fn fetch_add(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
                (<$value_ty>::MIN as int) <= old(perm).view().value + n,
                old(perm).view().value + n <= (<$value_ty>::MAX as int),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == old(perm).view().value + n,
            opens_invariants none
            no_unwind
        {
            self.fetch_add_wrapping(Tracked(&mut *perm), n)
        }

        #[inline(always)]
        #[verifier::atomic] /* vattr */
        pub fn fetch_sub(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
                (<$value_ty>::MIN as int) <= old(perm).view().value - n,
                old(perm).view().value - n <= <$value_ty>::MAX as int,
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == old(perm).view().value - n,
            opens_invariants none
            no_unwind
        {
            self.fetch_sub_wrapping(Tracked(&mut *perm), n)
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_and(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value & n),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_or(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value | n),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_xor(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value ^ n),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_xor(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_nand(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == !(old(perm).view().value & n),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_max(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (if old(perm).view().value > n { old(perm).view().value } else { n }),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_max(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_min(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (if old(perm).view().value < n { old(perm).view().value } else { n }),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_min(n, Ordering::SeqCst);
        }

        }
    };
}

macro_rules! atomic_bool_methods {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        verus!{

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_and(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                   equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == (old(perm).view().value && n),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_or(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                  equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == (old(perm).view().value || n),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_xor(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == ((old(perm).view().value && !n) || (!old(perm).view().value && n)),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_xor(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_nand(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == !(old(perm).view().value && n),
            opens_invariants none
            no_unwind
        {
            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }

        }
    };
}

make_bool_atomic!(PAtomicBool, PermissionBool, PermissionDataBool, AtomicBool, bool);

make_unsigned_integer_atomic!(
    PAtomicU8,
    PermissionU8,
    PermissionDataU8,
    AtomicU8,
    u8,
    wrapping_add_u8,
    wrapping_sub_u8
);
make_unsigned_integer_atomic!(
    PAtomicU16,
    PermissionU16,
    PermissionDataU16,
    AtomicU16,
    u16,
    wrapping_add_u16,
    wrapping_sub_u16
);
make_unsigned_integer_atomic!(
    PAtomicU32,
    PermissionU32,
    PermissionDataU32,
    AtomicU32,
    u32,
    wrapping_add_u32,
    wrapping_sub_u32
);

#[cfg(target_has_atomic = "64")]
make_unsigned_integer_atomic!(
    PAtomicU64,
    PermissionU64,
    PermissionDataU64,
    AtomicU64,
    u64,
    wrapping_add_u64,
    wrapping_sub_u64
);
make_unsigned_integer_atomic!(
    PAtomicUsize,
    PermissionUsize,
    PermissionDataUsize,
    AtomicUsize,
    usize,
    wrapping_add_usize,
    wrapping_sub_usize
);

make_signed_integer_atomic!(
    PAtomicI8,
    PermissionI8,
    PermissionDataI8,
    AtomicI8,
    i8,
    wrapping_add_i8,
    wrapping_sub_i8
);
make_signed_integer_atomic!(
    PAtomicI16,
    PermissionI16,
    PermissionDataI16,
    AtomicI16,
    i16,
    wrapping_add_i16,
    wrapping_sub_i16
);
make_signed_integer_atomic!(
    PAtomicI32,
    PermissionI32,
    PermissionDataI32,
    AtomicI32,
    i32,
    wrapping_add_i32,
    wrapping_sub_i32
);

#[cfg(target_has_atomic = "64")]
make_signed_integer_atomic!(
    PAtomicI64,
    PermissionI64,
    PermissionDataI64,
    AtomicI64,
    i64,
    wrapping_add_i64,
    wrapping_sub_i64
);
make_signed_integer_atomic!(
    PAtomicIsize,
    PermissionIsize,
    PermissionDataIsize,
    AtomicIsize,
    isize,
    wrapping_add_isize,
    wrapping_sub_isize
);

atomic_types_generic!(PAtomicPtr, PermissionPtr, PermissionDataPtr, AtomicPtr<T>, *mut T);

#[cfg_attr(verus_keep_ghost, verifier::verus_macro)]
impl<T> PAtomicPtr<T> {
    atomic_common_methods!(
        PAtomicPtr::<T>,
        PermissionPtr::<T>,
        PermissionDataPtr::<T>,
        AtomicPtr::<T>,
        *mut T,
        [ .view().addr ]
    );
}

// impl<X, Y, Pred> core::fmt::Debug for AtomicUpdate<X, Y, Pred> {
//     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//         f.debug_struct("AtomicUpdate").finish_non_exhaustive()
//     }
// }

verus! {

#[verifier::reject_recursive_types(X)]
pub struct AtomicUpdate<X, Y, Pred> {
    pred: Pred,
    _dummy: core::marker::PhantomData<spec_fn(X) -> Y>,
}

impl<X, Y, Pred> AtomicUpdate<X, Y, Pred> {
    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::pred"]
    pub closed spec fn pred(self) -> Pred {
        self.pred
    }

    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::resolves"]
    pub uninterp spec fn resolves(self) -> bool;

    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::input"]
    pub uninterp spec fn input(self) -> X;

    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::output"]
    pub uninterp spec fn output(self) -> Y;
}

impl<X, Y, Pred: UpdatePredicate<X, Y>> AtomicUpdate<X, Y, Pred> {
    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::req"]
    pub open spec fn req(self, x: X) -> bool {
        self.pred().req(x)
    }

    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::ens"]
    pub open spec fn ens(self, x: X, y: Y) -> bool {
        self.pred().ens(x, y)
    }

    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::outer_mask"]
    pub open spec fn outer_mask(self) -> Set<int> {
        self.pred().outer_mask()
    }

    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::inner_mask"]
    pub open spec fn inner_mask(self) -> Set<int> {
        self.pred().inner_mask()
    }
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::atomic::pred_args"]
#[doc(hidden)]
pub uninterp spec fn pred_args<Pred, Args>(pred: Pred) -> Args;

pub trait UpdatePredicate<X, Y>: Sized {
    spec fn req(self, x: X) -> bool;

    spec fn ens(self, x: X, y: Y) -> bool;

    open spec fn outer_mask(self) -> Set<int> {
        Set::empty()
    }

    open spec fn inner_mask(self) -> Set<int> {
        Set::empty()
    }
}

pub enum UpdateControlFlow {
    Commit,
    Abort,
}

impl UpdateControlFlow {
    pub open spec fn is_commit(self) -> bool {
        match self {
            UpdateControlFlow::Commit => true,
            UpdateControlFlow::Abort => false,
        }
    }

    pub open spec fn is_abort(self) -> bool {
        !self.is_commit()
    }
}

pub trait UpdateTry {
    spec fn branch(self) -> UpdateControlFlow;
}

impl<T, E> UpdateTry for Result<T, E> {
    open spec fn branch(self) -> UpdateControlFlow {
        match self {
            Ok(_) => UpdateControlFlow::Commit,
            Err(_) => UpdateControlFlow::Abort,
        }
    }
}

#[derive(Debug)]
pub struct I<T>(pub T);

impl<T> I<T> {
    pub proof fn get(tracked self) -> (tracked out: T)
        ensures
            self@ == out,
    {
        self.0
    }
}

impl<T> View for I<T> {
    type V = T;

    #[verifier::inline]
    open spec fn view(&self) -> T {
        self.0
    }
}

impl<T> UpdateTry for I<T> {
    open spec fn branch(self) -> UpdateControlFlow {
        UpdateControlFlow::Commit
    }
}

impl UpdateTry for () {
    open spec fn branch(self) -> UpdateControlFlow {
        UpdateControlFlow::Commit
    }
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::atomic::branch_bool"]
#[doc(hidden)]
pub open spec fn branch_bool<T: UpdateTry>(this: T) -> bool {
    this.branch().is_commit()
}

// Definition for atomic function call
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::atomic::atomically"]
#[doc(hidden)]
#[verifier::external_body]
pub fn atomically<X, Y: UpdateTry, P: UpdatePredicate<X, Y>>(
    _body: impl FnOnce(fn (X) -> Y, Ghost<AtomicUpdate<X, Y, P>>, fn ()),
) -> AtomicUpdate<X, Y, P> {
    arbitrary()
}

// Definitions for `try_open_atomic_update` macro
#[doc(hidden)]
pub struct BlockGuard<T> {
    _inner: core::marker::PhantomData<T>,
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::atomic::try_open_atomic_update_begin"]
#[doc(hidden)]
#[verifier::external]  /* vattr */
pub fn try_open_atomic_update_begin<X, Y: UpdateTry, P: UpdatePredicate<X, Y>>(
    _atomic_update: AtomicUpdate<X, Y, P>,
) -> (BlockGuard<AtomicUpdate<X, Y, P>>, X) {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::atomic::try_open_atomic_update_end"]
#[doc(hidden)]
#[verifier::external]  /* vattr */
pub fn try_open_atomic_update_end<X, Y: UpdateTry, P: UpdatePredicate<X, Y>>(
    _guard: BlockGuard<AtomicUpdate<X, Y, P>>,
    _y: Tracked<Y>,
) -> Tracked<Result<(), AtomicUpdate<X, Y, P>>> {
    unimplemented!()
}

// Helper function for wrapping/unwrapping tracked results
// using in `open_atomic_update` and `peek_atomic_update`
// #[doc(hidden)]
// #[verifier::skip_inst_collector]
// pub proof fn au_commit_wrap_proof<X, Y>(tracked y: Tracked<Y>) -> (res: Tracked<Result<Y, X>>)
//     ensures
//         res@ is Ok,
//         res@->Ok_0 == y@,
//     opens_invariants none
// {
//     Tracked(Ok(y.get()))
// }
// #[doc(hidden)]
// #[verifier::skip_inst_collector]
// pub exec fn au_commit_wrap_exec<X, Y>(y: Tracked<Y>) -> (res: Tracked<Result<Y, X>>)
//     ensures
//         res@ is Ok,
//         res@->Ok_0 == y@,
//     opens_invariants none
// {
//     Tracked(Ok(y.get()))
// }
// #[doc(hidden)]
// #[verifier::skip_inst_collector]
// pub proof fn au_abort_wrap_proof<X, Y>(tracked x: Tracked<X>) -> (res: Tracked<Result<Y, X>>)
//     ensures
//         res@ is Err,
//         res@->Err_0 == x@,
//     opens_invariants none
// {
//     Tracked(Err(x.get()))
// }
// #[doc(hidden)]
// #[verifier::skip_inst_collector]
// pub exec fn au_abort_wrap_exec<X, Y>(x: Tracked<X>) -> (res: Tracked<Result<Y, X>>)
//     ensures
//         res@ is Err,
//         res@->Err_0 == x@,
//     opens_invariants none
// {
//     Tracked(Err(x.get()))
// }
// #[doc(hidden)]
// #[verifier::skip_inst_collector]
// pub proof fn au_abort_unwrap_proof<X, Y, Z, Pred>(
//     tracked err_au: Tracked<Result<(), AtomicUpdate<X, Y, Z, Pred>>>,
// ) -> (au: Tracked<AtomicUpdate<X, Y, Z, Pred>>)
//     requires
//         err_au@ is Err,
//     ensures
//         err_au@->Err_0 == au@,
//     opens_invariants none
// {
//     Tracked(err_au.get().tracked_unwrap_err())
// }
// #[doc(hidden)]
// #[verifier::skip_inst_collector]
// pub exec fn au_abort_unwrap_exec<X, Y, Z, Pred>(
//     err_au: Tracked<Result<(), AtomicUpdate<X, Y, Z, Pred>>>,
// ) -> (au: Tracked<AtomicUpdate<X, Y, Z, Pred>>)
//     requires
//         err_au@ is Err,
//     ensures
//         err_au@->Err_0 == au@,
//     opens_invariants none
// {
//     Tracked(err_au.get().tracked_unwrap_err())
// }
// Macro definitions
#[macro_export]
macro_rules! open_atomic_update {
    ($($tail:tt)*) => {
        {
            let _ = ::verus_builtin_macros::verus_exec_open_au_macro_exprs!(
                $crate::atomic::try_open_atomic_update_internal!(
                    $($tail)*, @EXEC, au_commit_wrap_exec
                )
            );
        }
    };
}

#[macro_export]
macro_rules! open_atomic_update_in_proof {
    ($($tail:tt)*) => {
        {
            let _ = ::verus_builtin_macros::verus_ghost_open_au_macro_exprs!(
                $crate::atomic::try_open_atomic_update_internal!(
                    $($tail)*, @PROOF, au_commit_wrap_proof
                )
            );
        }
    };
}

#[macro_export]
macro_rules! peek_atomic_update {
    ($($tail:tt)*) => {
        {
            #[verifier::exec]
            let err_au = ::verus_builtin_macros::verus_exec_open_au_macro_exprs!(
                $crate::atomic::try_open_atomic_update_internal!(
                    $($tail)*, @EXEC, au_abort_wrap_exec
                )
            );

            match () {
                #[cfg(verus_keep_ghost_body)]
                _ => $crate::atomic::au_abort_unwrap_exec(err_au),

                #[cfg(not(verus_keep_ghost_body))]
                _ => ::verus_builtin::Tracked::assume_new_fallback(|| ::core::unreachable!()),
            }
        }
    };
}

#[macro_export]
macro_rules! peek_atomic_update_in_proof {
    ($($tail:tt)*) => {
        {
            #[verifier::proof]
            let err_au = ::verus_builtin_macros::verus_ghost_open_au_macro_exprs!(
                $crate::atomic::try_open_atomic_update_internal!(
                    $($tail)*, @PROOF, au_abort_wrap_proof
                )
            );

            match () {
                #[cfg(verus_keep_ghost_body)]
                _ => $crate::atomic::au_abort_unwrap_proof(err_au),

                #[cfg(not(verus_keep_ghost_body))]
                _ => ::verus_builtin::Tracked::assume_new_fallback(|| ::core::unreachable!()),
            }
        }
    };
}

#[macro_export]
macro_rules! try_open_atomic_update {
    ($($tail:tt)*) => {
        ::verus_builtin_macros::verus_exec_open_au_macro_exprs!(
            $crate::atomic::try_open_atomic_update_internal!($($tail)*)
        )
    };
}

#[macro_export]
macro_rules! try_open_atomic_update_in_proof {
    ($($tail:tt)*) => {
        ::verus_builtin_macros::verus_ghost_open_au_macro_exprs!(
            $crate::atomic::try_open_atomic_update_internal!($($tail)*)
        )
    };
}

#[macro_export]
macro_rules! try_open_atomic_update_internal {
    ($au:expr, $x:pat => $body:block, @EXEC, $wrap_fn:ident) => {
        $crate::atomic::try_open_atomic_update_internal!($au, $x => {
            #[verifier::exec]
            let v = $body;

            match () {
                #[cfg(verus_keep_ghost_body)]
                _ => $crate::atomic::$wrap_fn(v),

                #[cfg(not(verus_keep_ghost_body))]
                _ => ::verus_builtin::Tracked::assume_new_fallback(|| ::core::unreachable!()),
            }
        })
    };

    ($au:expr, $x:pat => $body:block, @PROOF, $wrap_fn:ident) => {
        $crate::atomic::try_open_atomic_update_internal!($au, $x => {
            #[verifier::proof]
            let v = $body;

            match () {
                #[cfg(verus_keep_ghost_body)]
                _ => $crate::atomic::$wrap_fn(v),

                #[cfg(not(verus_keep_ghost_body))]
                _ => ::verus_builtin::Tracked::assume_new_fallback(|| ::core::unreachable!()),
            }
        })
    };

    ($au:expr, $x:pat => $body:block) => {
        #[cfg_attr(verus_keep_ghost, verifier::open_au_block)] /* vattr */ {
            #[cfg(verus_keep_ghost_body)]
            let (guard, $x) = $crate::atomic::try_open_atomic_update_begin($au);
            let res = $body;

            match res {
                #[cfg(verus_keep_ghost_body)]
                res => $crate::atomic::try_open_atomic_update_end(guard, res),

                #[cfg(not(verus_keep_ghost_body))]
                _ => ::verus_builtin::Tracked::assume_new_fallback(|| ::core::unreachable!()),
            }
        }
    };
}

#[doc(hidden)]
pub use {try_open_atomic_update_internal};
pub use {
    open_atomic_update,
    open_atomic_update_in_proof,
    peek_atomic_update,
    peek_atomic_update_in_proof,
    try_open_atomic_update,
    try_open_atomic_update_in_proof,
};

impl<T> PAtomicPtr<T> {
    #[inline(always)]
    #[verifier::external_body]  /* vattr */
    #[verifier::atomic]  /* vattr */
    #[cfg(any(verus_keep_ghost, feature = "strict_provenance_atomic_ptr"))]
    pub fn fetch_and(&self, Tracked(perm): Tracked<&mut PermissionPtr<T>>, n: usize) -> (ret:
        *mut T)
        requires
            equal(self.id(), old(perm).view().patomic),
        ensures
            equal(old(perm).view().value, ret),
            perm.view().patomic == old(perm).view().patomic,
            perm.view().value@.addr == (old(perm).view().value@.addr & n),
            perm.view().value@.provenance == old(perm).view().value@.provenance,
            perm.view().value@.metadata == old(perm).view().value@.metadata,
        opens_invariants none
        no_unwind
    {
        return self.ato.fetch_and(n, Ordering::SeqCst);
    }

    #[inline(always)]
    #[verifier::external_body]  /* vattr */
    #[verifier::atomic]  /* vattr */
    #[cfg(any(verus_keep_ghost, feature = "strict_provenance_atomic_ptr"))]
    pub fn fetch_xor(&self, Tracked(perm): Tracked<&mut PermissionPtr<T>>, n: usize) -> (ret:
        *mut T)
        requires
            equal(self.id(), old(perm).view().patomic),
        ensures
            equal(old(perm).view().value, ret),
            perm.view().patomic == old(perm).view().patomic,
            perm.view().value@.addr == (old(perm).view().value@.addr ^ n),
            perm.view().value@.provenance == old(perm).view().value@.provenance,
            perm.view().value@.metadata == old(perm).view().value@.metadata,
        opens_invariants none
        no_unwind
    {
        return self.ato.fetch_xor(n, Ordering::SeqCst);
    }

    #[inline(always)]
    #[verifier::external_body]  /* vattr */
    #[verifier::atomic]  /* vattr */
    #[cfg(any(verus_keep_ghost, feature = "strict_provenance_atomic_ptr"))]
    pub fn fetch_or(&self, Tracked(perm): Tracked<&mut PermissionPtr<T>>, n: usize) -> (ret: *mut T)
        requires
            equal(self.id(), old(perm).view().patomic),
        ensures
            equal(old(perm).view().value, ret),
            perm.view().patomic == old(perm).view().patomic,
            perm.view().value@.addr == (old(perm).view().value@.addr | n),
            perm.view().value@.provenance == old(perm).view().value@.provenance,
            perm.view().value@.metadata == old(perm).view().value@.metadata,
        opens_invariants none
        no_unwind
    {
        return self.ato.fetch_or(n, Ordering::SeqCst);
    }
}

pub broadcast group group_atomic_axioms {
    PermissionBool::view_bijective,
    //
    // signed atomic integers
    //
    PermissionI8::view_bijective,
    PermissionI16::view_bijective,
    PermissionI32::view_bijective,
    #[cfg(target_has_atomic = "64")]
    PermissionI64::view_bijective,
    PermissionIsize::view_bijective,
    //
    // signed atomic integers
    //
    PermissionU8::view_bijective,
    PermissionU16::view_bijective,
    PermissionU32::view_bijective,
    #[cfg(target_has_atomic = "64")]
    PermissionU64::view_bijective,
    PermissionUsize::view_bijective,
}

} // verus!
