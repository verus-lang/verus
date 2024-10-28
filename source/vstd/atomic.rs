#![allow(unused_imports)]

use core::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicIsize, AtomicPtr, AtomicU16,
    AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering,
};

use super::modes::*;
use super::pervasive::*;
use super::prelude::*;

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
            pub spec fn view(self) -> $p_data_ident;

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
            pub spec fn view(self) -> $p_data_ident <T>;

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
        verus!{

        pub spec fn id(&self) -> int;

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
        verus!{

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

verus! {

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

} // verus!
