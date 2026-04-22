#![allow(unused_imports)]

use core::sync::atomic::{
    AtomicBool, AtomicI8, AtomicI16, AtomicI32, AtomicIsize, AtomicPtr, AtomicU8, AtomicU16,
    AtomicU32, AtomicUsize, Ordering,
};

#[cfg(target_has_atomic = "64")]
use core::sync::atomic::{AtomicI64, AtomicU64};

use super::modes::*;
use super::pervasive::*;
use super::prelude::*;
use super::view::*;
use super::wrapping::*;

macro_rules! make_unsigned_integer_atomic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty, $modname:ident) => {
        atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty, []);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $modname);
        }
    };
}

macro_rules! make_signed_integer_atomic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty, $modname:ident) => {
        atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
        #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty, []);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $modname);
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
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $modname:ident) => {
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
                perm.view().value as int == $modname::wrapping_add(old(perm).view().value, n),
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
                perm.view().value as int == $modname::wrapping_sub(old(perm).view().value, n),
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

make_unsigned_integer_atomic!(PAtomicU8, PermissionU8, PermissionDataU8, AtomicU8, u8, u8_specs);
make_unsigned_integer_atomic!(
    PAtomicU16,
    PermissionU16,
    PermissionDataU16,
    AtomicU16,
    u16,
    u16_specs
);
make_unsigned_integer_atomic!(
    PAtomicU32,
    PermissionU32,
    PermissionDataU32,
    AtomicU32,
    u32,
    u32_specs
);

#[cfg(target_has_atomic = "64")]
make_unsigned_integer_atomic!(
    PAtomicU64,
    PermissionU64,
    PermissionDataU64,
    AtomicU64,
    u64,
    u64_specs
);
make_unsigned_integer_atomic!(
    PAtomicUsize,
    PermissionUsize,
    PermissionDataUsize,
    AtomicUsize,
    usize,
    usize_specs
);

make_signed_integer_atomic!(PAtomicI8, PermissionI8, PermissionDataI8, AtomicI8, i8, i8_specs);
make_signed_integer_atomic!(
    PAtomicI16,
    PermissionI16,
    PermissionDataI16,
    AtomicI16,
    i16,
    i16_specs
);
make_signed_integer_atomic!(
    PAtomicI32,
    PermissionI32,
    PermissionDataI32,
    AtomicI32,
    i32,
    i32_specs
);

#[cfg(target_has_atomic = "64")]
make_signed_integer_atomic!(
    PAtomicI64,
    PermissionI64,
    PermissionDataI64,
    AtomicI64,
    i64,
    i64_specs
);
make_signed_integer_atomic!(
    PAtomicIsize,
    PermissionIsize,
    PermissionDataIsize,
    AtomicIsize,
    isize,
    isize_specs
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

impl<X, Y, Pred> core::fmt::Debug for AtomicUpdate<X, Y, Pred> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AtomicUpdate").finish_non_exhaustive()
    }
}

verus! {

/// The **atomic update (AU)** is a ghost object which encapsulates the linearization point of a logically atomic function.
///
/// Logical atomicity is a proof technique that allows us to treat a function as if it was atomic, i.e. as if it evaluates in a single atomic step, even though it might perform multiple `exec`-mode operations internally.
/// The key idea is that a logically atomic function contains a **linearization point (LP)**, that is, a point in the function which updates the state of the program in a single atomic step of computation.
/// We specify the behavior of such a function by describing the state of the program at four distinct points in time, specifically:
/// - **(private pre)** at the start of the function,
/// - **(atomic pre)** just before the linearization point,
/// - **(atomic post)** just after the linearization point,
/// - **(private post)** at the end of the function.
/// ```
///                        linearization point
///                                 🠗
/// ├──────────────────────────────┤●├─────────────────────────┤
///  private                 atomic   atomic            private
///  pre                        pre   post                 post
/// ```
/// The `AtomicUpdate` ghost object is the central abstraction for our implementation if logical atomicity, as it encapsulates the behavior of the function at the linearization point.
/// The atomic update is declared by the atomic specification, it is constructed by the atomic function call (i.e. the "client"), and it is opened/destructed at the linearization point of the logically atomic function (i.e. the "library").
///
/// # The Atomic Specification
///
/// We can declare a function to be logically atomic by adding an `atomically` block to its specification.
/// The atomic specification has the following general shape:
/// ```
/// exec fn function(px: PX) -> (py: PY)
///     atomically (atomic_update) {
///         type PredType,
///
///         (ax: AX) -> (ay: AY),
///
///         requires atomic_pre(px, ax),
///         ensures atomic_post(px, ax, ay),
///
///         outer_mask Eo,
///         inner_mask Ei,
///     },
///
///     requires private_pre(px),
///     ensures private_post(px, ax, ay, py),
/// ```
/// This specification binds an additional `tracked` variable `atomic_update: AtomicUpdate<AX, AY, PredType>`, where the type `PredType` is generated automatically by the atomic specification.
/// See the documentation for the [`UpdatePredicate`] trait for more information about the predicate type.
///
/// ## Notes on the Abort Case
///
/// Our implementation supports aborting, which allows the library to "peak" at the resources of the atomic update without committing to the linearization point.
/// To this end, we require the output type of the atomic update (named `AY` above) to implement the [`UpdateTry`] trait.
///
/// The most canonical type for the output is [`Result`], where `Ok(..)` indicates the atomic update has been committed at the linearization point of the function, and `Err(..)` indicates that the atomic update has been aborted.
/// In cases where the abort mechanism is undesirable, we provide a trivial wrapper type [`Commit`] which prevents the atomic update from being aborted.
///
/// # Opening the Atomic Update
/// To open the atomic update, we use the [`try_open_atomic_update`] macro as follows:
/// ```
/// let res_au = try_open_atomic_update!(au, ax => {
///     // assume atomic pre
///     // ...
///     // assert atomic post
///     Tracked(ay)
/// })
/// ```
/// When we open the atomic update, we are given the input (`ax: AX`) and learn the atomic precondition, and at the end of the macro call, we return the output (`ay: AY`) and prove the atomic postcondition.
/// The macro outputs a value of type `Result<(), Tracked<AtomicUpdate<AX, AY, PredType>>>`.
/// If the atomic update is committed, as indicated by the [`UpdateTry`] trait, then the atomic update is consumed and we get `Ok(())`.
/// Otherwise, if the atomic update is aborted, we get back the same atomic update we put in (i.e. `Err(Tracked(au))`), allowing us to open it again later.
///
/// # The Atomic Function Call
///
/// To call a logically atomic function, we use the following syntax:
/// ```
/// let py = function(px) atomically |update| {
///     // ...
///     // assert atomic pre
///     let ay = update(ax);
///     // assume atomic post
///     // ...
///     break/continue
/// }
/// ```
/// The atomic function call binds an `update` function, which represents the effects of the [`try_open_atomic_update`] macro to the client.
/// It is helpful to think of the macro as defining the `update` function, as their inputs and outputs, as well as their pre- and postcondition match precisely.
/// The `update` function is `proof`-mode, allowing atomic invariants to be opened around it.
///
/// Since the library function may open the atomic update multiple times, due to aborting, the client must prove that it can provide the required resources as many times as necessary, meaning the atomic function call must be a loop.
/// If the atomic update is committed by the library, as indicated by the [`UpdateTry`] implementation on the output type, the client must `break` out of the loop.
/// Similarly, if the library aborts the atomic update, the loop must `continue`, either explicitly or implicitly.
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(Y)]
#[verifier::reject_recursive_types(Pred)]
#[verifier::external_body]
pub struct AtomicUpdate<X, Y, Pred> {
    pred: Pred,
    _dummy: core::marker::PhantomData<fn (fn (X) -> Y)>,
}

impl<X, Y, Pred> AtomicUpdate<X, Y, Pred> {
    /// The predicate of the atomic update.
    ///
    /// See [`UpdatePredicate`] for more information.
    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::pred"]
    pub uninterp spec fn pred(self) -> Pred;

    /// A prophesy variable which indicates that an atomic update has been resolved.
    ///
    /// Initially, the value of this function is unknown, i.e. we can neither prove that it is `true` or `false`.
    /// Once the atomic update has been committed using the [`try_open_atomic_update`] macro, we learn that `au.resolves()` is `true`.
    ///
    /// We must be able to prove that `au.resolves()` when the logically atomic function exits.
    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::resolves"]
    pub uninterp spec fn resolves(self) -> bool;

    /// A prophesy variable for the input value of the atomic update.
    ///
    /// When the atomic update is committed, this variable is resolved to the input value of the atomic update.
    /// This variable is used internally in the (private) postcondition of the logically atomic function.
    #[rustc_diagnostic_item = "verus::vstd::atomic::AtomicUpdate::input"]
    pub uninterp spec fn input(self) -> X;

    /// A prophesy variable for the output value of the atomic update.
    ///
    /// When the atomic update is committed, this variable is resolved to the output value of the atomic update.
    /// This variable is used internally in the (private) postcondition of the logically atomic function.
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

/// Trait used to specify the update predicate for the [`AtomicUpdate`].
///
/// This trait is implemented automatically by Verus when a logically atomic function is defined.
/// ```
/// exec fn function(px: PX) -> (py: PY)
///     atomically (atomic_update) {
///         type PredType,
///
///         (ax: AX) -> (ay: AY),
///
///         requires atomic_pre(px, ax),
///         ensures atomic_post(px, ax, ay),
///
///         outer_mask Eo,
///         inner_mask Ei,
///     },
///     requires private_pre(px),
///     ensures private_post(px, ax, ay, py),
/// ```
/// The above code snipped generates (roughly) the type and trait implementation below.
/// ```
/// struct PredType { px: Ghost<PX> }
///
/// impl UpdatePredicate<AX, AY> for PredType {
///     open spec fn req(self, x: X)       -> bool { atomic_pre  }
///     open spec fn ens(self, x: X, y: Y) -> bool { atomic_post }
///
///     open spec fn outer_mask(self) -> Set<int> { Eo }
///     open spec fn inner_mask(self) -> Set<int> { Ei }
/// }
/// ```
pub trait UpdatePredicate<X, Y>: Sized {
    /// The atomic pre-condition.
    spec fn req(self, x: X) -> bool;

    /// The atomic post-condition.
    spec fn ens(self, x: X, y: Y) -> bool;

    /// The outer mask of the atomic update.
    open spec fn outer_mask(self) -> Set<int> {
        Set::empty()
    }

    /// The inner mask of the atomic update.
    open spec fn inner_mask(self) -> Set<int> {
        Set::empty()
    }
}

/// The control flow corresponding to the atomic update output.
pub enum UpdateControlFlow {
    /// The update output value indicates that the atomic update has been committed.
    ///
    /// This means [`try_open_atomic_update`] will consume the atomic update (i.e. return `Ok(())`),
    /// and the atomic function call has to `break`.
    Commit,
    /// The update output value indicates that the atomic update has been aborted.
    ///
    /// This means [`try_open_atomic_update`] will give back the atomic update (i.e. return `Err(Tracked(au))`),
    /// and the atomic function call has to `continue`.
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

/// A trivial wrapper type which indicates a commit.
///
/// This is useful for logically atomic functions which do not require an abort case.
#[derive(Debug)]
pub struct Commit<T>(pub T);

impl<T> Commit<T> {
    pub proof fn get(tracked self) -> (tracked out: T)
        ensures
            self@ == out,
    {
        self.0
    }
}

impl<T> View for Commit<T> {
    type V = T;

    #[verifier::inline]
    open spec fn view(&self) -> T {
        self.0
    }
}

impl<T> UpdateTry for Commit<T> {
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
#[verifier::external]
pub fn atomically<X, Y: UpdateTry, P: UpdatePredicate<X, Y>>(
    _body: impl FnOnce(fn (X) -> Y, Ghost<AtomicUpdate<X, Y, P>>),
) -> AtomicUpdate<X, Y, P> {
    arbitrary()
}

// Definitions for `try_open_atomic_update` macro
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::atomic::try_open_au"]
#[doc(hidden)]
#[verifier::external_body]
pub fn try_open_au<X, Y: UpdateTry, P: UpdatePredicate<X, Y>>(
    _atomic_update: AtomicUpdate<X, Y, P>,
    _body: impl FnOnce(X) -> Tracked<Y>,
) -> Tracked<Result<(), AtomicUpdate<X, Y, P>>> {
    arbitrary()
}

// Definitions for `try_open_atomic_update` macro
#[doc(hidden)]
pub struct BlockGuard<T> {
    _inner: core::marker::PhantomData<T>,
}

#[cfg(verus_keep_ghost)]
#[doc(hidden)]
#[verifier::external]  /* vattr */
pub fn bind_lifetime_internal<'a, X: 'a, Y, P>(
    _block_guard: &'a BlockGuard<AtomicUpdate<X, Y, P>>,
) -> X {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::atomic::try_open_atomic_update_begin"]
#[doc(hidden)]
#[verifier::external]  /* vattr */
pub fn try_open_atomic_update_begin<X, Y: UpdateTry, P: UpdatePredicate<X, Y>>(
    _atomic_update: AtomicUpdate<X, Y, P>,
) -> BlockGuard<AtomicUpdate<X, Y, P>> {
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
            let guard = $crate::atomic::try_open_atomic_update_begin($au);
            #[cfg(verus_keep_ghost_body)]
            let $x = $crate::atomic::bind_lifetime_internal(&guard);
            let res = $body;

            match res {
                #[cfg(verus_keep_ghost_body)]
                res => $crate::atomic::try_open_atomic_update_end(guard, res),

                #[cfg(not(verus_keep_ghost_body))]
                _ => ::verus_builtin::Tracked::assume_new_fallback(|| ::core::unreachable!()),
            }
        }
    };

    // ($au:expr, $x:pat => $body:block) => {
    //     match () {
    //         #[cfg(verus_keep_ghost_body)]
    //         _ => $crate::atomic::try_open_au($au, {
    //             let _verus_internal_identifier_for_closures = ::verus_builtin::dummy_capture_new();
    //             |$x| {
    //                 ::verus_builtin::dummy_capture_consume(_verus_internal_identifier_for_closures);
    //                 $body
    //             }
    //         }),

    //         #[cfg(not(verus_keep_ghost_body))]
    //         _ => {
    //             let _ = $body;
    //             ::verus_builtin::Tracked::assume_new_fallback(|| ::core::unreachable!())
    //         },
    //     }
    // };
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
