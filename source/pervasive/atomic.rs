use core::sync::atomic::{
    AtomicBool,
    AtomicU8, AtomicU16, AtomicU32, AtomicU64, AtomicUsize,
    AtomicI8, AtomicI16, AtomicI32, AtomicI64, AtomicIsize,
    Ordering};

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;
#[allow(unused_imports)] use crate::pervasive::result::*;

macro_rules! make_unsigned_integer_atomic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
        // TODO we could support `std::intrinsics::wrapping_add`
        // and use that instead.

        verus!{

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
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub);
        }
    }
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
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub);
        }
    }
}


macro_rules! make_bool_atomic {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
            atomic_bool_methods!($at_ident, $p_ident, $rust_ty, $value_ty);
        }
    }
}

macro_rules! atomic_types {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        #[verifier(external_body)] /* vattr */
        pub struct $at_ident {
            ato: $rust_ty,
        }

        #[verifier::proof]
        #[verifier(external_body)] /* vattr */
        pub struct $p_ident {
            no_copy: NoCopy,
        }

        #[verifier::spec]
        pub struct $p_data_ident {
            #[verifier::spec] pub patomic: int,
            #[verifier::spec] pub value: $value_ty,
        }

        impl $p_ident {
            #[verifier::spec]
            #[verifier(external_body)] /* vattr */
            pub fn view(self) -> $p_data_ident { unimplemented!(); }

            #[cfg(not(verus_macro_erase_ghost))]
            #[verifier::spec] #[verifier(publish)] /* vattr */
            pub fn is_for(&self, patomic: $at_ident) -> bool {
                self.view().patomic == patomic.id()
            }

            #[cfg(not(verus_macro_erase_ghost))]
            #[verifier::spec] #[verifier(publish)] /* vattr */
            pub fn points_to(&self, v: $value_ty) -> bool {
                self.view().value == v
            }
        }
    }
}

macro_rules! atomic_common_methods {
    ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        fndecl!(pub fn id(&self) -> int);

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        pub fn new(i: $value_ty) -> ($at_ident, Proof<$p_ident>) {
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|res : ($at_ident, Proof<$p_ident>)|
                equal(res.1.0.view(), $p_data_ident{ patomic: res.0.id(), value: i })
            );

            let p = $at_ident { ato: <$rust_ty>::new(i) };
            let Proof(t) = exec_proof_from_false();
            (p, Proof(t))
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn load(&self, #[verifier::proof] perm: &$p_ident) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), perm.view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| equal(perm.view().value, ret));
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.load(Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn store(&self, #[verifier::proof] perm: &mut $p_ident, v: $value_ty) {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(equal(perm.view().value, v) && equal(self.id(), perm.view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            self.ato.store(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn compare_exchange(&self, #[verifier::proof] perm: &mut $p_ident, current: $value_ty, new: $value_ty) -> Result<$value_ty, $value_ty> {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: Result<$value_ty, $value_ty>|
                equal(self.id(), perm.view().patomic)
                && match ret {
                    Result::Ok(r) =>
                           current == old(perm).view().value
                        && equal(perm.view().value, new)
                        && equal(r, old(perm).view().value),
                    Result::Err(r) =>
                           current != old(perm).view().value
                        && equal(perm.view().value, old(perm).view().value)
                        && equal(r, old(perm).view().value),
                }
            );
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            match self.ato.compare_exchange(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn compare_exchange_weak(&self, #[verifier::proof] perm: &mut $p_ident, current: $value_ty, new: $value_ty) -> Result<$value_ty, $value_ty> {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: Result<$value_ty, $value_ty>|
                equal(self.id(), perm.view().patomic)
                && match ret {
                    Result::Ok(r) =>
                           current == old(perm).view().value
                        && equal(perm.view().value, new)
                        && equal(r, old(perm).view().value),
                    Result::Err(r) =>
                           equal(perm.view().value, old(perm).view().value)
                        && equal(r, old(perm).view().value),
                }
            );
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            match self.ato.compare_exchange_weak(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn swap(&self, #[verifier::proof] perm: &mut $p_ident, v: $value_ty) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty|
                   equal(perm.view().value, v)
                && equal(old(perm).view().value, ret)
                && equal(self.id(), perm.view().patomic)
            );
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.swap(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        pub fn into_inner(self, #[verifier::proof] perm: $p_ident) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), perm.view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| equal(perm.view().value, ret));
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.into_inner();
        }
    }
}

macro_rules! atomic_integer_methods {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
        // Note that wrapping-on-overflow is the defined behavior for fetch_add and fetch_sub
        // for Rust's atomics (in contrast to ordinary arithmetic)

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_add_wrapping(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                spec_cast_integer::<$value_ty, int>(perm.view().value) == $wrap_add(spec_cast_integer(old(perm).view().value), spec_cast_integer(n)),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_add(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_sub_wrapping(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                spec_cast_integer::<$value_ty, int>(perm.view().value) == $wrap_sub(spec_cast_integer::<$value_ty, int>(old(perm).view().value), spec_cast_integer(n)),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_sub(n, Ordering::SeqCst);
        }

        // fetch_add and fetch_sub are more natural in the common case that you
        // don't expect wrapping

        #[inline(always)]
        #[verifier(atomic)] /* vattr */
        pub fn fetch_add(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
                spec_cast_integer::<$value_ty, int>(<$value_ty>::MIN) <= old(perm).view().value.spec_add(n),
                old(perm).view().value.spec_add(n) <= spec_cast_integer::<$value_ty, int>(<$value_ty>::MAX),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                spec_eq(perm.view().value, old(perm).view().value.spec_add(n)),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            self.fetch_add_wrapping(&mut *perm, n)
        }

        #[inline(always)]
        #[verifier(atomic)] /* vattr */
        pub fn fetch_sub(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
                spec_cast_integer::<$value_ty, int>(<$value_ty>::MIN) <= old(perm).view().value.spec_sub(n),
                old(perm).view().value.spec_sub(n) <= spec_cast_integer::<$value_ty, int>(<$value_ty>::MAX),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                spec_eq(perm.view().value, old(perm).view().value.spec_sub(n)),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            self.fetch_sub_wrapping(&mut *perm, n)
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_and(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value & n),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_or(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value | n),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_xor(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value ^ n),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_xor(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_nand(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == !(old(perm).view().value & n),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_max(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (if old(perm).view().value > n { old(perm).view().value } else { n }),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_max(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_min(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty
        {
            #[cfg(not(verus_macro_erase_ghost))]
            requires(equal(self.id(), old(perm).view().patomic));
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| [
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (if old(perm).view().value < n { old(perm).view().value } else { n }),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_min(n, Ordering::SeqCst);
        }
    }
}

macro_rules! atomic_bool_methods {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_and(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == (old(perm).view().value && n)
            );
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_or(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == (old(perm).view().value || n)
            );
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_xor(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == ((old(perm).view().value && !n) || (!old(perm).view().value && n))
            );
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_xor(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)] /* vattr */
        #[verifier(atomic)] /* vattr */
        pub fn fetch_nand(&self, #[verifier::proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            #[cfg(not(verus_macro_erase_ghost))]
            requires([
                equal(self.id(), old(perm).view().patomic),
            ]);
            #[cfg(not(verus_macro_erase_ghost))]
            ensures(|ret: $value_ty| equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == !(old(perm).view().value && n)
            );
            #[cfg(not(verus_macro_erase_ghost))]
            opens_invariants_none();

            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }
    }
}

make_bool_atomic!(PAtomicBool, PermissionBool, PermissionDataBool, AtomicBool, bool);

make_unsigned_integer_atomic!(PAtomicU8, PermissionU8, PermissionDataU8, AtomicU8, u8, wrapping_add_u8, wrapping_sub_u8);
make_unsigned_integer_atomic!(PAtomicU16, PermissionU16, PermissionDataU16, AtomicU16, u16, wrapping_add_u16, wrapping_sub_u16);
make_unsigned_integer_atomic!(PAtomicU32, PermissionU32, PermissionDataU32, AtomicU32, u32, wrapping_add_u32, wrapping_sub_u32);
make_unsigned_integer_atomic!(PAtomicU64, PermissionU64, PermissionDataU64, AtomicU64, u64, wrapping_add_u64, wrapping_sub_u64);
make_unsigned_integer_atomic!(PAtomicUsize, PermissionUsize, PermissionDataUsize, AtomicUsize, usize, wrapping_add_usize, wrapping_sub_usize);

make_signed_integer_atomic!(PAtomicI8, PermissionI8, PermissionDataI8, AtomicI8, i8, wrapping_add_i8, wrapping_sub_i8);
make_signed_integer_atomic!(PAtomicI16, PermissionI16, PermissionDataI16, AtomicI16, i16, wrapping_add_i16, wrapping_sub_i16);
make_signed_integer_atomic!(PAtomicI32, PermissionI32, PermissionDataI32, AtomicI32, i32, wrapping_add_i32, wrapping_sub_i32);
make_signed_integer_atomic!(PAtomicI64, PermissionI64, PermissionDataI64, AtomicI64, i64, wrapping_add_i64, wrapping_sub_i64);
make_signed_integer_atomic!(PAtomicIsize, PermissionIsize, PermissionDataIsize, AtomicIsize, isize, wrapping_add_isize, wrapping_sub_isize);

// TODO Support AtomicPtr
