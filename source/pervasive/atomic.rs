use std::sync::atomic::{
    AtomicBool,
    AtomicU8, AtomicU16, AtomicU32, AtomicU64,
    AtomicI8, AtomicI16, AtomicI32, AtomicI64,
    Ordering};

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;
#[allow(unused_imports)] use crate::pervasive::result::*;

macro_rules! make_unsigned_integer_atomic {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident, $int_min:expr, $int_max: expr) => {
        // TODO when we support `std::intrinsics::wrapping_add`,
        // use that instead.

        #[spec] #[verifier(publish)]
        pub fn $wrap_add(a: int, b: int) -> int {
            if a + b > $int_max {
                a + b - ($int_max - $int_min + 1)
            } else {
                a + b
            }
        }

        #[spec] #[verifier(publish)]
        pub fn $wrap_sub(a: int, b: int) -> int {
            if a - b < $int_min {
                a - b + ($int_max - $int_min + 1)
            } else {
                a - b
            }
        }

        atomic_types!($at_ident, $p_ident, $rust_ty, $value_ty);
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $rust_ty, $value_ty);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub, $int_min, $int_max);
        }
    }
}

macro_rules! make_signed_integer_atomic {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident, $int_min:expr, $int_max: expr) => {
        #[spec] #[verifier(publish)]
        pub fn $wrap_add(a: int, b: int) -> int {
            if a + b > $int_max {
                a + b - ($int_max - $int_min + 1)
            } else if a + b < $int_min {
                a + b + ($int_max - $int_min + 1)
            } else {
                a + b
            }
        }

        #[spec] #[verifier(publish)]
        pub fn $wrap_sub(a: int, b: int) -> int {
            if a - b > $int_max {
                a - b - ($int_max - $int_min + 1)
            } else if a - b < $int_min {
                a - b + ($int_max - $int_min + 1)
            } else {
                a - b
            }
        }

        atomic_types!($at_ident, $p_ident, $rust_ty, $value_ty);
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $rust_ty, $value_ty);
            atomic_integer_methods!($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub, $int_min, $int_max);
        }
    }
}


macro_rules! make_bool_atomic {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        atomic_types!($at_ident, $p_ident, $rust_ty, $value_ty);
        impl $at_ident {
            atomic_common_methods!($at_ident, $p_ident, $rust_ty, $value_ty);
            atomic_bool_methods!($at_ident, $p_ident, $rust_ty, $value_ty);
        }
    }
}

macro_rules! atomic_types {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        #[verifier(external_body)]
        pub struct $at_ident {
            ato: $rust_ty,
        }

        #[proof]
        #[verifier(unforgeable)]
        pub struct $p_ident {
            #[spec] pub patomic: int,
            #[spec] pub value: $value_ty,
        }

        impl $p_ident {
            #[spec] #[verifier(publish)]
            fn is_for(&self, patomic: $at_ident) -> bool {
                self.patomic == patomic.view()
            }

            #[spec] #[verifier(publish)]
            fn points_to(&self, v: $value_ty) -> bool {
                self.value == v
            }
        }
    }
}

macro_rules! atomic_common_methods {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        fndecl!(pub fn view(&self) -> int);

        #[inline(always)]
        #[verifier(external_body)]
        pub fn new(i: $value_ty) -> ($at_ident, Proof<$p_ident>) {
            ensures(|res : ($at_ident, Proof<$p_ident>)|
                equal(res.1, proof($p_ident{ patomic: res.0.view(), value: i }))
            );

            let p = $at_ident { ato: <$rust_ty>::new(i) };
            let Proof::proof(t) = exec_proof_from_false();
            (p, proof(t))
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn load(&self, #[proof] perm: &$p_ident) -> $value_ty {
            requires([
                equal(self.view(), perm.patomic),
            ]);
            ensures(|ret: $value_ty| equal(perm.value, ret));
            opens_invariants_none();

            return self.ato.load(Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn store(&self, #[proof] perm: &mut $p_ident, v: $value_ty) {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(equal(perm.value, v) && equal(self.view(), perm.patomic));
            opens_invariants_none();

            self.ato.store(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn compare_exchange(&self, #[proof] perm: &mut $p_ident, current: $value_ty, new: $value_ty) -> Result<$value_ty, $value_ty> {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: Result<$value_ty, $value_ty>|
                equal(self.view(), perm.patomic)
                && match ret {
                    Result::Ok(r) =>
                           current == old(perm).value
                        && equal(perm.value, new)
                        && equal(r, old(perm).value),
                    Result::Err(r) =>
                           current != old(perm).value
                        && equal(perm.value, old(perm).value)
                        && equal(r, old(perm).value),
                }
            );
            opens_invariants_none();

            match self.ato.compare_exchange(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn compare_exchange_weak(&self, #[proof] perm: &mut $p_ident, current: $value_ty, new: $value_ty) -> Result<$value_ty, $value_ty> {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: Result<$value_ty, $value_ty>|
                equal(self.view(), perm.patomic)
                && match ret {
                    Result::Ok(r) =>
                           current == old(perm).value
                        && equal(perm.value, new)
                        && equal(r, old(perm).value),
                    Result::Err(r) =>
                           equal(perm.value, old(perm).value)
                        && equal(r, old(perm).value),
                }
            );
            opens_invariants_none();

            match self.ato.compare_exchange_weak(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn swap(&self, #[proof] perm: &mut $p_ident, v: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty|
                   equal(perm.value, v)
                && equal(old(perm).value, ret)
                && equal(self.view(), perm.patomic)
            );
            opens_invariants_none();

            return self.ato.swap(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        pub fn into_inner(self, #[proof] perm: $p_ident) -> $value_ty {
            requires([
                equal(self.view(), perm.patomic),
            ]);
            ensures(|ret: $value_ty| equal(perm.value, ret));
            opens_invariants_none();

            return self.ato.into_inner();
        }
    }
}

macro_rules! atomic_integer_methods {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident, $int_min:expr, $int_max:expr) => {
        // Note that wrapping-on-overflow is the defined behavior for fetch_add and fetch_sub
        // for Rust's atomics (in contrast to ordinary arithmetic)

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_add_wrapping(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == $wrap_add(old(perm).value, n)
            );
            opens_invariants_none();

            return self.ato.fetch_add(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_sub_wrapping(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == $wrap_sub(old(perm).value, n)
            );
            opens_invariants_none();

            return self.ato.fetch_sub(n, Ordering::SeqCst);
        }

        // fetch_add and fetch_sub are more natural in the common case that you
        // don't expect wrapping
        //
        // TODO fetch_add and fetch_sub could be verified, untrusted, in terms of
        // fetch_add_wrapping and fetch_sub_wrapping; however, right now we do not
        // support the #[verifier(atomic)] attribute on untrusted functions

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_add(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
                $int_min <= old(perm).value + n,
                old(perm).value + n <= $int_max,
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == old(perm).value + n
            );
            opens_invariants_none();

            return self.ato.fetch_add(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_sub(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
                $int_min <= old(perm).value - n,
                old(perm).value - n <= $int_max,
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == old(perm).value - n
            );
            opens_invariants_none();

            return self.ato.fetch_add(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_and(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == (old(perm).value & n)
            );
            opens_invariants_none();

            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_or(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == (old(perm).value | n)
            );
            opens_invariants_none();

            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_xor(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == (old(perm).value ^ n)
            );
            opens_invariants_none();

            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_nand(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == !(old(perm).value & n)
            );
            opens_invariants_none();

            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_max(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == (if old(perm).value > n { old(perm).value } else { n })
            );
            opens_invariants_none();

            return self.ato.fetch_max(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_min(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == (if old(perm).value < n { old(perm).value } else { n })
            );
            opens_invariants_none();

            return self.ato.fetch_min(n, Ordering::SeqCst);
        }
    }
}

macro_rules! atomic_bool_methods {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty) => {
        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_and(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == (old(perm).value && n)
            );
            opens_invariants_none();

            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_or(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == (old(perm).value || n)
            );
            opens_invariants_none();

            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_xor(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == ((old(perm).value && !n) || (!old(perm).value && n))
            );
            opens_invariants_none();

            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(atomic)]
        pub fn fetch_nand(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
            requires([
                equal(self.view(), old(perm).patomic),
            ]);
            ensures(|ret: $value_ty| equal(old(perm).value, ret)
                && perm.patomic == old(perm).patomic
                && perm.value == !(old(perm).value && n)
            );
            opens_invariants_none();

            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }
    }
}

make_bool_atomic!(PAtomicBool, PermissionBool, AtomicBool, bool);

make_unsigned_integer_atomic!(PAtomicU8, PermissionU8, AtomicU8, u8, wrapping_add_u8, wrapping_sub_u8, 0, 0xff);
make_unsigned_integer_atomic!(PAtomicU16, PermissionU16, AtomicU16, u16, wrapping_add_u16, wrapping_sub_u16, 0, 0xffff);
make_unsigned_integer_atomic!(PAtomicU32, PermissionU32, AtomicU32, u32, wrapping_add_u32, wrapping_sub_u32, 0, 0xffff_ffff);
make_unsigned_integer_atomic!(PAtomicU64, PermissionU64, AtomicU64, u64, wrapping_add_u64, wrapping_sub_u64, 0, 0xffff_ffff_ffff_ffff);

make_signed_integer_atomic!(PAtomicI8, PermissionI8, AtomicI8, i8, wrapping_add_i8, wrapping_sub_i8, -0x80, 0x7f);
make_signed_integer_atomic!(PAtomicI16, PermissionI16, AtomicI16, i16, wrapping_add_i16, wrapping_sub_i16, -0x8000, 0x7fff);
make_signed_integer_atomic!(PAtomicI32, PermissionI32, AtomicI32, i32, wrapping_add_i32, wrapping_sub_i32, -0x8000_0000, 0x7fff_ffff);
make_signed_integer_atomic!(PAtomicI64, PermissionI64, AtomicI64, i64, wrapping_add_i64, wrapping_sub_i64, -0x8000_0000_0000_0000, 0x7fff_ffff_ffff_ffff);

// TODO usize and isize (for this, we need to be able to use constants like usize::MAX)
