use std::sync::atomic::{AtomicU32, Ordering};

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

// TODO support all the different integer types

macro_rules! make_atomic {
    ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
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
            #[spec]
            fn is_for(&self, patomic: $at_ident) -> bool {
                self.patomic == patomic.view()
            }

            #[spec]
            fn points_to(&self, v: $value_ty) -> bool {
                self.value == v
            }
        }

        impl $at_ident {
            #[verifier(pub_abstract)]
            #[spec]
            pub fn view(&self) -> int {
                arbitrary()
            }

            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: $value_ty) -> ($at_ident, Proof<$p_ident>) {
                ensures(|res : ($at_ident, Proof<$p_ident>)|
                    equal(res.1, proof($p_ident{ patomic: res.0.view(), value: i }))
                );

                let p = $at_ident { ato: <$rust_ty>::new(i) };
                #[proof] let t = proof_from_false();
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

            // TODO uncomment these once Verus supports `Result`
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            /*
            pub fn compare_exchange(&self, #[proof] perm: &mut $p_ident, current: $value_ty, new: $value_ty) -> Result<$value_ty, $value_ty> {
                requires([
                    equal(self.view(), old(perm).patomic),
                ]);
                ensures(|ret: Result<$value_ty, $value_ty>|
                    equal(self.view(), perm.patomic)
                    && match ret {
                        Ok(r) =>
                               current == old(perm).value
                            && equal(perm.value, new)
                            && equal(r, old(perm).value),
                        Err(r) =>
                               current != old(perm).value
                            && equal(perm.value, old(perm).value)
                            && equal(r, old(perm).value),
                    }
                );
                opens_invariants_none();

                return self.ato.compare_exchange(current, new, Ordering::SeqCst, Ordering::SeqCst);
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
                        Ok(r) =>
                               current == old(perm).value
                            && equal(perm.value, new)
                            && equal(r, old(perm).value),
                        Err(r) =>
                               equal(perm.value, old(perm).value)
                            && equal(r, old(perm).value),
                    }
                );
                opens_invariants_none();

                return self.ato.compare_exchange_weak(current, new, Ordering::SeqCst, Ordering::SeqCst);
            }
            */

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

            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, #[proof] perm: &mut $p_ident, n: $value_ty) -> $value_ty {
                requires([
                    equal(self.view(), old(perm).patomic),
                ]);
                ensures(|ret: $value_ty| equal(old(perm).value, ret)
                    && perm.patomic == old(perm).patomic
                    && perm.value == old(perm).value & n
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
                    && perm.value == old(perm).value | n
                );
                opens_invariants_none();

                return self.ato.fetch_or(n, Ordering::SeqCst);
            }

            // TODO uncomment this once Verus supports bitwise negation
            /*
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
            */

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
}

#[spec]
pub fn wrapping_add_u32(a: int, b: int) -> int {
    if a + b >= 0x100000000 {
        a + b - 0x100000000
    } else {
        a + b
    }
}

#[spec]
pub fn wrapping_sub_u32(a: int, b: int) -> int {
    if a - b < 0 {
        a - b + 0x100000000
    } else {
        a - b
    }
}

make_atomic!(PAtomicU32, PermissionU32, AtomicU32, u32, wrapping_add_u32, wrapping_sub_u32);
