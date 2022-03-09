use std::cell::UnsafeCell;
use std::mem::MaybeUninit;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

// TODO Identifier should be some opaque type, not necessarily an int

// TODO implement: borrow, borrow_mut, take, swap, read_copy

// TODO figure out how Drop should work

//type Identifier = int;

#[verifier(external_body)]
pub struct PCell<#[verifier(strictly_positive)] V> {
    ucell: UnsafeCell<MaybeUninit<V>>,
}

#[proof]
#[verifier(unforgeable)]
pub struct Permission<V> {
    #[spec] pub pcell: int,
    #[spec] pub value: option::Option<V>,
}

impl<V> PCell<V> {
    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (PCell<V>, Proof<Permission<V>>) {
        ensures(|pt : (PCell<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pcell: pt.0.view(), value: option::Option::None }))
        );

        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
        let Proof(t) = exec_proof_from_false();
        (p, Proof(t))
    }

    fndecl!(pub fn view(&self) -> int);

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, #[proof] perm: &mut Permission<V>, v: V) {
        requires([
            equal(self.view(), old(perm).pcell),
            equal(old(perm).value, option::Option::None),
        ]);
        ensures(
            equal(perm.pcell, old(perm).pcell) &&
            equal(perm.value, option::Option::Some(v))
        );
        opens_invariants_none();

        unsafe {
            *(self.ucell.get()) = MaybeUninit::new(v);
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, #[proof] perm: &mut Permission<V>) -> V {
        requires([
            equal(self.view(), old(perm).pcell),
            old(perm).value.is_Some(),
        ]);
        ensures(|v: V| [
            equal(perm.pcell, old(perm).pcell),
            equal(perm.value, option::Option::None),
            equal(v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::uninit();
            std::mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, #[proof] perm: &mut Permission<V>, in_v: V) -> V {
        requires([
            equal(self.view(), old(perm).pcell),
            old(perm).value.is_Some(),
        ]);
        ensures(|out_v: V| [
            equal(perm.pcell, old(perm).pcell),
            equal(perm.value, option::Option::Some(in_v)),
            equal(out_v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::new(in_v);
            std::mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn as_ref<'a>(&self, #[proof] perm: &'a Permission<V>) -> &'a V {
        requires([
            equal(self.view(), perm.pcell),
            perm.value.is_Some(),
        ]);
        ensures(|v: V|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();

        unsafe {
            (*self.ucell.get()).assume_init_ref()
        }
    }

    //////////////////////////////////
    // Untrusted functions below here

    #[inline(always)]
    pub fn into_inner(self, #[proof] perm: Permission<V>) -> V {
        requires([
            equal(self.view(), perm.pcell),
            perm.value.is_Some(),
        ]);
        ensures(|v|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();

        #[proof] let mut perm = perm;
        self.take(&mut perm)
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn new(v: V) -> (PCell<V>, Proof<Permission<V>>) {
        ensures(|pt : (PCell<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pcell: pt.0.view(), value: option::Option::Some(v) }))
        );

        let (p, Proof(mut t)) = Self::empty();
        p.put(&mut t, v);
        (p, Proof(t))
    }
}
