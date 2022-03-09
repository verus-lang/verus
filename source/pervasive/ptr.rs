use std::ptr::NonNull;
use std::mem::MaybeUninit;
use std::alloc::{Layout};
use std::alloc::{dealloc};

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

/// PPtr ("i.e., permissioned pointer").
///
/// This is similar to PCell, but has a few key differences:
///  * In PCell<T>, the type T is placed internally to the PCell, whereas with PPtr,
///    the type T is placed at some location on the heap.
///  * Since PPtr is just a pointer (represented by an integer), it can be `Copy`
///  * The `ptr::Permission` token represents not just the permission to read/write
///    the contents, but also to deallocate.


// TODO implement: borrow_mut, Drop

// TODO Identifier should be some opaque type, not necessarily an int
//type Identifier = int;

#[verifier(external_body)]
pub struct PPtr<#[verifier(strictly_positive)] V> {
    uptr: NonNull<MaybeUninit<V>>,
}

#[proof]
#[verifier(unforgeable)]
pub struct Permission<V> {
    #[spec] pub pptr: int,
    #[spec] pub value: option::Option<V>,
}

impl<V> PPtr<V> {
    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (PPtr<V>, Proof<Permission<V>>) {
        ensures(|pt : (PPtr<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pptr: pt.0.view(), value: option::Option::None }))
        );
        opens_invariants_none();

        let p = PPtr {
            uptr: Box::leak(box MaybeUninit::uninit()).into(),
        };
        let Proof(t) = exec_proof_from_false();
        (p, Proof(t))
    }

    fndecl!(pub fn view(&self) -> int);

    #[inline(always)]
    #[verifier(external_body)]
    pub fn clone(&self) -> PPtr<V> {
        ensures(|pt: PPtr<V>| equal(pt.view(), self.view()));
        opens_invariants_none();

        PPtr { uptr: self.uptr }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, #[proof] perm: &mut Permission<V>, v: V) {
        requires([
            equal(self.view(), old(perm).pptr),
            equal(old(perm).value, option::Option::None),
        ]);
        ensures([
            equal(perm.pptr, old(perm).pptr),
            equal(perm.value, option::Option::Some(v)),
        ]);
        opens_invariants_none();

        unsafe {
            *(self.uptr.as_ptr()) = MaybeUninit::new(v);
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, #[proof] perm: &mut Permission<V>) -> V {
        requires([
            equal(self.view(), old(perm).pptr),
            old(perm).value.is_Some(),
        ]);
        ensures(|v: V| [
            equal(perm.pptr, old(perm).pptr),
            equal(perm.value, option::Option::None),
            equal(v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::uninit();
            std::mem::swap(&mut m, &mut *self.uptr.as_ptr());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, #[proof] perm: &mut Permission<V>, in_v: V) -> V {
        requires([
            equal(self.view(), old(perm).pptr),
            old(perm).value.is_Some(),
        ]);
        ensures(|out_v: V| [
            equal(perm.pptr, old(perm).pptr),
            equal(perm.value, option::Option::Some(in_v)),
            equal(out_v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::new(in_v);
            std::mem::swap(&mut m, &mut *self.uptr.as_ptr());
            m.assume_init()
        }
    }

    /// Note that `self` is just a pointer, so it doesn't need to outlive 
    /// the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn as_ref<'a>(&self, #[proof] perm: &'a Permission<V>) -> &'a V {
        requires([
            equal(self.view(), perm.pptr),
            perm.value.is_Some(),
        ]);
        ensures(|v: V|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();
        
        unsafe {
            self.uptr.as_ref().assume_init_ref()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn dispose(&self, #[proof] perm: Permission<V>) {
        requires([
            equal(self.view(), perm.pptr),
            equal(perm.value, option::Option::None),
        ]);
        opens_invariants_none();

        dealloc(self.uptr.cast().as_ptr(), Layout::for_value(self.uptr.as_ref()));
    }

    //////////////////////////////////
    // Untrusted functions below here

    #[inline(always)]
    pub fn into_inner(self, #[proof] perm: Permission<V>) -> V {
        requires([
            equal(self.view(), perm.pptr),
            perm.value.is_Some(),
        ]);
        ensures(|v|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();

        #[proof] let mut perm = perm;
        let v = self.take(&mut perm);
        self.dispose(perm);
        v
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn new(v: V) -> (PPtr<V>, Proof<Permission<V>>) {
        ensures(|pt : (PPtr<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pptr: pt.0.view(), value: option::Option::Some(v) }))
        );

        let (p, Proof(mut t)) = Self::empty();
        p.put(&mut t, v);
        (p, Proof(t))
    }
}
