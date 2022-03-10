#![feature(maybe_uninit_ref)]

#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::option::*;
use pervasive::ptr::*;
use pervasive::cell::*;
use pervasive::modes::*;
use pervasive::invariants::*;

use state_machines_macros::concurrent_state_machine;

concurrent_state_machine!(Dupe<#[verifier(maybe_negative)] T> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(multiset)]
        pub reader: Multiset<T>,
    }

    #[init]
    fn initialize_one(&self, t: T) {
        // Initialize with a single reader
        init(storage, Option::Some(t));
        init(reader, Multiset::singleton(t));
    }

    #[invariant]
    fn agreement(&self) -> bool {
        forall(|x: T| self.reader.count(x) > 0 >>=
            equal(self.storage, Option::Some(x)))
    }

    #[transition]
    fn dupe(&self, t: T) {
        have_element(reader, t);
        add_element(reader, t);
    }

    #[readonly]
    fn borrow(&self, t: T) {
        have_element(reader, t);
        guard_some(storage, t);
    }

     #[inductive(initialize_one)]
     fn initialize_one_inductive(post: Dupe<T>, t: T) { }
 
     #[inductive(dupe)]
     fn dupe_inductive(self: Dupe<T>, post: Dupe<T>, t: T) { }
});

#[proof]
pub struct Duplicable<#[verifier(maybe_negative)] T> {
    #[proof] pub inst: Dupe_Instance<T>,
    #[proof] pub reader: Dupe_reader<T>,
}

impl<T> Duplicable<T> {
    #[spec]
    pub fn wf(self) -> bool {
        equal(self.reader.instance, self.inst)
    }

    #[spec]
    pub fn view(self) -> T {
        self.reader.value
    }

    #[proof]
    #[verifier(returns(proof))]
    pub fn new(#[proof] t: T) -> Self {
        ensures(|s: Self| s.wf() && equal(s.view(), t));

        #[proof] let (inst, mut readers) = Dupe_Instance::initialize_one(/* spec */ t, Option::Some(t));
        #[proof] let reader = readers.proof_remove(Dupe_reader { value: t, instance: inst });
        Duplicable {
            inst, reader
        }
    }

    #[proof]
    #[verifier(returns(proof))]
    pub fn clone(#[proof] &self) -> Self {
        requires(self.wf());
        ensures(|other: Self|
            other.wf() && equal(self.view(), other.view())
        );

        #[proof] let r = self.inst.dupe(self.reader.value, &self.reader);
        Duplicable { inst: self.inst.clone(), reader: r }
    }

    #[proof]
    #[verifier(returns(proof))]
    pub fn borrow(#[proof] &self) -> &T {
        requires(self.wf());
        ensures(|t: &T| equal(*t, self.view()));

        self.inst.borrow(self.reader.value, &self.reader)
    }
}

concurrent_state_machine!(RefCounter<#[verifier(maybe_negative)] T> {
    fields {
        #[sharding(variable)]
        pub counter: nat,

        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(multiset)]
        pub reader: Multiset<T>,
    }

    #[invariant]
    fn reader_agrees_storage(&self) -> bool {
        forall(|t: T| self.reader.count(t) > 0 >>=
            equal(self.storage, Option::Some(t)))
    }

    #[invariant]
    fn counter_agrees_storage(&self) -> bool {
        self.counter == 0 >>= self.storage.is_None()
    }

    #[invariant]
    fn counter_agrees_storage_rev(&self) -> bool {
        self.storage.is_None() >>= self.counter == 0
    }

    #[invariant]
    fn counter_agrees_reader_count(&self) -> bool {
        self.storage.is_Some() >>=
            self.reader.count(self.storage.get_Some_0()) == self.counter
    }


    #[init]
    fn initialize_empty(&self) {
        init(counter, 0);
        init(storage, Option::None);
        init(reader, Multiset::empty());
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: RefCounter<T>) { }
    
    #[transition]
    fn do_deposit(&self, x: T) {
        require(self.counter == 0);
        update(counter, 1);
        deposit_some(storage, x);
        add_element(reader, x);
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(self: RefCounter<T>, post: RefCounter<T>, x: T) { }

    #[readonly]
    fn reader_guard(&self, x: T) {
        have_element(reader, x);
        guard_some(storage, x);
    }

    #[transition]
    fn do_clone(&self, x: T) {
        have_element(reader, x);
        add_element(reader, x);
        update(counter, self.counter + 1);
    }

    #[inductive(do_clone)]
    fn do_clone_inductive(self: RefCounter<T>, post: RefCounter<T>, x: T) {
        assert(self.reader.count(x) > 0);
        assert(equal(self.storage, Option::Some(x)));
        assert(self.storage.is_Some());
        assert(self.counter > 0);
    }

    #[transition]
    fn dec_basic(&self, x: T) {
        require(self.counter >= 2);
        remove_element(reader, x);
        update(counter, self.counter - 1);
    }

    #[transition]
    fn dec_to_zero(&self, x: T) {
        remove_element(reader, x);
        require(self.counter < 2);
        assert(self.counter == 1);
        update(counter, 0);
        withdraw_some(storage, x);
    }

    #[inductive(dec_basic)]
    fn dec_basic_inductive(self: RefCounter<T>, post: RefCounter<T>, x: T) {
        assert(self.reader.count(x) > 0);
        assert(equal(self.storage, Option::Some(x)));
    }

    #[inductive(dec_to_zero)]
    fn dec_to_zero_inductive(self: RefCounter<T>, post: RefCounter<T>, x: T) { }
});

struct InnerRc<S> {
    pub rc_cell: PCell<u64>,
    pub s: S,
}

#[proof]
struct GhostStuff<S> {
    #[proof] pub rc_perm: cell::Permission<u64>,
    #[proof] pub rc_token: RefCounter_counter<ptr::Permission<InnerRc<S>>>,
}

impl<S> GhostStuff<S> {
    #[spec]
    fn wf(self, inst: RefCounter_Instance<ptr::Permission<InnerRc<S>>>, cell: PCell<u64>) -> bool {
        equal(self.rc_perm.pcell, cell.view())
        && equal(self.rc_token.instance, inst)
        && self.rc_perm.value.is_Some()
        && self.rc_perm.value.get_Some_0() as nat == self.rc_token.value
    }
}

impl<S> InnerRc<S> {
    #[spec]
    fn wf(self, cell: PCell<u64>) -> bool {
        equal(self.rc_cell, cell)
    }
}

struct MyRc<S> {
    #[proof] pub inst: RefCounter_Instance<ptr::Permission<InnerRc<S>>>,
    #[proof] pub inv: Duplicable<LocalInvariant<GhostStuff<S>>>,
    #[proof] pub reader: RefCounter_reader<ptr::Permission<InnerRc<S>>>,
    pub ptr: PPtr<InnerRc<S>>,
}

impl<S> MyRc<S> {
    #[spec]
    fn wf(self) -> bool {
        equal(self.reader.value.pptr, self.ptr.view())
        && equal(self.reader.instance, self.inst)
        && self.reader.value.value.is_Some()
        && self.inv.wf()
        && (forall(|g: GhostStuff<S>| self.inv.view().inv(g) ==
            g.wf(self.inst, self.reader.value.value.get_Some_0().rc_cell)))
    }

    #[spec]
    fn view(self) -> S {
        self.reader.value.value.get_Some_0().s
    }

    fn new(s: S) -> Self {
        ensures(|rc: MyRc<S>| [
            rc.wf(),
            equal(rc.view(), s),
        ]);

        let (rc_cell, Proof(mut rc_perm)) = PCell::new(1);
        let inner_rc = InnerRc::<S> { rc_cell, s };

        let (ptr, Proof(mut ptr_perm)) = PPtr::new(inner_rc);

        #[proof] let (inst, mut rc_token, _) = RefCounter_Instance::initialize_empty(Option::None);
        #[proof] let reader = inst.do_deposit(ptr_perm, &mut rc_token, ptr_perm);

        #[proof] let g = GhostStuff::<S> { rc_perm, rc_token };

        #[proof] let inv = LocalInvariant::new(g,
            |g: GhostStuff<S>|
                g.wf(reader.instance, reader.value.value.get_Some_0().rc_cell),
            0);
        #[proof] let inv = Duplicable::new(inv);

        MyRc { inst, inv, reader, ptr }
    }

    fn as_ref<'b>(&'b self) -> &'b S {
        requires(self.wf());
        ensures(|s: &'b S| equal(*s, self.view()));

        #[proof] let perm = self.inst.reader_guard(
            self.reader.value,
            &self.reader);
        &self.ptr.as_ref(perm).s
    }

    fn clone(&self) -> Self {
        requires(self.wf());
        ensures(|s: Self| s.wf() && equal(s.view(), self.view()));

        #[proof] let perm = self.inst.reader_guard(
            self.reader.value,
            &self.reader);
        let inner_rc_ref = &self.ptr.as_ref(perm);

        #[proof] let mut new_reader;
        open_local_invariant!(self.inv.borrow() => g => {
            #[proof] let GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

            let count = inner_rc_ref.rc_cell.take(&mut rc_perm);

            assume(count < 100000000);

            let count = count + 1;
            inner_rc_ref.rc_cell.put(&mut rc_perm, count);

            new_reader = self.inst.do_clone(
                self.reader.value,
                &mut rc_token,
                &self.reader);
                
            g = GhostStuff { rc_perm, rc_token };
        });

        MyRc {
            inst: self.inst.clone(),
            inv: self.inv.clone(),
            reader: new_reader,
            ptr: self.ptr.clone(),
        }
    }

    fn dispose(self) {
        requires(self.wf());

        let MyRc { inst, inv, reader, ptr } = self;

        #[proof] let perm = inst.reader_guard(
            reader.value,
            &reader);
        let inner_rc_ref = &ptr.as_ref(perm);

        open_local_invariant!(inv.borrow() => g => {
            #[proof] let GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

            let count = inner_rc_ref.rc_cell.take(&mut rc_perm);
            if count >= 2 {
                let count = count - 1;
                inner_rc_ref.rc_cell.put(&mut rc_perm, count);

                inst.dec_basic(
                    reader.value,
                    &mut rc_token,
                    reader);
            } else {
                #[proof] let mut inner_rc_perm = inst.dec_to_zero(
                    reader.value,
                    &mut rc_token,
                    reader);

                let inner_rc = ptr.take(&mut inner_rc_perm);

                // we still have to write back to the `inner_rc` to restore the invariant
                // even though inner_rc has been moved onto the stack here.
                // so this will probably get optimized out
                let count = count - 1;
                inner_rc.rc_cell.put(&mut rc_perm, count);

                ptr.dispose(inner_rc_perm);
            }

            g = GhostStuff { rc_perm, rc_token };
        });
    }
}

fn main() { }
