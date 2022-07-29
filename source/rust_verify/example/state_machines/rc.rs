#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::option::*;
use pervasive::ptr::*;
use pervasive::cell::*;
use pervasive::modes::*;
use pervasive::invariant::*;

use state_machines_macros::tokenized_state_machine;

tokenized_state_machine!(Dupe<T> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(multiset)]
        pub reader: Multiset<T>,
    }

    init!{
        initialize_one(t: T) {
            // Initialize with a single reader
            init storage = Option::Some(t);
            init reader = Multiset::singleton(t);
        }
    }

    #[invariant]
    pub fn agreement(&self) -> bool {
        forall(|x: T| self.reader.count(x) > 0 >>=
            equal(self.storage, Option::Some(x)))
    }

    transition!{
        dupe(t: T) {
            have reader >= {t};
            add reader += {t};
        }
    }

    property!{
        borrow(t: T) {
            have reader >= {t};
            guard storage >= Some(t);
        }
    }

     #[inductive(initialize_one)]
     fn initialize_one_inductive(post: Self, t: T) { }
 
     #[inductive(dupe)]
     fn dupe_inductive(pre: Self, post: Self, t: T) { }
});

#[proof]
pub struct Duplicable<T> {
    #[proof] pub inst: Dupe::Instance<T>,
    #[proof] pub reader: Dupe::reader<T>,
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

        #[proof] let (inst, mut readers) = Dupe::Instance::initialize_one(/* spec */ t, Option::Some(t));
        #[proof] let reader = readers.tracked_remove(Dupe::reader { value: t, instance: inst });
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

tokenized_state_machine!(RefCounter<#[verifier(maybe_negative)] T> {
    fields {
        #[sharding(variable)]
        pub counter: nat,

        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(multiset)]
        pub reader: Multiset<T>,
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall(|t: T| self.reader.count(t) > 0 >>=
            equal(self.storage, Option::Some(t)))
    }

    #[invariant]
    pub fn counter_agrees_storage(&self) -> bool {
        self.counter == 0 >>= self.storage.is_None()
    }

    #[invariant]
    pub fn counter_agrees_storage_rev(&self) -> bool {
        self.storage.is_None() >>= self.counter == 0
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.storage.is_Some() >>=
            self.reader.count(self.storage.get_Some_0()) == self.counter
    }

    init!{
        initialize_empty() {
            init counter = 0;
            init storage = Option::None;
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: Self) { }
    
    transition!{
        do_deposit(x: T) {
            require(pre.counter == 0);
            update counter = 1;
            deposit storage += Some(x);
            add reader += {x};
        }
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(pre: Self, post: Self, x: T) { }

    property!{
        reader_guard(x: T) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    transition!{
        do_clone(x: T) {
            have reader >= {x};
            add reader += {x};
            update counter = pre.counter + 1;
        }
    }

    #[inductive(do_clone)]
    fn do_clone_inductive(pre: Self, post: Self, x: T) {
        assert(pre.reader.count(x) > 0);
        assert(equal(pre.storage, Option::Some(x)));
        assert(pre.storage.is_Some());
        assert(pre.counter > 0);
    }

    transition!{
        dec_basic(x: T) {
            require(pre.counter >= 2);
            remove reader -= {x};
            update counter = (pre.counter - 1) as nat;
        }
    }

    transition!{
        dec_to_zero(x: T) {
            remove reader -= {x};
            require(pre.counter < 2);
            assert(pre.counter == 1);
            update counter = 0;
            withdraw storage -= Some(x);
        }
    }

    #[inductive(dec_basic)]
    fn dec_basic_inductive(pre: Self, post: Self, x: T) {
        assert(pre.reader.count(x) > 0);
        assert(equal(pre.storage, Option::Some(x)));
    }

    #[inductive(dec_to_zero)]
    fn dec_to_zero_inductive(pre: Self, post: Self, x: T) { }
});

struct InnerRc<S> {
    pub rc_cell: PCell<u64>,
    pub s: S,
}

#[proof]
struct GhostStuff<S> {
    #[proof] pub rc_perm: cell::Permission<u64>,
    #[proof] pub rc_token: RefCounter::counter<ptr::Permission<InnerRc<S>>>,
}

impl<S> GhostStuff<S> {
    #[spec]
    fn wf(self, inst: RefCounter::Instance<ptr::Permission<InnerRc<S>>>, cell: PCell<u64>) -> bool {
        equal(self.rc_perm.pcell, cell.id())
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
    #[proof] pub inst: RefCounter::Instance<ptr::Permission<InnerRc<S>>>,
    #[proof] pub inv: Duplicable<LocalInvariant<GhostStuff<S>>>,
    #[proof] pub reader: RefCounter::reader<ptr::Permission<InnerRc<S>>>,
    pub ptr: PPtr<InnerRc<S>>,
}

impl<S> MyRc<S> {
    #[spec]
    fn wf(self) -> bool {
        equal(self.reader.value.pptr, self.ptr.id())
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

        let (rc_cell, rc_perm) = PCell::new(1);
        let inner_rc = InnerRc::<S> { rc_cell, s };

        let (ptr, ptr_perm) = PPtr::new(inner_rc);

        #[proof] let (inst, mut rc_token, _) = RefCounter::Instance::initialize_empty(Option::None);
        
        #[proof] let ptr_perm = tracked_get(ptr_perm);
        #[proof] let reader = inst.do_deposit(ptr_perm, &mut rc_token, ptr_perm);

        #[proof] let g = GhostStuff::<S> { rc_perm: tracked_get(rc_perm), rc_token };

        #[proof] let inv = LocalInvariant::new(g,
            |g: GhostStuff<S>|
                g.wf(reader.instance, reader.value.value.get_Some_0().rc_cell),
            0);
        #[proof] let inv = Duplicable::new(inv);

        MyRc { inst, inv, reader, ptr }
    }

    fn borrow<'b>(&'b self) -> &'b S {
        requires(self.wf());
        ensures(|s: &'b S| equal(*s, self.view()));

        #[proof] let perm = self.inst.reader_guard(
            self.reader.value,
            &self.reader);
        &self.ptr.borrow(tracked_exec_borrow(perm)).s
    }

    fn clone(&self) -> Self {
        requires(self.wf());
        ensures(|s: Self| s.wf() && equal(s.view(), self.view()));

        #[proof] let perm = self.inst.reader_guard(
            self.reader.value,
            &self.reader);
        let inner_rc_ref = &self.ptr.borrow(tracked_exec_borrow(perm));

        #[proof] let new_reader;
        open_local_invariant!(self.inv.borrow() => g => {
            #[proof] let GhostStuff { rc_perm: rc_perm, rc_token: mut rc_token } = g;
            let mut rc_perm = tracked_exec(rc_perm);

            let count = inner_rc_ref.rc_cell.take(&mut rc_perm);

            assume(count < 100000000);

            let count = count + 1;
            inner_rc_ref.rc_cell.put(&mut rc_perm, count);

            new_reader = self.inst.do_clone(
                self.reader.value,
                &mut rc_token,
                &self.reader);
                
            g = GhostStuff { rc_perm: tracked_get(rc_perm), rc_token };
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
        let inner_rc_ref = &ptr.borrow(tracked_exec_borrow(perm));

        open_local_invariant!(inv.borrow() => g => {
            #[proof] let GhostStuff { rc_perm: rc_perm, rc_token: mut rc_token } = g;
            let mut rc_perm = tracked_exec(rc_perm);

            let count = inner_rc_ref.rc_cell.take(&mut rc_perm);
            if count >= 2 {
                let count = count - 1;
                inner_rc_ref.rc_cell.put(&mut rc_perm, count);

                inst.dec_basic(
                    reader.value,
                    &mut rc_token,
                    reader);
            } else {
                #[proof] let inner_rc_perm = inst.dec_to_zero(
                    reader.value,
                    &mut rc_token,
                    reader);
                let mut inner_rc_perm = tracked_exec(inner_rc_perm);

                let inner_rc = ptr.take(&mut inner_rc_perm);

                // we still have to write back to the `inner_rc` to restore the invariant
                // even though inner_rc has been moved onto the stack here.
                // so this will probably get optimized out
                let count = count - 1;
                inner_rc.rc_cell.put(&mut rc_perm, count);

                ptr.dispose(inner_rc_perm);
            }

            g = GhostStuff { rc_perm: tracked_get(rc_perm), rc_token };
        });
    }
}

fn main() { }
