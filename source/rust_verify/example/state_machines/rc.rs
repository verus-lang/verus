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

// TODO make S generic (this requires a trait bound `S: &'static`)
struct S {
    s: u8,
}

struct InnerRc {
    pub rc_cell: PCell<u64>,
    pub s: S,
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

#[proof]
struct GhostStuff {
    #[proof] pub rc_perm: cell::Permission<u64>,
    #[proof] pub rc_token: RefCounter_counter<ptr::Permission<InnerRc>>,
}

impl GhostStuff {
    #[spec]
    fn wf(self, inst: RefCounter_Instance<ptr::Permission<InnerRc>>, cell: PCell<u64>) -> bool {
        equal(self.rc_perm.pcell, cell.view())
        && equal(self.rc_token.instance, inst)
        && self.rc_perm.value.is_Some()
        && self.rc_perm.value.get_Some_0() as nat == self.rc_token.counter
    }
}

impl InnerRc {
    #[spec]
    fn wf(self, cell: PCell<u64>) -> bool {
        equal(self.rc_cell, cell)
    }
}


struct MyRc {
    #[proof] pub inst: RefCounter_Instance<ptr::Permission<InnerRc>>,
    #[proof] pub inv: &'static LocalInvariant<GhostStuff>,
    #[proof] pub reader: RefCounter_reader<ptr::Permission<InnerRc>>,
    pub ptr: PPtr<InnerRc>,
}

impl MyRc {
    #[spec]
    fn wf(self) -> bool {
        equal(self.reader.reader.pptr, self.ptr.view())
        && equal(self.reader.instance, self.inst)
        && self.reader.reader.value.is_Some()
        && (forall(|g: GhostStuff| self.inv.inv(g) ==
            g.wf(self.inst, self.reader.reader.value.get_Some_0().rc_cell)))
    }

    #[spec]
    fn view(self) -> S {
        self.reader.reader.value.get_Some_0().s
    }

    fn new(s: S) -> MyRc {
        ensures(|rc: MyRc| [
            rc.wf(),
            equal(rc.view(), s),
        ]);

        let (rc_cell, Proof(mut rc_perm)) = PCell::empty();
        rc_cell.put(1, &mut rc_perm);
        let inner_rc = InnerRc { rc_cell, s };

        let (ptr, Proof(mut ptr_perm)) = PPtr::empty();
        ptr.put(inner_rc, &mut ptr_perm);

        #[proof] let (inst, mut rc_token) = RefCounter_initialize_empty();
        #[proof] let reader = RefCounter_do_deposit(inst.clone(), ptr_perm, &mut rc_token, ptr_perm);

        #[proof] let g = GhostStuff { rc_perm, rc_token };

        #[proof] let inv = LocalInvariant::new(g,
            |g: GhostStuff|
                g.wf(reader.instance, reader.reader.value.get_Some_0().rc_cell),
            0);
        #[proof] let inv = inv.to_static_ref();

        MyRc { inst, inv, reader, ptr }
    }

    fn as_ref<'a>(&'a self) -> &'a S {
        requires(self.wf());
        ensures(|s: &'a S| equal(*s, self.view()));

        #[proof] let perm = RefCounter_reader_guard(
            self.inst.clone(),
            self.reader.reader,
            &self.reader);
        &self.ptr.as_ref(perm).s
    }

    fn clone(&self) -> Self {
        requires(self.wf());
        ensures(|s: Self| s.wf() && equal(s.view(), self.view()));

        #[proof] let perm = RefCounter_reader_guard(
            self.inst.clone(),
            self.reader.reader,
            &self.reader);
        let inner_rc_ref = &self.ptr.as_ref(perm);

        #[proof] let mut new_reader;
        open_local_invariant!(&self.inv => g => {
            #[proof] let GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

            let count = inner_rc_ref.rc_cell.take(&mut rc_perm);

            assume(count < 100000000);

            let count = count + 1;
            inner_rc_ref.rc_cell.put(count, &mut rc_perm);

            new_reader = RefCounter_do_clone(self.inst.clone(),
                self.reader.reader,
                &mut rc_token,
                &self.reader);
                
            g = GhostStuff { rc_perm, rc_token };
        });

        MyRc {
            inst: self.inst.clone(),
            inv: self.inv,
            reader: new_reader,
            ptr: self.ptr.clone(),
        }
    }

    fn dispose(self) {
        requires(self.wf());

        let MyRc { inst, inv, reader, ptr } = self;

        #[proof] let perm = RefCounter_reader_guard(
            inst.clone(),
            reader.reader,
            &reader);
        let inner_rc_ref = &ptr.as_ref(perm);

        open_local_invariant!(&inv => g => {
            #[proof] let GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

            let count = inner_rc_ref.rc_cell.take(&mut rc_perm);
            if count >= 2 {
                let count = count - 1;
                inner_rc_ref.rc_cell.put(count, &mut rc_perm);

                RefCounter_dec_basic(inst.clone(),
                    reader.reader,
                    &mut rc_token,
                    reader);
            } else {
                #[proof] let mut inner_rc_perm = RefCounter_dec_to_zero(inst.clone(),
                    reader.reader,
                    &mut rc_token,
                    reader);

                let inner_rc = ptr.take(&mut inner_rc_perm);

                // we still have to write back to the `inner_rc` to restore the invariant
                // even though inner_rc has been moved onto the stack here.
                // so this will probably get optimized out
                let count = count - 1;
                inner_rc.rc_cell.put(count, &mut rc_perm);

                ptr.dispose(inner_rc_perm);
            }

            g = GhostStuff { rc_perm, rc_token };
        });
    }
}

fn main() { }
