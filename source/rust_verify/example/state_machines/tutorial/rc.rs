#![allow(unused_imports)]

// ANCHOR: full
use builtin::*;
use builtin_macros::*;
use vstd::{*, pervasive::*};
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::cell::*;
use vstd::modes::*;
use vstd::invariant::*;
use state_machines_macros::tokenized_state_machine;

verus!{

tokenized_state_machine!(Dupe<T> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(constant)]
        pub val: T,
    }

    init!{
        initialize_one(t: T) {
            // Initialize with a single reader
            init storage = Option::Some(t);
            init val = t;
        }
    }

    #[invariant]
    pub fn agreement(&self) -> bool {
        self.storage == Option::Some(self.val)
    }

    property!{
        borrow() {
            guard storage >= Some(pre.val);
        }
    }

     #[inductive(initialize_one)]
     fn initialize_one_inductive(post: Self, t: T) { }
});

pub tracked struct Duplicable<T> {
    pub tracked inst: Dupe::Instance<T>,
}

impl<T> Duplicable<T> {
    pub open spec fn wf(self) -> bool {
        true
    }

    pub open spec fn view(self) -> T {
        self.inst.val()
    }

    pub proof fn new(tracked t: T) -> (tracked s: Self)
        ensures s.wf() && s@ == t,
    {
        let tracked inst = Dupe::Instance::initialize_one(/* spec */ t, Option::Some(t));
        Duplicable {
            inst,
        }
    }

    pub proof fn clone(tracked &self) -> (tracked other: Self)
        requires self.wf(),
        ensures other.wf() && self@ == other@,
    {
        Duplicable { inst: self.inst.clone() }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        requires self.wf(),
        ensures *t == self@,
    {
        self.inst.borrow()
    }
}

// ANCHOR: fields
tokenized_state_machine!(RefCounter<Perm> {
    fields {
        #[sharding(variable)]
        pub counter: nat,

        #[sharding(storage_option)]
        pub storage: Option<Perm>,

        #[sharding(multiset)]
        pub reader: Multiset<Perm>,
    }
// ANCHOR_END: fields

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: Perm| self.reader.count(t) > 0 ==>
            self.storage == Option::Some(t)
    }

    #[invariant]
    pub fn counter_agrees_storage(&self) -> bool {
        self.counter == 0 ==> self.storage.is_None()
    }

    #[invariant]
    pub fn counter_agrees_storage_rev(&self) -> bool {
        self.storage.is_None() ==> self.counter == 0
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.storage.is_Some() ==>
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
        do_deposit(x: Perm) {
            require(pre.counter == 0);
            update counter = 1;
            deposit storage += Some(x);
            add reader += {x};
        }
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(pre: Self, post: Self, x: Perm) { }

    property!{
        reader_guard(x: Perm) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    transition!{
        do_clone(x: Perm) {
            have reader >= {x};
            add reader += {x};
            update counter = pre.counter + 1;
        }
    }

    #[inductive(do_clone)]
    fn do_clone_inductive(pre: Self, post: Self, x: Perm) {
        assert(pre.reader.count(x) > 0);
        assert(pre.storage == Option::Some(x));
        assert(pre.storage.is_Some());
        assert(pre.counter > 0);
    }

    transition!{
        dec_basic(x: Perm) {
            require(pre.counter >= 2);
            remove reader -= {x};
            update counter = (pre.counter - 1) as nat;
        }
    }

    transition!{
        dec_to_zero(x: Perm) {
            remove reader -= {x};
            require(pre.counter < 2);
            assert(pre.counter == 1);
            update counter = 0;
            withdraw storage -= Some(x);
        }
    }

    #[inductive(dec_basic)]
    fn dec_basic_inductive(pre: Self, post: Self, x: Perm) {
        assert(pre.reader.count(x) > 0);
        assert(pre.storage == Option::Some(x));
    }

    #[inductive(dec_to_zero)]
    fn dec_to_zero_inductive(pre: Self, post: Self, x: Perm) { }
});

struct InnerRc<S> {
    pub rc_cell: PCell<u64>,
    pub s: S,
}

type MemPerms<S> = (ptr::PointsTo<InnerRc<S>>, ptr::Dealloc<InnerRc<S>>);

tracked struct GhostStuff<S> {
    pub tracked rc_perm: cell::PointsTo<u64>,
    pub tracked rc_token: RefCounter::counter<MemPerms<S>>,
}

impl<S> GhostStuff<S> {
    pub open spec fn wf(self, inst: RefCounter::Instance<MemPerms<S>>, cell: PCell<u64>) -> bool {
        &&& self.rc_perm@.pcell == cell.id()
        &&& self.rc_token@.instance == inst
        &&& self.rc_perm@.value.is_Some()
        &&& self.rc_perm@.value.get_Some_0() as nat == self.rc_token@.value
    }
}

impl<S> InnerRc<S> {
    spec fn wf(self, cell: PCell<u64>) -> bool {
        self.rc_cell == cell
    }
}

struct_with_invariants!{
    struct MyRc<S> {
        pub inst: Tracked< RefCounter::Instance<MemPerms<S>> >,
        pub inv: Tracked< Duplicable<LocalInvariant<_, GhostStuff<S>, _>> >,
        pub reader: Tracked< RefCounter::reader<MemPerms<S>> >,

        pub ptr: PPtr<InnerRc<S>>,

        pub rc_cell: Ghost< PCell<u64> >,
    }

    spec fn wf(self) -> bool {
        predicate {
            &&& self.reader@@.key.0@.pptr == self.ptr.id()
            &&& self.reader@@.key.1@.pptr == self.ptr.id()

            &&& self.reader@@.instance == self.inst@
            &&& self.reader@@.count == 1
            &&& self.reader@@.key.0@.value.is_Some()
            &&& self.inv@.wf()
            &&& self.reader@@.key.0@.value.get_Some_0().rc_cell == self.rc_cell
        }

        invariant on inv with (inst, rc_cell)
            specifically (self.inv@@)
            is (v: GhostStuff<S>)
        {
            v.wf(inst@, rc_cell@)
        }
    }
}

impl<S> MyRc<S> {
    spec fn view(self) -> S {
        self.reader@@.key.0@.value.get_Some_0().s
    }

    fn new(s: S) -> (rc: Self)
        ensures
            rc.wf(),
            rc@ == s,
    {
        let (rc_cell, Tracked(rc_perm)) = PCell::new(1);
        let inner_rc = InnerRc::<S> { rc_cell, s };

        let (ptr, Tracked(ptr_perm), Tracked(dealloc_perm)) = PPtr::new(inner_rc);

        let tracked (Tracked(inst), Tracked(mut rc_token), _) = RefCounter::Instance::initialize_empty(Option::None);
        let tracked reader = inst.do_deposit((ptr_perm, dealloc_perm), &mut rc_token, (ptr_perm, dealloc_perm));
        let tracked g = GhostStuff::<S> { rc_perm, rc_token };

        let tr_inst = Tracked(inst);
        let gh_cell = Ghost(rc_cell);

        let tracked inv = LocalInvariant::new((tr_inst, gh_cell), g, 0);
        let tracked inv = Duplicable::new(inv);

        MyRc {
            inst: tr_inst, inv: Tracked(inv), reader: Tracked(reader),
            ptr,
            rc_cell: gh_cell,
        }
    }

    fn borrow<'b>(&'b self) -> (s: &'b S)
        requires self.wf(),
        ensures *s == self@,
    {
        let tracked inst = self.inst.borrow();
        let tracked reader = self.reader.borrow();
        let tracked perm = inst.reader_guard(reader@.key, &reader);
        &self.ptr.borrow(Tracked(&perm.0)).s
    }

    fn clone(&self) -> (s: Self)
        requires self.wf(),
        ensures s.wf() && s@ == self@,
    {
        let tracked inst = self.inst.borrow();
        let tracked reader = self.reader.borrow();

        let tracked perm = inst.reader_guard(reader@.key, &reader);
        let inner_rc_ref = self.ptr.borrow(Tracked(&perm.0));

        let tracked new_reader;
        open_local_invariant!(self.inv.borrow().borrow() => g => {
            let tracked GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

            let count = inner_rc_ref.rc_cell.take(Tracked(&mut rc_perm));

            assume(count < 100000000);

            let count = count + 1;
            inner_rc_ref.rc_cell.put(Tracked(&mut rc_perm), count);

            proof {
                new_reader = self.inst.borrow().do_clone(
                    reader@.key,
                    &mut rc_token,
                    &reader);
            }
                
            proof { g = GhostStuff { rc_perm, rc_token }; }
        });

        MyRc {
            inst: Tracked(self.inst.borrow().clone()),
            inv: Tracked(self.inv.borrow().clone()),
            reader: Tracked(new_reader),
            ptr: self.ptr,
            rc_cell: Ghost(self.rc_cell@),
        }
    }

    fn dispose(self)
        requires self.wf(),
    {
        let MyRc { inst: Tracked(inst), inv: Tracked(inv), reader: Tracked(reader), ptr, rc_cell: _ } = self;

        let tracked perm = inst.reader_guard(
            reader@.key,
            &reader);

        let inner_rc_ref = &ptr.borrow(Tracked(&perm.0));

        open_local_invariant!(inv.borrow() => g => {
            let tracked GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

            let count = inner_rc_ref.rc_cell.take(Tracked(&mut rc_perm));
            if count >= 2 {
                let count = count - 1;
                inner_rc_ref.rc_cell.put(Tracked(&mut rc_perm), count);

                proof {
                    inst.dec_basic(
                        reader.view().key,
                        &mut rc_token,
                        reader);
                }
            } else {
                let tracked (mut inner_rc_perm, inner_rc_dealloc) = inst.dec_to_zero(
                    reader.view().key,
                    &mut rc_token,
                    reader);

                let inner_rc = ptr.take(Tracked(&mut inner_rc_perm));

                // we still have to write back to the `inner_rc` to restore the invariant
                // even though inner_rc has been moved onto the stack here.
                // so this will probably get optimized out
                let count = count - 1;
                inner_rc.rc_cell.put(Tracked(&mut rc_perm), count);

                ptr.dispose(Tracked(inner_rc_perm), Tracked(inner_rc_dealloc));
            }

            proof { g = GhostStuff { rc_perm, rc_token }; }
        });
    }
}

enum Sequence<V> {
    Nil,
    Cons(V, MyRc<Sequence<V>>),
}

fn main() {
    let nil = MyRc::new(Sequence::Nil);
    let a5 = MyRc::new(Sequence::Cons(5, nil.clone()));
    let a7 = MyRc::new(Sequence::Cons(7, nil.clone()));
    let a67 = MyRc::new(Sequence::Cons(6, a7.clone()));
}

}
// ANCHOR_END: full
