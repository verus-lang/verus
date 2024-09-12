#![allow(unused_imports)]

// ANCHOR: full
use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::cell::*;
use vstd::invariant::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::{atomic::*, pervasive::*, *};
use vstd::shared::*;

verus! {

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

struct InnerArc<S> {
    pub rc_cell: PAtomicU64,
    pub s: S,
}

type MemPerms<S> = simple_pptr::PointsTo<InnerArc<S>>;

tracked struct GhostStuff<S> {
    pub tracked rc_perm: PermissionU64,
    pub tracked rc_token: RefCounter::counter<MemPerms<S>>,
}

impl<S> GhostStuff<S> {
    pub open spec fn wf(self, inst: RefCounter::Instance<MemPerms<S>>, cell: PAtomicU64) -> bool {
        &&& self.rc_perm@.patomic == cell.id()
        &&& self.rc_token@.instance == inst
        &&& self.rc_perm@.value as nat == self.rc_token@.value
    }
}

impl<S> InnerArc<S> {
    spec fn wf(self, cell: PAtomicU64) -> bool {
        self.rc_cell == cell
    }
}

struct_with_invariants!{
    struct MyArc<S> {
        pub inst: Tracked< RefCounter::Instance<MemPerms<S>> >,
        pub inv: Tracked< Shared<AtomicInvariant<_, GhostStuff<S>, _>> >,
        pub reader: Tracked< RefCounter::reader<MemPerms<S>> >,

        pub ptr: PPtr<InnerArc<S>>,

        pub rc_cell: Ghost< PAtomicU64 >,
    }

    spec fn wf(self) -> bool {
        predicate {
            &&& self.reader@@.key.pptr() == self.ptr
            &&& self.reader@@.key.pptr() == self.ptr

            &&& self.reader@@.instance == self.inst@
            &&& self.reader@@.count == 1
            &&& self.reader@@.key.is_init()
            &&& self.reader@@.key.value().rc_cell == self.rc_cell
        }

        invariant on inv with (inst, rc_cell)
            specifically (self.inv@@)
            is (v: GhostStuff<S>)
        {
            v.wf(inst@, rc_cell@)
        }
    }
}

impl<S> MyArc<S> {
    spec fn view(self) -> S {
        self.reader@@.key.value().s
    }

    fn new(s: S) -> (rc: Self)
        ensures
            rc.wf(),
            rc@ == s,
    {
        let (rc_cell, Tracked(rc_perm)) = PAtomicU64::new(1);
        let inner_rc = InnerArc::<S> { rc_cell, s };
        let (ptr, Tracked(ptr_perm)) = PPtr::new(inner_rc);
        let tracked (Tracked(inst), Tracked(mut rc_token), _) =
            RefCounter::Instance::initialize_empty(Option::None);
        let tracked reader = inst.do_deposit(
            ptr_perm,
            &mut rc_token,
            ptr_perm,
        );
        let tracked g = GhostStuff::<S> { rc_perm, rc_token };
        let tr_inst = Tracked(inst);
        let gh_cell = Ghost(rc_cell);
        let tracked inv = AtomicInvariant::new((tr_inst, gh_cell), g, 0);
        let tracked inv = Shared::new(inv);
        MyArc { inst: tr_inst, inv: Tracked(inv), reader: Tracked(reader), ptr, rc_cell: gh_cell }
    }

    fn borrow<'b>(&'b self) -> (s: &'b S)
        requires
            self.wf(),
        ensures
            *s == self@,
    {
        let tracked inst = self.inst.borrow();
        let tracked reader = self.reader.borrow();
        let tracked perm = inst.reader_guard(reader@.key, &reader);
        &self.ptr.borrow(Tracked(perm)).s
    }

    fn clone(&self) -> (s: Self)
        requires
            self.wf(),
        ensures
            s.wf() && s@ == self@,
    {
        loop
            invariant
                self.wf(),
        {
            let tracked inst = self.inst.borrow();
            let tracked reader = self.reader.borrow();
            let tracked perm = inst.reader_guard(reader@.key, &reader);
            let inner_rc_ref = self.ptr.borrow(Tracked(perm));
            let count: u64;
            open_atomic_invariant!(self.inv.borrow().borrow() => g => {
                let tracked GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

                count = inner_rc_ref.rc_cell.load(Tracked(&rc_perm));

                proof { g = GhostStuff { rc_perm, rc_token }; }
            });
            assume(count < 100000000);
            let tracked mut new_reader = None;
            let res;
            open_atomic_invariant!(self.inv.borrow().borrow() => g => {
                let tracked GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

                let count = count + 1;
                res = inner_rc_ref.rc_cell.compare_exchange_weak(Tracked(&mut rc_perm), count, count + 1);

                proof {
                    if res.is_ok() {
                        new_reader = Some(self.inst.borrow().do_clone(
                            reader@.key,
                            &mut rc_token,
                            &reader));
                    }
                }

                proof { g = GhostStuff { rc_perm, rc_token }; }
            });
            if res.is_ok() {
                return MyArc {
                    inst: Tracked(self.inst.borrow().clone()),
                    inv: Tracked(self.inv.borrow().clone()),
                    reader: Tracked(new_reader.tracked_unwrap()),
                    ptr: self.ptr,
                    rc_cell: Ghost(self.rc_cell@),
                };
            }
        }
    }

    fn dispose(self)
        requires
            self.wf(),
    {
        let MyArc {
            inst: Tracked(inst),
            inv: Tracked(inv),
            reader: Tracked(reader),
            ptr,
            rc_cell: _,
        } = self;
        let tracked perm = inst.reader_guard(reader@.key, &reader);
        let inner_rc_ref = &ptr.borrow(Tracked(perm));
        let count;
        let tracked mut inner_rc_perm_opt = None;
        open_atomic_invariant!(inv.borrow() => g => {
            let tracked GhostStuff { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

            count = inner_rc_ref.rc_cell.fetch_sub_wrapping(Tracked(&mut rc_perm), 1);

            proof {
                if rc_token@.value < 2 {
                    let tracked inner_rc_perm = inst.dec_to_zero(
                        reader.view().key, &mut rc_token, reader);
                    inner_rc_perm_opt = Some(inner_rc_perm);
                } else {
                    inst.dec_basic(reader.view().key, &mut rc_token, reader);
                }

                g = GhostStuff { rc_perm, rc_token };
            }
        });
        if count == 1 {
            let tracked mut inner_rc_perm = inner_rc_perm_opt.tracked_unwrap();
            let _inner_rc = ptr.take(Tracked(&mut inner_rc_perm));
            ptr.free(Tracked(inner_rc_perm));
        }
    }
}

enum Sequence<V> {
    Nil,
    Cons(V, MyArc<Sequence<V>>),
}

fn main() {
    let nil = MyArc::new(Sequence::Nil);
    let a5 = MyArc::new(Sequence::Cons(5, nil.clone()));
    let a7 = MyArc::new(Sequence::Cons(7, nil.clone()));
    let a67 = MyArc::new(Sequence::Cons(6, a7.clone()));
}

} // verus!
// ANCHOR_END: full
