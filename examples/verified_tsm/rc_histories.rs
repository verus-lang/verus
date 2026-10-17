#![allow(unused_imports)]
// ANCHOR: full
use std::marker::PhantomData;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::invariant::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::simple_pptr::*;
use vstd::{pervasive::*, *};
verus! {

// ANCHOR: fields
verified_tokenized_state_machine!(
RefCounter<Perm> {
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
        self.counter == 0 ==> self.storage is None
    }

    #[invariant]
    pub fn counter_agrees_storage_rev(&self) -> bool {
        self.storage is None ==> self.counter == 0
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.storage is Some ==>
            self.reader.count(self.storage->0) == self.counter
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
        assert(pre.storage is Some);
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

pub struct InnerRc<S> {
    pub rc_cell: cell::PCell<u64>,
    pub s: S,
}

pub type MemPerms<S> = simple_pptr::PointsTo<InnerRc<S>>;

pub tracked struct GhostStuff<S> {
    pub tracked rc_perm: cell::PointsTo<u64>,
    pub tracked rc_token: RefCounter::counter<MemPerms<S>>,
}

impl<S> GhostStuff<S> {
    pub open spec fn wf(
        self,
        inst: RefCounter::Instance<MemPerms<S>>,
        cell: cell::PCell<u64>,
    ) -> bool {
        &&& self.rc_perm.id() == cell.id()
        &&& self.rc_token.instance_id() == inst.id()
        &&& self.rc_perm.is_init()
        &&& self.rc_perm.value() as nat == self.rc_token.value()
    }
}

impl<S> InnerRc<S> {
    spec fn wf(self, cell: cell::PCell<u64>) -> bool {
        self.rc_cell == cell
    }
}

pub struct RefInvariantPredicate<S> {
    pub phantom: PhantomData<S>,
}

impl<S> InvariantPredicate<(Loc, vstd::cell::CellId), GhostStuff<S>> for RefInvariantPredicate<S> {
    open spec fn inv(key: (Loc, vstd::cell::CellId), state: GhostStuff<S>) -> bool {
        state.rc_perm.id() == key.1 && state.rc_perm.is_init() && state.rc_token.instance_id()
            == key.0 && state.rc_token.value() == state.rc_perm.value() as nat
    }
}

pub type RefInvariant<S> = LocalInvariant<
    (Loc, vstd::cell::CellId),
    GhostStuff<S>,
    RefInvariantPredicate<S>,
>;

pub struct MyRc<S: 'static> {
    pub inst: Tracked<RefCounter::Instance<MemPerms<S>>>,
    pub inv: Tracked<&'static RefInvariant<S>>,
    pub reader: Tracked<RefCounter::reader<MemPerms<S>>>,
    pub ptr: PPtr<InnerRc<S>>,
    pub rc_cell: Ghost<cell::PCell<u64>>,
}

impl<S: 'static> MyRc<S> {
    pub open spec fn wf(self) -> bool {
        &&& self.reader@.element().pptr() == self.ptr
        &&& self.reader@.instance_id() == self.inst@.id()
        &&& self.reader@.element().is_init()
        &&& self.reader@.element().value().rc_cell == self.rc_cell@
        &&& self.inv@.constant() == (self.inst@.id(), self.rc_cell@.id())
    }

    pub open spec fn view(self) -> S {
        self.reader@.element().value().s
    }

    pub fn new(s: S) -> (rc: Self)
        ensures
            rc.wf(),
            rc@ == s,
    {
        let (rc_cell, Tracked(rc_perm)) = cell::PCell::new(1);
        let inner_rc = InnerRc::<S> { rc_cell, s };
        let (ptr, Tracked(ptr_perm)) = PPtr::new(inner_rc);
        let tracked (Tracked(inst), Tracked(mut rc_token), _) =
            RefCounter::Instance::initialize_empty(Option::None);
        let tracked reader = inst.do_deposit(ptr_perm, &mut rc_token, ptr_perm);
        let tracked g = GhostStuff::<S> { rc_perm, rc_token };
        let tr_inst = Tracked(inst);
        let gh_cell = Ghost(rc_cell);
        let tracked inv = LocalInvariant::new((tr_inst@.id(), rc_cell.id()), g, 0);
        let tracked inv = vstd::modes::tracked_static_ref(inv);
        MyRc { inst: tr_inst, inv: Tracked(inv), reader: Tracked(reader), ptr, rc_cell: gh_cell }
    }

    pub fn borrow<'b>(&'b self) -> (s: &'b S)
        requires
            self.wf(),
        ensures
            *s == self@,
    {
        let tracked inst = self.inst.borrow();
        let tracked reader = self.reader.borrow();
        let tracked perm = inst.reader_guard(reader.element(), &reader);
        &self.ptr.borrow(Tracked(perm)).s
    }

    pub fn clone(&self) -> (s: Option<Self>)
        requires
            self.wf(),
        ensures
            s is Some ==> s->Some_0.wf() && s->Some_0@ == self@,
    {
        let tracked inst = self.inst.borrow();
        let tracked reader = self.reader.borrow();
        let tracked perm = inst.reader_guard(reader.element(), &reader);
        let inner_rc_ref = self.ptr.borrow(Tracked(perm));
        let tracked mut new_reader = None;
        let count;
        open_local_invariant!(*self.inv.borrow()=>g=>{
   let tracked GhostStuff{rc_perm:mut rc_perm,rc_token:mut rc_token}=g;
   count=inner_rc_ref.rc_cell.take(Tracked(&mut rc_perm));
   if count==u64::MAX{inner_rc_ref.rc_cell.put(Tracked(&mut rc_perm),count);}
   else{
    let count=count+1;inner_rc_ref.rc_cell.put(Tracked(&mut rc_perm),count);
    proof{new_reader=Some(self.inst.borrow().do_clone(reader.element(),&mut rc_token,&reader));}
   }
   proof{g=GhostStuff{rc_perm,rc_token};}
  });
        if count == u64::MAX {
            None
        } else {
            Some(
                MyRc {
                    inst: Tracked(self.inst.borrow().clone()),
                    inv: Tracked(*self.inv.borrow()),
                    reader: Tracked(new_reader.tracked_unwrap()),
                    ptr: self.ptr,
                    rc_cell: Ghost(self.rc_cell@),
                },
            )
        }
    }

    pub fn dispose(self)
        requires
            self.wf(),
    {
        let MyRc {
            inst: Tracked(inst),
            inv: Tracked(inv),
            reader: Tracked(reader),
            ptr,
            rc_cell: _,
        } = self;
        let tracked perm = inst.reader_guard(reader.element(), &reader);
        let inner_rc_ref = &ptr.borrow(Tracked(perm));
        let count;
        let tracked mut inner_rc_perm_opt = None;
        open_local_invariant!(inv=>g=>{
   let tracked GhostStuff{rc_perm:mut rc_perm,rc_token:mut rc_token}=g;
   count=inner_rc_ref.rc_cell.take(Tracked(&mut rc_perm));
   if count>=2{
    let count=count-1;inner_rc_ref.rc_cell.put(Tracked(&mut rc_perm),count);
    proof{inst.dec_basic(reader.element(),&mut rc_token,reader);}
   }else{
    let tracked mut inner_rc_perm=inst.dec_to_zero(reader.element(),&mut rc_token,reader);
    let inner_rc=ptr.take(Tracked(&mut inner_rc_perm));
    let count=count-1;inner_rc.rc_cell.put(Tracked(&mut rc_perm),count);
    proof{inner_rc_perm_opt=Some(inner_rc_perm);}
   }
   proof{g=GhostStuff{rc_perm,rc_token};}
  });
        if count < 2 {
            ptr.free(Tracked(inner_rc_perm_opt.tracked_unwrap()));
        }
    }
}

pub enum Sequence<V: 'static> {
    Nil,
    Cons(V, MyRc<Sequence<V>>),
}

fn main() {
    let nil = MyRc::new(Sequence::<u64>::Nil);
    let tail5 = match nil.clone() {
        Some(rc) => rc,
        None => {
            return;
        },
    };
    let a5 = MyRc::new(Sequence::Cons(5u64, tail5));
    let tail7 = match nil.clone() {
        Some(rc) => rc,
        None => {
            return;
        },
    };
    let a7 = MyRc::new(Sequence::Cons(7u64, tail7));
    let tail67 = match a7.clone() {
        Some(rc) => rc,
        None => {
            return;
        },
    };
    let a67 = MyRc::new(Sequence::Cons(6u64, tail67));
    match a5.borrow() {
        Sequence::Nil => {
            assert(false);
        },
        Sequence::Cons(value, _) => {
            assert(*value == 5);
        },
    }
    match a67.borrow() {
        Sequence::Nil => {
            assert(false);
        },
        Sequence::Cons(value, _) => {
            assert(*value == 6);
        },
    }

    // Exercise both disposal branches on a value whose last reference is freed.
    let value = MyRc::new(42u64);
    let copy = match value.clone() {
        Some(rc) => rc,
        None => {
            return;
        },
    };
    let observed = copy.borrow();
    assert(*observed == 42);
    copy.dispose();
    let observed = value.borrow();
    assert(*observed == 42);
    value.dispose();

    // The recursive guide client intentionally retains its shared tails.
    a5.dispose();
    a67.dispose();
    a7.dispose();
    nil.dispose();
}

} // verus!
// ANCHOR_END: full
