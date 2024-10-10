#![allow(unused_imports)]

use builtin::*;
use vstd::prelude::*;
use vstd::multiset::*;
use vstd::modes::*;
use vstd::set::*;
use vstd::invariant::InvariantPredicate;
use vstd::cell::{PCell, PointsTo, CellId};
use vstd::atomic_ghost::*;
use state_machines_macros::tokenized_state_machine;
use core::marker::PhantomData;

tokenized_state_machine!(
RwLockToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        #[sharding(constant)]
        pub k: K,

        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        #[sharding(variable)]
        pub flag_exc: bool,

        #[sharding(variable)]
        pub flag_rc: nat,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(option)]
        pub pending_writer: Option<()>,

        #[sharding(option)]
        pub writer: Option<()>,

        #[sharding(multiset)]
        pub pending_reader: Multiset<()>,

        #[sharding(multiset)]
        pub reader: Multiset<V>,
    }

    init!{
        initialize_full(k: K, t: V) {
            require Pred::inv(k, t);
            init k = k;
            init pred = PhantomData;
            init flag_exc = false;
            init flag_rc = 0;
            init storage = Option::Some(t);
            init pending_writer = Option::None;
            init writer = Option::None;
            init pending_reader = Multiset::empty();
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize_full)]
    fn initialize_full_inductive(post: Self, k: K, t: V) { }

    /// Increment the 'rc' counter, obtain a pending_reader
    transition!{
        acquire_read_start() {
            update flag_rc = pre.flag_rc + 1;
            add pending_reader += {()};
        }
    }

    /// Exchange the pending_reader for a reader by checking
    /// that the 'exc' bit is 0
    transition!{
        acquire_read_end() {
            require(pre.flag_exc == false);

            remove pending_reader -= {()};

            birds_eye let x: V = pre.storage.get_Some_0();
            add reader += {x};

            assert Pred::inv(pre.k, x);
        }
    }

    /// Decrement the 'rc' counter, abandon the attempt to gain
    /// the 'read' lock.
    transition!{
        acquire_read_abandon() {
            remove pending_reader -= {()};
            assert(pre.flag_rc >= 1);
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    /// Atomically set 'exc' bit from 'false' to 'true'
    /// Obtain a pending_writer
    transition!{
        acquire_exc_start() {
            require(pre.flag_exc == false);
            update flag_exc = true;
            add pending_writer += Some(());
        }
    }

    /// Finish obtaining the write lock by checking that 'rc' is 0.
    /// Exchange the pending_writer for a writer and withdraw the
    /// stored object.
    transition!{
        acquire_exc_end() {
            require(pre.flag_rc == 0);

            remove pending_writer -= Some(());

            add writer += Some(());

            birds_eye let x = pre.storage.get_Some_0();
            withdraw storage -= Some(x);

            assert Pred::inv(pre.k, x);
        }
    }

    /// Release the write-lock. Update the 'exc' bit back to 'false'.
    /// Return the 'writer' and also deposit an object back into storage.
    transition!{
        release_exc(x: V) {
            require Pred::inv(pre.k, x);
            remove writer -= Some(());

            update flag_exc = false;

            deposit storage += Some(x);
        }
    }

    /// Check that the 'reader' is actually a guard for the given object.
    property!{
        read_guard(x: V) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    property!{
        read_match(x: V, y: V) {
            have reader >= {x};
            have reader >= {y};
            assert(equal(x, y));
        }
    }

    /// Release the reader-lock. Decrement 'rc' and return the 'reader' object.
    #[transition]
    transition!{
        release_shared(x: V) {
            remove reader -= {x};

            assert(pre.flag_rc >= 1) by {
                //assert(pre.reader.count(x) >= 1);
                assert(equal(pre.storage, Option::Some(x)));
                //assert(equal(x, pre.storage.get_Some_0()));
            };
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    #[invariant]
    pub fn exc_bit_matches(&self) -> bool {
        (if self.flag_exc { 1 } else { 0 as int }) ==
            (if self.pending_writer.is_Some() { 1 } else { 0 as int }) as int
            + (if self.writer.is_Some() { 1 } else { 0 as int }) as int
    }

    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.flag_rc == self.pending_reader.count(())
            + self.reader.count(self.storage.get_Some_0())
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| imply(self.reader.count(t) > 0,
            equal(self.storage, Option::Some(t)))
    }

    #[invariant]
    pub fn writer_agrees_storage(&self) -> bool {
        imply(self.writer.is_Some(), self.storage.is_None())
    }

    #[invariant]
    pub fn writer_agrees_storage_rev(&self) -> bool {
        imply(self.storage.is_None(), self.writer.is_Some())
    }

    #[invariant]
    pub fn sto_user_inv(&self) -> bool {
        self.storage matches Some(x) ==> Pred::inv(self.k, x)
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(pre: Self, post: Self) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(pre: Self, post: Self, x: V) { }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self, x: V) {
        assert(equal(pre.storage, Option::Some(x)));
    }
});

verus!{

ghost struct InternalPred<K, V, Pred> {
    k: K, v: V, pred: Pred,
}

impl<K, V, Pred: InvariantPredicate<K, V>> InvariantPredicate<(K, CellId), PointsTo<V>> for InternalPred<K, V, Pred> {
    closed spec fn inv(k: (K, CellId), v: PointsTo<V>) -> bool {
        v.view().pcell == k.1
          && v.view().value.is_Some()
          && Pred::inv(k.0, v.view().value.get_Some_0())
    }
}

struct_with_invariants!{
    struct RwLock<K, V, Pred: InvariantPredicate<K, V>> {
        cell: PCell<V>,
        exc: AtomicBool<_, RwLockToks::flag_exc<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>, _>,
        rc: AtomicU64<_, RwLockToks::flag_rc<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>, _>,

        inst: Tracked<RwLockToks::Instance<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>>,
        k: Ghost<K>,
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        invariant on exc with (inst) is (v: bool, g: RwLockToks::flag_exc<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>) {
            g@.instance == inst@
                && g@.value == v
        }

        invariant on rc with (inst) is (v: u64, g: RwLockToks::flag_rc<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>) {
            g@.instance == inst@
                && g@.value == v
        }

        predicate {
            self.inst@.k() == (self.k@, self.cell.id())
        }
    }
}

struct WriteHandle<'a, K, V, Pred: InvariantPredicate<K, V>> {
    handle: Tracked<RwLockToks::writer<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>>,
    perm: Tracked<PointsTo<V>>,
    rwlock: &'a RwLock<K, V, Pred>,
}

tracked struct ReadHandle<K, V, Pred: InvariantPredicate<K, V>> {
    tracked handle: RwLockToks::reader<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>,
}

impl<K, V, Pred: InvariantPredicate<K, V>> ReadHandle<K, V, Pred> {
    spec fn view(&self) -> V {
        self.handle.view().key.view().value.unwrap()
    }
}

impl<'a, K, V, Pred: InvariantPredicate<K, V>> WriteHandle<'a, K, V, Pred> {
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        equal(self.perm@.view().pcell, self.rwlock.cell.id())
          && self.perm@.view().value.is_None()
          && equal(self.handle@.view().instance, self.rwlock.inst@)
          && self.rwlock.wf()
    }

    pub closed spec fn rwlock(self) -> RwLock<K, V, Pred> {
        *self.rwlock
    }

    fn release_write(self, t: V)
        requires
            self.rwlock().inv(t),
    {
        proof { use_type_invariant(&self); }
        let WriteHandle { handle: Tracked(handle), perm: Tracked(mut perm), rwlock: _ } = self;
        self.rwlock.cell.put(Tracked(&mut perm), t);

        atomic_with_ghost!(
            &self.rwlock.exc => store(false);
            ghost g =>
        {
            self.rwlock.inst.borrow().release_exc(perm, &mut g, perm, handle);
        });
    }
}

impl<K, V, Pred: InvariantPredicate<K, V>> RwLock<K, V, Pred> {
    pub closed spec fn constant(&self) -> K {
        self.k@
    }

    pub open spec fn inv(&self, t: V) -> bool {
        Pred::inv(self.constant(), t)
    }

    spec fn wf_read_handle(&self, read_handle: &ReadHandle<K, V, Pred>) -> bool {
        equal(read_handle.handle.view().instance, self.inst@)
          && read_handle.handle.view().key.view().value.is_Some()
          && equal(read_handle.handle.view().key.view().pcell, self.cell.id())
          && read_handle.handle.view().count == 1
    }

    fn new(t: V, Ghost(k): Ghost<K>) -> (s: Self)
        requires Pred::inv(k, t)
        ensures s.constant() == k,
    {
        let (cell, Tracked(perm)) = PCell::<V>::new(t);

        let tracked (Tracked(inst), Tracked(flag_exc), Tracked(flag_rc), _, _, _, _) =
            RwLockToks::Instance::<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>::initialize_full((k, cell.id()), perm, Option::Some(perm));
        let inst = Tracked(inst);

        let exc = AtomicBool::new(
            Ghost(inst), false, Tracked(flag_exc));
        let rc = AtomicU64::new(
            Ghost(inst), 0, Tracked(flag_rc));

        RwLock { cell, exc, rc, inst, k: Ghost(k) }
    }

    fn acquire_write(&self) -> (ret: (V, WriteHandle<K, V, Pred>))
        ensures ({
            let t = ret.0; let write_handle = ret.1;
                && write_handle.rwlock() == *self
                && self.inv(t)
        }),
    {
        proof { use_type_invariant(self); }
        let mut done = false;
        let tracked mut token: Option<RwLockToks::pending_writer<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>> = Option::None;
        while !done
            invariant
                done ==>
                    token.is_Some() && equal(token.get_Some_0().view().instance, self.inst@),
                self.wf(),
        {
            let result = atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning res;
                ghost g =>
            {
                if res.is_Ok() {
                    token = Option::Some(self.inst.borrow().acquire_exc_start(&mut g));
                }
            });

            done = match result {
                Result::Ok(_) => true,
                _ => false,
            };
        }

        loop
            invariant
                token.is_Some() && equal(token.get_Some_0().view().instance, self.inst@),
                self.wf(),
        {
            let tracked mut perm_opt: Option<PointsTo<V>> = None;
            let tracked mut handle_opt: Option<RwLockToks::writer<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>> = None;

            let result = atomic_with_ghost!(
                &self.rc => load();
                returning res;
                ghost g =>
            {
                if res == 0 {
                    let tracked tok = match token { Option::Some(t) => t, Option::None => proof_from_false() };
                    let tracked x = self.inst.borrow().acquire_exc_end(&g, tok);
                    token = None;
                    let tracked (_, Tracked(perm), Tracked(exc_handle)) = x;
                    perm_opt = Some(perm);
                    handle_opt = Some(exc_handle);
                }
            });

            if result == 0 {
                let tracked mut perm = match perm_opt { Option::Some(t) => t, Option::None => proof_from_false() };
                let tracked handle = match handle_opt { Option::Some(t) => t, Option::None => proof_from_false() };
                let t = self.cell.take(Tracked(&mut perm));
                let write_handle = WriteHandle { perm: Tracked(perm), handle: Tracked(handle), rwlock: self };
                return (t, write_handle);
            }
        }
    }

    fn acquire_read(&self) -> (x: Tracked<ReadHandle<K, V, Pred>>)
        ensures ({ let read_handle = x@;
            self.wf_read_handle(&read_handle)
                && self.inv(read_handle.view())
        })
    {
        proof { use_type_invariant(self); }
        loop
            invariant self.wf(),
        {
            let val = atomic_with_ghost!(&self.rc => load(); ghost g => { });

            let tracked mut token: Option<RwLockToks::pending_reader<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>> = Option::None;

            if val < 0xffff_ffff_ffff_ffff {
                let result = atomic_with_ghost!(
                    &self.rc => compare_exchange(val, val + 1);
                    returning res;
                    ghost g =>
                {
                    if res.is_Ok() {
                        token = Option::Some(self.inst.borrow().acquire_read_start(&mut g));
                    }
                });

                match result {
                    Result::Ok(_) => {
                        let tracked mut handle_opt: Option<RwLockToks::reader<(K, CellId), PointsTo<V>, InternalPred<K, V, Pred>>> = None;

                        let result = atomic_with_ghost!(
                            &self.exc => load();
                            returning res;
                            ghost g =>
                        {
                            if res == false {
                                let tracked tok = match token { Option::Some(t) => t, Option::None => proof_from_false() };
                                let tracked x = self.inst.borrow().acquire_read_end(&g, tok);
                                token = None;
                                let tracked (_, Tracked(exc_handle)) = x;
                                handle_opt = Some(exc_handle);
                            }
                        });

                        if result == false {
                            let tracked handle = match handle_opt { Option::Some(t) => t, Option::None => proof_from_false() };
                            let tracked read_handle = ReadHandle { handle };
                            return Tracked(read_handle);
                        } else {
                            let _ = atomic_with_ghost!(
                                &self.rc => fetch_sub(1);
                                ghost g =>
                            {
                                let tracked tok = match token { Option::Some(t) => t, Option::None => proof_from_false() };
                                self.inst.borrow().acquire_read_abandon(&mut g, tok);
                            });
                        }
                    }
                    _ => { }
                }
            }
        }
    }

    fn borrow<'a>(&'a self, Tracked(read_handle): Tracked<&'a ReadHandle<K, V, Pred>>) -> (t: &'a V)
        requires
            self.wf_read_handle(&read_handle),
        ensures t == read_handle.view()
    {
        proof { use_type_invariant(self); }
        let tracked perm = self.inst.borrow().read_guard(read_handle.handle.view().key, &read_handle.handle);
        self.cell.borrow(Tracked(&perm))
    }

    proof fn lemma_readers_match(
        tracked &self, 
        tracked read_handle1: &ReadHandle<K, V, Pred>,
        tracked read_handle2: &ReadHandle<K, V, Pred>
    )
        requires
            self.wf_read_handle(read_handle1),
            self.wf_read_handle(read_handle2),
        ensures(equal(
            read_handle1.view(),
            read_handle2.view(),
        )),
    {
        use_type_invariant(self);
        self.inst.borrow().read_match(
            read_handle1.handle.view().key,
            read_handle2.handle.view().key,
            &read_handle1.handle,
            &read_handle2.handle);
    }


    fn release_read(&self, Tracked(read_handle): Tracked<ReadHandle<K, V, Pred>>)
        requires
            self.wf_read_handle(&read_handle),
    {
        proof { use_type_invariant(self); }
        let tracked ReadHandle { handle } = read_handle;

        let _ = atomic_with_ghost!(
            &self.rc => fetch_sub(1);
            ghost g =>
        {
            self.inst.borrow().release_shared(handle.view().key, &mut g, handle);
        });
    }
}

struct ExamplePredicate { }
impl InvariantPredicate<(), u64> for ExamplePredicate {
    open spec fn inv(k: (), v: u64) -> bool {
        v == 5 || v == 13
    }
}

fn main() {
    let lock = RwLock::<(), u64, ExamplePredicate>::new(5, Ghost(()));

    let (val, write_handle) = lock.acquire_write();
    assert(val == 5 || val == 13);
    write_handle.release_write(13);

    let Tracked(read_handle1) = lock.acquire_read();
    let Tracked(read_handle2) = lock.acquire_read();

    let val1 = lock.borrow(Tracked(&read_handle1));
    let val2 = lock.borrow(Tracked(&read_handle2));

    proof { lock.lemma_readers_match(&read_handle1, &read_handle2); }
    assert(*val1 == *val2);

    lock.release_read(Tracked(read_handle1));
    lock.release_read(Tracked(read_handle2));
}

}
