#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(non_shorthand_field_patterns)]

use super::atomic_ghost::*;
use super::cell::{CellId, PCell, PointsTo};
use super::invariant::InvariantPredicate;
use super::modes::*;
use super::multiset::*;
use super::prelude::*;
use super::set::*;
use core::marker::PhantomData;
use state_machines_macros::tokenized_state_machine_vstd;

tokenized_state_machine_vstd!(
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
    fn initialize_full_inductive(post: Self, k: K, t: V) {
        broadcast use group_multiset_axioms;
    }

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

            birds_eye let x: V = pre.storage->0;
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

            birds_eye let x = pre.storage->0;
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
                //assert(equal(x, pre.storage->0));
            };
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    #[invariant]
    pub fn exc_bit_matches(&self) -> bool {
        (if self.flag_exc { 1 } else { 0 as int }) ==
            (if self.pending_writer is Some { 1 } else { 0 as int }) as int
            + (if self.writer is Some { 1 } else { 0 as int }) as int
    }

    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.flag_rc == self.pending_reader.count(())
            + self.reader.count(self.storage->0)
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| imply(#[trigger] self.reader.count(t) > 0,
            equal(self.storage, Option::Some(t)))
    }

    #[invariant]
    pub fn writer_agrees_storage(&self) -> bool {
        imply(self.writer is Some, self.storage is None)
    }

    #[invariant]
    pub fn writer_agrees_storage_rev(&self) -> bool {
        imply(self.storage is None, self.writer is Some)
    }

    #[invariant]
    pub fn sto_user_inv(&self) -> bool {
        self.storage.is_some() ==> Pred::inv(self.k, self.storage.unwrap())
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(pre: Self, post: Self) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(pre: Self, post: Self, x: V) { }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self, x: V) {
        broadcast use group_multiset_axioms;
        assert(equal(pre.storage, Option::Some(x)));
    }
});

verus! {

pub trait RwLockPredicate<V>: Sized {
    spec fn inv(self, v: V) -> bool;
}

impl<V> RwLockPredicate<V> for spec_fn(V) -> bool {
    open spec fn inv(self, v: V) -> bool {
        self(v)
    }
}

ghost struct InternalPred<V, Pred> {
    v: V,
    pred: Pred,
}

impl<V, Pred: RwLockPredicate<V>> InvariantPredicate<(Pred, CellId), PointsTo<V>> for InternalPred<
    V,
    Pred,
> {
    closed spec fn inv(k: (Pred, CellId), v: PointsTo<V>) -> bool {
        v.id() == k.1 && v.is_init() && k.0.inv(v.value())
    }
}

struct_with_invariants_vstd!{
    /** A verified implementation of a reader-writer lock,
    implemented using atomics and a reference count.

    When constructed, you can provide an invariant via the `Pred` parameter,
    specifying the allowed values that can go in the lock.

    Note that this specification does *not* verify the absence of dead-locks.

    ### Examples

    On construction of a lock, we can specify an invariant for the object that goes inside.
    One way to do this is by providing a `spec_fn`, which implements the [`RwLockPredicate`]
    trait.

    ```rust,ignore
    fn example1() {
        // We can create a lock with an invariant: `v == 5 || v == 13`.
        // Thus only 5 or 13 can be stored in the lock.
        let lock = RwLock::<u64, spec_fn(u64) -> bool>::new(5, Ghost(|v| v == 5 || v == 13));

        let (val, write_handle) = lock.acquire_write();
        assert(val == 5 || val == 13);
        write_handle.release_write(13);

        let read_handle1 = lock.acquire_read();
        let read_handle2 = lock.acquire_read();

        // We can take multiple read handles at the same time:

        let val1 = read_handle1.borrow();
        let val2 = read_handle2.borrow();

        // RwLock has a lemma that both read handles have the same value:

        proof { ReadHandle::lemma_readers_match(&read_handle1, &read_handle2); }
        assert(*val1 == *val2);

        read_handle1.release_read();
        read_handle2.release_read();
    }
    ```

    It's often easier to implement the [`RwLockPredicate`] trait yourself. This way you can
    have a configurable predicate without needing to work with higher-order functions.

    ```rust,ignore
    struct FixedParity {
        pub parity: int,
    }

    impl RwLockPredicate<u64> for FixedParity {
        open spec fn inv(self, v: u64) -> bool {
            v % 2 == self.parity
        }
    }

    fn example2() {
        // Create a lock that can only store even integers
        let lock_even = RwLock::<u64, FixedParity>::new(20, Ghost(FixedParity { parity: 0 }));

        // Create a lock that can only store odd integers
        let lock_odd = RwLock::<u64, FixedParity>::new(23, Ghost(FixedParity { parity: 1 }));

        let read_handle_even = lock_even.acquire_read();
        let val_even = *read_handle_even.borrow();
        assert(val_even % 2 == 0);

        let read_handle_odd = lock_odd.acquire_read();
        let val_odd = *read_handle_odd.borrow();
        assert(val_odd % 2 == 1);
    }
    ```
    */

    pub struct RwLock<V, Pred: RwLockPredicate<V>> {
        cell: PCell<V>,
        exc: AtomicBool<_, RwLockToks::flag_exc<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>, _>,
        rc: AtomicUsize<_, RwLockToks::flag_rc<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>, _>,

        inst: Tracked<RwLockToks::Instance<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>>,
        pred: Ghost<Pred>,
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        invariant on exc with (inst) is (v: bool, g: RwLockToks::flag_exc<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>) {
            g.instance_id() == inst@.id()
                && g.value() == v
        }

        invariant on rc with (inst) is (v: usize, g: RwLockToks::flag_rc<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>) {
            g.instance_id() == inst@.id()
                && g.value() == v
        }

        predicate {
            self.inst@.k() == (self.pred@, self.cell.id())
        }
    }
}

/// Handle obtained for an exclusive write-lock from an [`RwLock`].
///
/// Note that this handle does not contain a reference to the lock-protected object;
/// ownership of the object is obtained separately from [`RwLock::acquire_write`].
/// This may be changed in the future.
///
/// **Warning:** The lock is _NOT_ released automatically when the handle
/// is dropped. You must call [`release_write`](WriteHandle::release_write).
/// Verus does not check that lock is released.
pub struct WriteHandle<'a, V, Pred: RwLockPredicate<V>> {
    handle: Tracked<RwLockToks::writer<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>>,
    perm: Tracked<PointsTo<V>>,
    rwlock: &'a RwLock<V, Pred>,
}

/// Handle obtained for a shared read-lock from an [`RwLock`].
///
/// **Warning:** The lock is _NOT_ released automatically when the handle
/// is dropped. You must call [`release_read`](ReadHandle::release_read).
/// Verus does not check that lock is released.
pub struct ReadHandle<'a, V, Pred: RwLockPredicate<V>> {
    handle: Tracked<RwLockToks::reader<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>>,
    rwlock: &'a RwLock<V, Pred>,
}

impl<'a, V, Pred: RwLockPredicate<V>> WriteHandle<'a, V, Pred> {
    #[verifier::type_invariant]
    spec fn wf_write_handle(self) -> bool {
        equal(self.perm@.id(), self.rwlock.cell.id()) && self.perm@.is_uninit() && equal(
            self.handle@.instance_id(),
            self.rwlock.inst@.id(),
        ) && self.rwlock.wf()
    }

    pub closed spec fn rwlock(self) -> RwLock<V, Pred> {
        *self.rwlock
    }

    pub fn release_write(self, new_val: V)
        requires
            self.rwlock().inv(new_val),
    {
        proof {
            use_type_invariant(&self);
        }
        let WriteHandle { handle: Tracked(handle), perm: Tracked(mut perm), rwlock } = self;
        self.rwlock.cell.put(Tracked(&mut perm), new_val);

        atomic_with_ghost!(
            &rwlock.exc => store(false);
            ghost g =>
        {
            self.rwlock.inst.borrow().release_exc(perm, &mut g, perm, handle);
        });
    }
}

impl<'a, V, Pred: RwLockPredicate<V>> ReadHandle<'a, V, Pred> {
    #[verifier::type_invariant]
    spec fn wf_read_handle(self) -> bool {
        equal(self.handle@.instance_id(), self.rwlock.inst@.id())
            && self.handle@.element().is_init() && equal(
            self.handle@.element().id(),
            self.rwlock.cell.id(),
        ) && self.rwlock.wf()
    }

    pub closed spec fn view(self) -> V {
        self.handle@.element().value()
    }

    pub closed spec fn rwlock(self) -> RwLock<V, Pred> {
        *self.rwlock
    }

    /// Obtain a shared reference to the object contained in the lock.
    pub fn borrow<'b>(&'b self) -> (val: &'b V)
        ensures
            val == self.view(),
    {
        proof {
            use_type_invariant(self);
        }
        let tracked perm = self.rwlock.inst.borrow().read_guard(
            self.handle@.element(),
            self.handle.borrow(),
        );
        self.rwlock.cell.borrow(Tracked(&perm))
    }

    pub proof fn lemma_readers_match(
        tracked read_handle1: &ReadHandle<V, Pred>,
        tracked read_handle2: &ReadHandle<V, Pred>,
    )
        requires
            read_handle1.rwlock() == read_handle2.rwlock(),
        ensures
            (equal(read_handle1.view(), read_handle2.view())),
    {
        use_type_invariant(read_handle1);
        use_type_invariant(read_handle2);
        read_handle1.rwlock.inst.borrow().read_match(
            read_handle1.handle@.element(),
            read_handle2.handle@.element(),
            &read_handle1.handle.borrow(),
            &read_handle2.handle.borrow(),
        );
    }

    pub fn release_read(self) {
        proof {
            use_type_invariant(&self);
        }
        let ReadHandle { handle: Tracked(handle), rwlock } = self;

        let _ =
            atomic_with_ghost!(
            &rwlock.rc => fetch_sub(1);
            ghost g =>
        {
            rwlock.inst.borrow().release_shared(handle.element(), &mut g, handle);
        });
    }
}

impl<V, Pred: RwLockPredicate<V>> RwLock<V, Pred> {
    /// Predicate configured for this lock instance.
    pub closed spec fn pred(&self) -> Pred {
        self.pred@
    }

    /// Indicates if the value `v` can be stored in the lock. Per the definition,
    /// it depends on `[self.pred()]`, which is configured upon lock construction ([`RwLock::new`]).
    pub open spec fn inv(&self, val: V) -> bool {
        self.pred().inv(val)
    }

    pub fn new(val: V, Ghost(pred): Ghost<Pred>) -> (s: Self)
        requires
            pred.inv(val),
        ensures
            s.pred() == pred,
    {
        let (cell, Tracked(perm)) = PCell::<V>::new(val);

        let tracked (Tracked(inst), Tracked(flag_exc), Tracked(flag_rc), _, _, _, _) =
            RwLockToks::Instance::<
            (Pred, CellId),
            PointsTo<V>,
            InternalPred<V, Pred>,
        >::initialize_full((pred, cell.id()), perm, Option::Some(perm));
        let inst = Tracked(inst);

        let exc = AtomicBool::new(Ghost(inst), false, Tracked(flag_exc));
        let rc = AtomicUsize::new(Ghost(inst), 0, Tracked(flag_rc));

        RwLock { cell, exc, rc, inst, pred: Ghost(pred) }
    }

    /// Acquires an exclusive write-lock. To release it, use [`WriteHandle::release_write`].
    ///
    /// **Warning:** The lock is _NOT_ released automatically when the handle
    /// is dropped. You must call [`WriteHandle::release_write`].
    /// Verus does not check that lock is released.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_write(&self) -> (ret: (V, WriteHandle<V, Pred>))
        ensures
            ({
                let val = ret.0;
                let write_handle = ret.1;
                &&& write_handle.rwlock() == *self
                &&& self.inv(val)
            }),
    {
        proof {
            use_type_invariant(self);
        }
        let mut done = false;
        let tracked mut token: Option<
            RwLockToks::pending_writer<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>,
        > = Option::None;
        while !done
            invariant
                done ==> token.is_some() && equal(token->0.instance_id(), self.inst@.id()),
                self.wf(),
        {
            let result =
                atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning res;
                ghost g =>
            {
                if res is Ok {
                    token = Option::Some(self.inst.borrow().acquire_exc_start(&mut g));
                }
            });

            done =
            match result {
                Result::Ok(_) => true,
                _ => false,
            };
        }
        loop
            invariant
                token is Some && equal(token->0.instance_id(), self.inst@.id()),
                self.wf(),
        {
            let tracked mut perm_opt: Option<PointsTo<V>> = None;
            let tracked mut handle_opt: Option<
                RwLockToks::writer<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>,
            > = None;

            let result =
                atomic_with_ghost!(
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
                let tracked mut perm = match perm_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked handle = match handle_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let t = self.cell.take(Tracked(&mut perm));
                let write_handle = WriteHandle {
                    perm: Tracked(perm),
                    handle: Tracked(handle),
                    rwlock: self,
                };
                return (t, write_handle);
            }
        }
    }

    /// Acquires a shared read-lock. To release it, use [`ReadHandle::release_read`].
    ///
    /// **Warning:** The lock is _NOT_ released automatically when the handle
    /// is dropped. You must call [`ReadHandle::release_read`].
    /// Verus does not check that lock is released.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_read(&self) -> (read_handle: ReadHandle<V, Pred>)
        ensures
            read_handle.rwlock() == *self,
            self.inv(read_handle.view()),
    {
        proof {
            use_type_invariant(self);
        }
        loop
            invariant
                self.wf(),
        {
            let val = atomic_with_ghost!(&self.rc => load(); ghost g => { });

            let tracked mut token: Option<
                RwLockToks::pending_reader<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>,
            > = Option::None;

            if val < usize::MAX {
                let result =
                    atomic_with_ghost!(
                    &self.rc => compare_exchange(val, val + 1);
                    returning res;
                    ghost g =>
                {
                    if res is Ok {
                        token = Option::Some(self.inst.borrow().acquire_read_start(&mut g));
                    }
                });

                match result {
                    Result::Ok(_) => {
                        let tracked mut handle_opt: Option<
                            RwLockToks::reader<(Pred, CellId), PointsTo<V>, InternalPred<V, Pred>>,
                        > = None;

                        let result =
                            atomic_with_ghost!(
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
                            let tracked handle = match handle_opt {
                                Option::Some(t) => t,
                                Option::None => proof_from_false(),
                            };
                            let read_handle = ReadHandle { handle: Tracked(handle), rwlock: self };
                            return read_handle;
                        } else {
                            let _ =
                                atomic_with_ghost!(
                                &self.rc => fetch_sub(1);
                                ghost g =>
                            {
                                let tracked tok = match token { Option::Some(t) => t, Option::None => proof_from_false() };
                                self.inst.borrow().acquire_read_abandon(&mut g, tok);
                            });
                        }
                    },
                    _ => {},
                }
            }
        }
    }

    /// Destroys the lock and returns the inner object.
    /// Note that this may deadlock if not all locks have been released.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn into_inner(self) -> (v: V)
        ensures
            self.inv(v),
    {
        let (v, _write_handle) = self.acquire_write();
        v
    }
}

} // verus!
