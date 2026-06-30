//! Example usage of vstd::logatom
//!
//! We develop a linearizable counter, modelled with a GhostVarAuth resource
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::logatom;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::*;

verus! {

/// The owned version of the counter
struct OwnedCounter {
    atomic: PAtomicU64,
    inv: Tracked<AtomicInvariant<CounterPredicate, CounterInvariant, CounterPredicate>>,
    counter_id: Ghost<Loc>,
}

impl OwnedCounter {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.inv@.constant().perm_id == self.atomic.id()
        &&& self.inv@.constant().auth_id == self.counter_id@
    }

    /// id of the authoritative resource
    spec fn auth_id(self) -> Loc {
        self.counter_id@
    }

    /// id of the atomic invariant
    spec fn inv_id(self) -> int {
        self.inv@.namespace()
    }

    /// Creating a counter with a particular initial value
    /// We get out of it the counter and a half-permission to change the counter
    fn new(initial_value: u64) -> (r: (Self, Tracked<GhostVar<u64>>))
        ensures
            r.0.auth_id() == r.1@.id(),
            r.1@@ == initial_value,
    {
        let (atomic, Tracked(perm)) = PAtomicU64::new(initial_value);

        let tracked var;
        let tracked inv;
        proof {
            let tracked (auth, v) = GhostVarAuth::new(initial_value);
            var = v;
            let ghost counter_pred = CounterPredicate { perm_id: perm.id(), auth_id: auth.id() };
            let tracked counter_inv = CounterInvariant { perm, auth };
            inv = AtomicInvariant::new(counter_pred, counter_inv, 0);
        }

        let counter = OwnedCounter { atomic, inv: Tracked(inv), counter_id: Ghost(var.id()) };

        (counter, Tracked(var))
    }

    /// We can get a reference view over the counter
    fn as_ref<'a>(&'a self) -> (r: Counter<'a>)
        ensures
            r.auth_id() == self.auth_id(),
            r.inv_id() == self.inv_id(),
    {
        proof {
            use_type_invariant(self);
        }
        Counter { atomic: &self.atomic, inv: &self.inv, counter_id: self.counter_id }
    }
}

/// The counter that threads will interact with
struct Counter<'a> {
    atomic: &'a PAtomicU64,
    inv: &'a Tracked<AtomicInvariant<CounterPredicate, CounterInvariant, CounterPredicate>>,
    counter_id: Ghost<Loc>,
}

/// The invariant that is maintained
tracked struct CounterInvariant {
    perm: PermissionU64,
    auth: GhostVarAuth<u64>,
}

/// The predicate over the invariant (i.e., the constant part of the invariant)
struct CounterPredicate {
    perm_id: int,
    auth_id: Loc,
}

impl InvariantPredicate<CounterPredicate, CounterInvariant> for CounterPredicate {
    closed spec fn inv(pred: CounterPredicate, v: CounterInvariant) -> bool {
        // ids must match
        &&& v.perm.id() == pred.perm_id
        &&& v.auth.id()
            == pred.auth_id
        // the permission must agree with the resource on the value
        &&& v.perm@.value == v.auth@
    }
}

impl<'a> Counter<'a> {
    /// type invariant
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.inv@.constant().perm_id == self.atomic.id()
        &&& self.inv@.constant().auth_id == self.counter_id@
    }

    /// id of the authoritative resource
    spec fn auth_id(self) -> Loc {
        self.counter_id@
    }

    /// id of the atomic invariant
    spec fn inv_id(self) -> int {
        self.inv@.namespace()
    }

    /// Linearizable load
    fn load<RL>(&self, Tracked(lin): Tracked<RL>) -> (r: (u64, Tracked<RL::Completion>)) where
        RL: logatom::ReadLinearizer<LoadOp>,

        requires
            // simplification: the linearizer does not open invariants
            lin.namespaces().finite(),
            lin.namespaces().is_empty(),
            // the linearizer has preconditions that must hold
            lin.pre(LoadOp { id: self.auth_id() }),
        ensures
            // the linearizer has postconditions that must hold
            lin.post(LoadOp { id: self.auth_id() }, r.0, r.1@),
    {
        proof {
            // learn the counter ids match the invariant ids
            use_type_invariant(self);
        }
        let tracked inv = self.inv.borrow();
        let curr;
        let tracked comp;
        let ghost op = LoadOp { id: self.auth_id() };
        open_atomic_invariant!(inv => v => {
            let tracked CounterInvariant { perm, auth } = v;
            // do the load
            curr = self.atomic.load(Tracked(&perm));
            proof {
                // apply the linearizer
                comp = lin.apply(op, &auth, &curr);
                v = CounterInvariant { perm, auth };
            }
        });

        (curr, Tracked(comp))
    }

    /// Linearizable increment
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::loop_isolation(false)]
    fn inc<ML>(&self, Tracked(lin): Tracked<ML>) -> (r: (u64, Tracked<ML::Completion>)) where
        ML: logatom::MutLinearizer<IncOp>,

        requires
            lin.namespaces().finite(),
            lin.namespaces().is_empty(),
            lin.pre(IncOp { id: self.auth_id() }),
        ensures
            lin.post(IncOp { id: self.auth_id() }, r.0, r.1@),
    {
        proof {
            use_type_invariant(self);
        }
        let tracked inv = self.inv.borrow();
        let mut curr;
        open_atomic_invariant!(inv => v => {
            let tracked CounterInvariant { perm, auth } = v;
            curr = self.atomic.load(Tracked(&perm));
            proof { v = CounterInvariant { perm, auth } }
        });

        let ghost orig_lin = lin;
        let tracked mut maybe_lin = Some(lin);

        loop
            invariant
                maybe_lin == Some(orig_lin),
        {
            let tracked mut compl = None;
            let next = curr.wrapping_add(1);
            let res;

            open_atomic_invariant!(inv => v => {
                let tracked CounterInvariant { perm, auth } = v;
                let ghost prev: u64 = perm@.value;

                res = self.atomic.compare_exchange_weak(Tracked(&mut perm), curr, next);

                proof {
                    if res is Ok {
                        // operation succeeded, we can linearize (inside the atomic invariant)
                        assert(prev == curr);
                        assert(next == prev.wrapping_add(1));

                        let op = IncOp { id: self.auth_id() };
                        let tracked lin = maybe_lin.tracked_take();
                        assert(auth@ == curr);
                        compl = Some(lin.apply(op, &mut auth, (), &curr));

                        v = CounterInvariant { perm, auth };
                        assert(inv.inv(v));
                    } else {
                        v = CounterInvariant { perm, auth };
                        assert(inv.inv(v));
                    }
                }
            });

            match res {
                Ok(_) => return (curr, Tracked(compl.tracked_unwrap())),
                Err(new) => {
                    curr = new;
                    continue;
                },
            }
        }
    }
}

/// Operation for loading the counter
struct LoadOp {
    id: Loc,
}

impl logatom::ReadOperation for LoadOp {
    type Resource = GhostVarAuth<u64>;

    type ExecResult = u64;

    closed spec fn requires(self, pre: Self::Resource, e: Self::ExecResult) -> bool {
        &&& pre.id() == self.id
        &&& pre@ == e
    }

    closed spec fn peek_requires(self, r: Self::Resource) -> bool {
        false
    }

    closed spec fn peek_ensures(self, r: Self::Resource) -> bool {
        false
    }
}

/// Operation for incrementing the counter
struct IncOp {
    id: Loc,
}

impl logatom::MutOperation for IncOp {
    type Resource = GhostVarAuth<u64>;

    type ExecResult = u64;

    type NewState = ();

    closed spec fn requires(
        self,
        pre: Self::Resource,
        new_state: Self::NewState,
        e: Self::ExecResult,
    ) -> bool {
        &&& pre.id() == self.id
        &&& pre@ == e
    }

    closed spec fn ensures(
        self,
        pre: Self::Resource,
        post: Self::Resource,
        new_state: Self::NewState,
    ) -> bool {
        &&& post.id() == self.id
        &&& post@ == pre@.wrapping_add(1)
    }

    closed spec fn peek_requires(self, r: Self::Resource) -> bool {
        false
    }

    closed spec fn peek_ensures(self, r: Self::Resource) -> bool {
        false
    }
}

struct LoadPerm {
    pub tracked var: GhostVar<u64>,
}

impl logatom::ReadLinearizer<LoadOp> for LoadPerm {
    type Completion = GhostVar<u64>;

    closed spec fn namespaces(self) -> ISet<int> {
        ISet::empty()
    }

    closed spec fn pre(self, op: LoadOp) -> bool {
        &&& op.id == self.var.id()
    }

    closed spec fn post(self, op: LoadOp, exec_res: u64, completion: Self::Completion) -> bool {
        &&& op.id == self.var.id()
        &&& op.id == completion.id()
        &&& self.var == completion
        &&& exec_res == completion@
    }

    proof fn apply(
        tracked self,
        op: LoadOp,
        tracked resource: &GhostVarAuth<u64>,
        exec_res: &u64,
    ) -> (tracked result: Self::Completion) {
        resource.agree(&self.var);
        self.var
    }

    proof fn peek(tracked &self, op: LoadOp, tracked resource: &GhostVarAuth<u64>) {
    }
}

struct IncPerm {
    pub tracked var: GhostVar<u64>,
}

impl logatom::MutLinearizer<IncOp> for IncPerm {
    type Completion = GhostVar<u64>;

    closed spec fn namespaces(self) -> ISet<int> {
        ISet::empty()
    }

    closed spec fn pre(self, op: IncOp) -> bool {
        op.id == self.var.id()
    }

    closed spec fn post(self, op: IncOp, exec_res: u64, completion: Self::Completion) -> bool {
        &&& op.id == self.var.id()
        &&& op.id == completion.id()
    }

    proof fn apply(
        tracked self,
        op: IncOp,
        tracked resource: &mut GhostVarAuth<u64>,
        new_state: (),
        exec_res: &u64,
    ) -> (tracked result: Self::Completion) {
        let ghost old_self = self;
        let tracked IncPerm { mut var } = self;

        resource.update(&mut var, exec_res.wrapping_add(1));
        var
    }

    proof fn peek(tracked &self, op: IncOp, tracked resource: &GhostVarAuth<u64>) {
    }
}

// test that this works!
//
// note that we always need the owned GhostVar to do anything with the counter
//
// This means that our proof needs to show that there is actually one thread doing
// the operation at any point of time, sequentially.
//
// Though counterintuitive, we can imagine this to be useful to encode how in a particular
// context we do know that only one thread is operations, and that proof gets to know the
// *exact* value of the counter.
//
// To allow for concurrency, we need different ghost state, that gives back different knowledge.
// For instance, if we allow full concurrent threads to run ops on the counter, the best we can
// learn is some lower bound on the counter value, which would require a different resource
// construction. See examples/resource/monotonic_counter.rs for more inspiration.
fn main() {
    let (owned_counter, Tracked(orig_var)) = OwnedCounter::new(42);
    let ctr = owned_counter.as_ref();

    assert(orig_var@ == 42);
    let lperm = Tracked(LoadPerm { var: orig_var });
    let (res, load_var) = ctr.load(lperm);
}

} // verus!
