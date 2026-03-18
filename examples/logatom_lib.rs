#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::tokens::frac::*;
use vstd::logatom::{self, *};

verus! {

pub struct K {
    pub patomic_id: int,
    pub ghost_var_id: int,
}

pub struct V {
    pub perm: PermissionU64,
    pub auth: GhostVarAuth<u64>,
}

pub struct InvPred;
impl vstd::invariant::InvariantPredicate<K, V> for InvPred {
    open spec fn inv(k: K, v: V) -> bool {
        let K { patomic_id, ghost_var_id } = k;
        let V { perm, auth } = v;
        &&& perm@.patomic == patomic_id
        &&& auth.id() == ghost_var_id
        &&& perm@.value == auth.view()
    }
}

pub struct MyPermissionU64 {
    pub inner: GhostVar<u64>,
}

impl MyPermissionU64 {
    pub open spec fn id(self) -> int {
        self.inner.id()
    }

    pub open spec fn value(self) -> u64 {
        self.inner.view()
    }

    pub open spec fn is_for(self, my_patomic: MyPAtomicU64) -> bool {
        self.id() == my_patomic.id()
    }

    pub open spec fn points_to(self, value: u64) -> bool {
        self.value() == value
    }
}

pub struct MyPAtomicU64 {
    pub inner: PAtomicU64,
    pub inv: Tracked<AtomicInvariant<K, V, InvPred>>,
}

impl MyPAtomicU64 {
    pub open spec fn wf(self) -> bool {
        let ghost K { patomic_id, .. } = self.inv@.constant();
        &&& self.inner.id() == patomic_id
    }

    pub open spec fn id(self) -> int {
        let ghost K { ghost_var_id, .. } = self.inv@.constant();
        ghost_var_id
    }

    pub open spec fn inv_namespace(self) -> int {
        self.inv@.namespace()
    }

    pub fn new(v: u64, inv_ns: Ghost<int>) -> (out: (MyPAtomicU64, Tracked<MyPermissionU64>))
        ensures
            out.0.wf(),
            out.0.inv_namespace() == inv_ns@,
            out.1@.is_for(out.0),
            out.1@.points_to(v),
    {
        let (patomic, perm) = PAtomicU64::new(v);
        Self::from_patomic(patomic, perm, inv_ns)
    }

    pub fn from_patomic(patomic: PAtomicU64, perm: Tracked<PermissionU64>, Ghost(inv_ns): Ghost<int>)
        -> (out: (MyPAtomicU64, Tracked<MyPermissionU64>))
        requires
            perm@.is_for(patomic),
        ensures
            out.0.inner == patomic,
            out.0.wf(),
            out.0.inv_namespace() == inv_ns,
            out.1@.is_for(out.0),
            out.1@.points_to(perm@.value()),
    {
        let tracked (gva, gv) = GhostVarAuth::new(perm@.value());
        let my_patomic = MyPAtomicU64 {
            inner: patomic,
            inv: Tracked(AtomicInvariant::<K, V, InvPred>::new(
                K { patomic_id: perm@.id(), ghost_var_id: gva.id(), },
                V { perm: perm.get(), auth: gva, },
                inv_ns,
            )),
        };

        let tracked my_perm = MyPermissionU64 {
            inner: gv,
        };

        (my_patomic, Tracked(my_perm))
    }

    pub fn into_patomic(self, Tracked(my_perm): Tracked<MyPermissionU64>)
        -> (out: (PAtomicU64, Tracked<PermissionU64>))
        requires
            my_perm.is_for(self),
            self.wf(),
        ensures
            out.0 == self.inner,
            out.1@.is_for(out.0),
            out.1@.points_to(my_perm.value()),
    {
        let Self { inner, inv } = self;
        let tracked V { perm, auth } = inv.get().into_inner();
        proof { auth.agree(&my_perm.inner) };
        (inner, Tracked(perm))
    }
}

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

pub exec fn increment_seq(var: &MyPAtomicU64, Tracked(my_perm): Tracked<&mut MyPermissionU64>)
    requires
        var.wf(),
        old(my_perm).is_for(*var),
    ensures
        my_perm.value() == old(my_perm).value().wrapping_add(1),
        my_perm.is_for(*var),
{
    let curr;
    open_atomic_invariant!(var.inv.borrow() => v => {
        let tracked V { perm, auth } = v;
        curr = var.inner.load(Tracked(&perm));
        proof {
            auth.agree(&my_perm.inner);
            v = V { perm, auth };
        }
    });

    let next = curr.wrapping_add(1);
    open_atomic_invariant!(var.inv.borrow() => v => {
        let tracked V { perm, auth } = v;
        var.inner.store(Tracked(&mut perm), next);
        proof {
            auth.update(&mut my_perm.inner, next);
            assert(my_perm.value() == next);
            v = V { perm, auth };
        }
    });
}

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

pub fn increment_perm(var: &MyPAtomicU64, Tracked(my_perm): Tracked<&mut MyPermissionU64>)
    requires
        var.wf(),
        old(my_perm).is_for(*var),
    ensures
        my_perm.is_for(*var),
        my_perm.points_to(old(my_perm).value().wrapping_add(1)),
{
    let tracked inv = var.inv.borrow();
    let mut curr;
    open_atomic_invariant!(inv => v => {
        let tracked V { perm, auth } = v;
        curr = var.inner.load(Tracked(&perm));
        proof { v = V { perm, auth } }
    });

    let ghost orig_perm = *my_perm;
    loop invariant *my_perm == orig_perm {
        let next = curr.wrapping_add(1);
        let res;

        open_atomic_invariant!(inv => v => {
            let tracked V { perm, auth } = v;
            let ghost prev: u64 = perm@.value;

            res = var.inner.compare_exchange_weak(Tracked(&mut perm), curr, next);

            proof {
                if res is Ok {
                    assert(prev == curr);
                    assert(next == prev.wrapping_add(1));

                    auth.update(&mut my_perm.inner, next);

                    v = V { perm, auth };
                    assert(inv.inv(v));
                } else {
                    v = V { perm, auth };
                    assert(inv.inv(v));
                }
            }
        });

        match res {
            Ok(_) => break,
            Err(new) => {
                curr = new;
                continue;
            }
        }
    }
}

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

pub struct IncrementUpdate {
    pub auth: GhostVarAuth<u64>,
}

impl IncrementUpdate {
    pub open spec fn id(self) -> int {
        self.auth.id()
    }

    pub open spec fn value(self) -> u64 {
        self.auth@
    }

    pub proof fn update(tracked &mut self, tracked my_perm: &mut MyPermissionU64)
        requires
            old(self).id() == old(my_perm).id(),
        ensures
            self.id() == old(self).id(),
            my_perm.id() == old(my_perm).id(),
            old(self).value() == old(my_perm).value(),
            self.value() == my_perm.value(),
            my_perm.value() == old(my_perm).value().wrapping_add(1),
    {
        let next = self.auth@.wrapping_add(1);
        self.auth.update(&mut my_perm.inner, next);
    }
}

pub struct IncrementOp {
    pub id: int,
}

impl logatom::MutOperation for IncrementOp {
    type Resource = IncrementUpdate;
    type ExecResult = u64;
    type NewState = ();

    open spec fn requires(
        self,
        pre: Self::Resource,
        new_state: Self::NewState,
        e: Self::ExecResult
    ) -> bool {
        &&& pre.id() == self.id
        &&& pre.value() == e
    }

    open spec fn ensures(
        self,
        pre: Self::Resource,
        post: Self::Resource,
        new_state: Self::NewState
    ) -> bool {
        &&& post.id() == self.id
        &&& post.value() == pre.value().wrapping_add(1)
    }

    open spec fn peek_requires(self, r: Self::Resource) -> bool {
        false
    }

    open spec fn peek_ensures(self, r: Self::Resource) -> bool {
        false
    }
}

pub fn increment<Carrier>(var: &MyPAtomicU64, Tracked(carrier): Tracked<Carrier>)
        -> (out: (u64, Tracked<Carrier::Completion>))
    where
        Carrier: logatom::MutLinearizer<IncrementOp>,
    requires
        var.wf(),
        carrier.pre(IncrementOp { id: var.id() }),
        !carrier.namespaces().contains(var.inv_namespace()),
    ensures
        carrier.post(IncrementOp { id: var.id() }, out.0, out.1@),
    opens_invariants any,
{
    let tracked inv = var.inv.borrow();
    let mut curr;
    open_atomic_invariant!(inv => v => {
        let tracked V { perm, auth } = v;
        curr = var.inner.load(Tracked(&perm));
        proof { v = V { perm, auth } }
    });

    let ghost orig_carrier = carrier;
    let tracked mut maybe_carrier = Some(carrier);

    loop invariant maybe_carrier == Some(orig_carrier) {
        let tracked mut compl = None;
        let next = curr.wrapping_add(1);
        let res;

        open_atomic_invariant!(inv => v => {
            let tracked V { perm, auth } = v;
            let ghost prev: u64 = perm@.value;

            res = var.inner.compare_exchange_weak(Tracked(&mut perm), curr, next);

            proof {
                if res is Ok {
                    assert(prev == curr);
                    assert(next == prev.wrapping_add(1));

                    let op = IncrementOp { id: var.id() };
                    let tracked mut update = IncrementUpdate { auth };
                    let tracked carrier = maybe_carrier.tracked_take();
                    compl = Some(carrier.apply(op, &mut update, (), &curr));
                    let tracked IncrementUpdate { auth } = update;

                    v = V { perm, auth };
                    assert(inv.inv(v));
                } else {
                    v = V { perm, auth };
                    assert(inv.inv(v));
                }
            }
        });

        match res {
            Ok(_) => return (curr, Tracked(compl.tracked_unwrap())),
            Err(new) => {
                curr = new;
                continue;
            }
        }
    }
}

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

pub struct ClientSyncCarrier {
    pub my_perm: MyPermissionU64,
}

impl logatom::MutLinearizer<IncrementOp> for ClientSyncCarrier {
    type Completion = MyPermissionU64;

    open spec fn pre(self, op: IncrementOp) -> bool {
        &&& self.my_perm.id() == op.id
        &&& self.my_perm.value() == 6
    }

    open spec fn post(
        self,
        op: IncrementOp,
        r: <IncrementOp as logatom::MutOperation>::ExecResult,
        out: Self::Completion
    ) -> bool {
        &&& out.id() == op.id
        &&& out.value() == 7
        &&& r == 6
    }

    proof fn apply(
        tracked self,
        op: IncrementOp,
        tracked r: &mut <IncrementOp as logatom::MutOperation>::Resource,
        new_state: <IncrementOp as logatom::MutOperation>::NewState,
        e: &<IncrementOp as logatom::MutOperation>::ExecResult,
    ) -> (tracked out: Self::Completion) {
        let tracked mut my_perm = self.my_perm;
        r.update(&mut my_perm);
        my_perm
    }

    proof fn peek(
        tracked &self,
        op: IncrementOp,
        tracked r: &<IncrementOp as logatom::MutOperation>::Resource
    ) {}
}

pub fn client_sync() {
    let (my_patomic, Tracked(my_perm)) = MyPAtomicU64::new(6, Ghost(1234));
    assert(my_perm.points_to(6));

    let tracked carrier = ClientSyncCarrier { my_perm };
    let (prev, Tracked(my_perm)) = increment::<ClientSyncCarrier>(
        &my_patomic,
        Tracked(carrier)
    );

    assert(prev == 6);
    assert(my_perm.points_to(7));
}

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

pub struct UserInv;
pub open spec const USER_INV: int = 6789;
impl InvariantPredicate<int, MyPermissionU64> for UserInv {
    open spec fn inv(id: int, perm: MyPermissionU64) -> bool {
        &&& perm.id() == id
    }
}

pub struct ClientInvCarrier<'a> {
    pub my_inv: &'a AtomicInvariant<int, MyPermissionU64, UserInv>,
    pub credit: OpenInvariantCredit,
}

impl logatom::MutLinearizer<IncrementOp> for ClientInvCarrier<'_> {
    type Completion = ();

    open spec fn namespaces(self) -> Set<int> {
        set![USER_INV]
    }

    open spec fn pre(self, op: IncrementOp) -> bool {
        &&& self.my_inv.constant() == op.id
        &&& self.my_inv.namespace() == USER_INV
    }

    open spec fn post(
        self,
        op: IncrementOp,
        r: <IncrementOp as logatom::MutOperation>::ExecResult,
        out: Self::Completion
    ) -> bool {
        &&& true
    }

    proof fn apply(
        tracked self,
        op: IncrementOp,
        tracked r: &mut <IncrementOp as logatom::MutOperation>::Resource,
        new_state: <IncrementOp as logatom::MutOperation>::NewState,
        e: &<IncrementOp as logatom::MutOperation>::ExecResult,
    ) -> (tracked out: Self::Completion) {
        open_atomic_invariant!(self.credit => self.my_inv => my_perm => {
            r.update(&mut my_perm);
        });
    }

    proof fn peek(
        tracked &self,
        op: IncrementOp,
        tracked r: &<IncrementOp as logatom::MutOperation>::Resource
    ) {}
}

pub fn client_inv() {
    let (my_patomic, Tracked(my_perm)) = MyPAtomicU64::new(6, Ghost(1234));
    let tracked inv = AtomicInvariant::<_, _, UserInv>::new(my_perm.id(), my_perm, USER_INV);
    let Tracked(mut credit) = vstd::invariant::create_open_invariant_credit();

    let tracked carrier = ClientInvCarrier { my_inv: &inv, credit };
    let (prev, Tracked(_unit)) = increment::<ClientInvCarrier>(
        &my_patomic,
        Tracked(carrier)
    );
}

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

} // verus!
