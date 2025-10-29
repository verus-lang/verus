// rust_verify/tests/example.rs ignore --- incomplete proof
use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::tokens::frac::*;

verus! {

type FlipAU = AtomicUpdate<FlagToken, FlagToken, FlipPred>;

pub enum Protocol {
    Empty(GhostVarAuth<Option<FlipAU>>),
    Offering(Tracked<FlipAU>),
    Accepted,
}

use Protocol::*;

impl Protocol {
    proof fn take_empty(tracked self) -> (tracked out: GhostVarAuth<Option<FlipAU>>)
        requires self is Empty,
        ensures self == Empty(out),
    {
        match self {
            Empty(gva) => gva,
            _ => proof_from_false(),
        }
    }

    proof fn take_offer(tracked self) -> (tracked out: Tracked<FlipAU>)
        requires self is Offering,
        ensures self == Offering(out),
    {
        match self {
            Offering(au) => au,
            _ => proof_from_false(),
        }
    }
}

type K = (int, int, int, int);
type V = (PermissionBool, PermissionU32, GhostVarAuth<bool>, GhostVar<Option<FlipAU>>, Protocol);

pub struct FlagInv;
impl InvariantPredicate<K, V> for FlagInv {
    open spec fn inv(k: K, v: V) -> bool {
        let (value_id, pend_id, state_id, gv_id) = k;
        let (value_perm, pend_perm, state, gv, proto) = v;
        &&& value_perm.id() == value_id
        &&& pend_perm.id() == pend_id
        &&& state.id() == state_id
        &&& gv.id() == gv_id
        &&& pend_perm.value() < 3
        &&& match proto {
            Empty(gva) => {
                &&& pend_perm.value() == 0
                &&& gva.id() == gv_id
                &&& gv@ is None
                &&& gva@ is None
                &&& gv@ == gva@
            }
            Offering(au) => {
                &&& pend_perm.value() == 1
                &&& gv@ is Some
                &&& gv@->0 == au@
            },
            Accepted => {
                &&& pend_perm.value() == 2
                &&& gv@ is Some
                &&& gv@->0.resolves()
            }
        }
    }
}

pub struct FlagToken {
    pub value: GhostVar<bool>,
}

pub struct Flag {
    pub value: PAtomicBool,
    pub pending: PAtomicU32,
    pub inv: Tracked<AtomicInvariant<K, V, FlagInv>>,
}

impl Flag {
    pub open spec fn wf(self) -> bool {
        &&& self.inv@.constant().0 == self.value.id()
        &&& self.inv@.constant().1 == self.pending.id()
    }

    pub open spec fn token_id(self) -> int {
        self.inv@.constant().2
    }

    pub fn new() -> (out: (Self, Tracked<FlagToken>))
        ensures
            out.0.wf(),
            out.0.token_id() == out.1@.value.id(),
    {
        let (value, Tracked(value_perm)) = PAtomicBool::new(false);
        let (pending, Tracked(pending_perm)) = PAtomicU32::new(0);
        let tracked (state_auth, state_var) = GhostVarAuth::new(false);
        let tracked (au_auth, au_var) = GhostVarAuth::new(None);
        let tracked inv = AtomicInvariant::new(
            (value.id(), pending.id(), state_auth.id(), au_auth.id()),
            (value_perm, pending_perm, state_auth, au_var, Empty(au_auth)),
            arbitrary()
        );

        let this = Self { value, pending, inv: Tracked(inv) };
        let tracked token = FlagToken { value: state_var };
        (this, Tracked(token))
    }

    pub fn read(&self) -> bool
        requires self.wf(),
    {
        let out;
        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            out = self.value.load(Tracked(&value_perm));
            proof { v = (value_perm, pend_perm, auth, gv, proto); }
        });

        return out;
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::loop_isolation(false)]
    pub fn flip(&self)
        atomically (atomic_update) {
            type FlipPred,
            (old_token: FlagToken) -> (new_token: FlagToken),
            requires
                old_token.value.id() == self.token_id(),
            ensures
                new_token.value@ == !old_token.value@,
                new_token.value.id() == old_token.value.id(),
        },
        requires self.wf(),
    {
        let tracked mut au = atomic_update;

        loop invariant
            self.wf(),
            au == atomic_update,
        {
            match self.try_cancel_two_flips(au) {
                Some(upd) => proof { au = upd.get() },
                None => return,
            }

            match self.try_simple_flip(au) {
                Some(upd) => proof { au = upd.get() },
                None => return,
            }

            match self.try_handshake(au) {
                Some(upd) => proof { au = upd.get() },
                None => return,
            }
        }
    }

    fn try_cancel_two_flips(&self, tracked au: FlipAU) -> (out: Option<Tracked<FlipAU>>)
        requires
            self.wf(),
            au.pred().args(self),
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 2);

            proof {
                if res.is_ok() {
                    let tracked au = maybe_au.tracked_take();
                    let tracked other_au = proto.take_offer();

                    assert(gv@ is Some);
                    assert(gv@->0 == other_au);

                    open_atomic_update!(au, mut token => {
                        let ghost old = auth@;
                        auth.update(&mut token.value, !old);
                        token
                    });

                    open_atomic_update!(other_au.get(), mut token => {
                        let ghost old = auth@;
                        auth.update(&mut token.value, !old);
                        token
                    });

                    assert(gv@ is Some);
                    assert(gv@->0.resolves());

                    proto = Accepted;
                }

                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_ok() {
            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }

    fn try_simple_flip(&self, tracked au: FlipAU) -> (out: Option<Tracked<FlipAU>>)
        requires
            self.wf(),
            au.pred().args(self),
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.value.compare_exchange(Tracked(&mut value_perm), true, false);
            proof {
                if res.is_ok() {
                    let tracked au = maybe_au.tracked_take();
                    open_atomic_update!(au, mut token => {
                        let ghost old = auth@;
                        auth.update(&mut token.value, !old);
                        token
                    });
                }

                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_ok() {
            return None;
        }

        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.value.compare_exchange(Tracked(&mut value_perm), false, true);
            proof {
                if res.is_ok() {
                    let tracked au = maybe_au.tracked_take();
                    open_atomic_update!(au, mut token => {
                        let ghost old = auth@;
                        auth.update(&mut token.value, !old);
                        token
                    });
                }

                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_ok() {
            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }

    fn try_handshake(&self, tracked au: FlipAU) -> (out: Option<Tracked<FlipAU>>)
        requires
            self.wf(),
            au.pred().args(self),
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let tracked mut auth_au = None;
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 0, 1);

            proof {
                if res.is_ok() {
                    let tracked au = maybe_au.tracked_take();
                    assert(proto is Empty);

                    let tracked mut gva = proto.take_empty();
                    assert(gva.id() == gv.id());
                    assert(gva@ is None);

                    gva.update(&mut gv, Some(au));
                    auth_au = Some(gva);

                    proto = Offering(Tracked(au));
                }

                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_err() {
            return Some(Tracked(maybe_au.tracked_take()));
        }

        assert(auth_au is Some);

        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 0);

            proof {
                if res.is_ok() {
                    assert(proto is Offering);
                    assert(maybe_au is None);
                    assert(auth_au is Some);

                    let tracked mut au = proto.take_offer();
                    let tracked mut gva = auth_au.tracked_take();
                    gva.agree(&gv);

                    gva.update(&mut gv, None);
                    assert(gva@ is None);

                    maybe_au = Some(au.get());
                    proto = Empty(gva);
                } else {
                    assert(auth_au is Some);
                    let tracked mut gva = auth_au.tracked_borrow();
                    gva.agree(&gv);

                    assert(proto is Accepted);
                    assert(gva@ is Some);
                    let ghost au = gva@->0;
                    assert(au.resolves());
                }

                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_err() {
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
                self.pending.store(Tracked(&mut pend_perm), 0);

                proof {
                    let tracked mut gva = auth_au.tracked_take();
                    gva.update(&mut gv, None);
                    proto = Empty(gva);
                    v = (value_perm, pend_perm, auth, gv, proto);
                }
            });

            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }
}

} // verus!
