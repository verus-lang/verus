// rust_verify/tests/example.rs ignore --- incomplete proof
use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::tokens::frac::*;

verus! {

type FlipAU = AtomicUpdate<FlagToken, FlagToken, FlipPred>;

enum Protocol {
    Empty,
    Offering(GhostVar<FlipAU>, Tracked<FlipAU>),
    Accepted(GhostVar<FlipAU>),
}

type K = (int, int, int);
type V = (PermissionBool, PermissionU32, GhostVarAuth<bool>, Option<FlipAU>);

pub struct FlagInv;
impl InvariantPredicate<K, V> for FlagInv {
    open spec fn inv(k: K, v: V) -> bool {
        let (value_id, pend_id, auth_id) = k;
        let (value_perm, pend_perm, auth, stored_au) = v;

        &&& value_perm.id() == value_id
        &&& pend_perm.id() == pend_id
        &&& auth.id() == auth_id
        &&& pend_perm.value() < 3
        &&& stored_au is Some <==> pend_perm.value() == 1
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
        let tracked (auth, var) = GhostVarAuth::new(false);
        let tracked inv = AtomicInvariant::new(
            (value.id(), pending.id(), auth.id()),
            (value_perm, pending_perm, auth, None),
            arbitrary()
        );

        let this = Self { value, pending, inv: Tracked(inv) };
        let tracked token = FlagToken { value: var };
        (this, Tracked(token))
    }

    pub fn read(&self) -> bool
        requires self.wf(),
    {
        let out;
        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut other_au) = v;
            out = self.value.load(Tracked(&value_perm));
            proof { v = (value_perm, pend_perm, auth, other_au); }
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
            vstd::atomic::pred_args::<FlipPred, &Flag>(au.pred()) == self,
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut maybe_other_au) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 2);

            proof {
                if res.is_ok() {
                    let tracked other_au = maybe_other_au.tracked_take();
                    let tracked au = maybe_au.tracked_take();

                    open_atomic_update!(au, mut token => {
                        let ghost old = auth@;
                        auth.update(&mut token.value, !old);
                        token
                    });

                    open_atomic_update!(other_au, mut token => {
                        let ghost old = auth@;
                        auth.update(&mut token.value, !old);
                        token
                    });
                }

                v = (value_perm, pend_perm, auth, maybe_other_au);
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
            vstd::atomic::pred_args::<FlipPred, &Flag>(au.pred()) == self,
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut other_au) = v;
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

                v = (value_perm, pend_perm, auth, other_au);
            }
        });

        if res.is_ok() {
            return None;
        }

        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut other_au) = v;
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

                v = (value_perm, pend_perm, auth, other_au);
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
            vstd::atomic::pred_args::<FlipPred, &Flag>(au.pred()) == self,
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut stored_au) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 0, 1);

            proof {
                if res.is_ok() {
                    let tracked au = maybe_au.tracked_take();
                    assert(stored_au is None);
                    stored_au = Some(au);
                }

                v = (value_perm, pend_perm, auth, stored_au);
            }
        });

        if res.is_err() {
            return Some(Tracked(maybe_au.tracked_take()));
        }

        let res;
        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut stored_au) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 0);

            proof {
                if res.is_ok() {
                    let tracked au = stored_au.tracked_take();
                    assert(maybe_au is None);
                    maybe_au = Some(au);
                }

                v = (value_perm, pend_perm, auth, stored_au);
            }
        });

        if res.is_err() {
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked (mut value_perm, mut pend_perm, mut auth, mut stored_au) = v;
                self.pending.store(Tracked(&mut pend_perm), 0);
                proof { v = (value_perm, pend_perm, auth, stored_au); }
            });

            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }
}

} // verus!
