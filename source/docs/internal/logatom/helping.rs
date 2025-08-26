use vstd::atomic::*;
use vstd::tokens::frac::*;

// This is a simple example where concurrent processes help each other finish a task.
//
// In this example, the task we want to complete is flipping a boolean, which is not terribly
// interesting and can be done with a significantly less effort, but we use this operation
// as a placeholder for a more complicated operation on a concurrent datastructure.
//
// To allow processes to coordinate each other, there is an `pending` field, which keeps track of
// how many bit flips are currently in progress.

verus! {

type FlipAU = AtomicUpdate<FlagToken, FlagToken, FlipPred>;

type K = (int, int);
type V = (PermissionBool, PermissionU32, GhostVarAuth<bool>, Option<FlipAU>);

struct FlagInv;
impl InvariantPredicate<K, V> for FlagInv {
    spec fn inv(k: K, v: V) -> bool {
        &&& v.0@.id() == k.0
        &&& v.1@.id() == k.1
        &&& v.1@.value() < 3
    }
}

pub struct FlagToken {
    state: GhostVar<bool>,
}

pub struct Flag {
    value: PAtomicBool,
    pending: PAtomicU32,
    inv: Tracked<AtomicInvariant<K, V, FlagInv>>,
}

impl Flag {
    pub fn new() -> (Self, FlagToken) {
        let (value, Tracked(value_perm)) = AtomicBool::new(false);
        let (pending, Tracked(pending_perm)) = AtomicBool::new(0);
        let (Tracked(auth), Tracked(var)) = GhostVarAuth::new(false);
        let tracked inv = AtomicInvariant::new(
            (value.id(), pending.id()),
            (value_perm, pending_perm, auth, None),
            arbitrary()
        );

        let this = Self { value, pending, inv };
        let token = FlagToken { state: var };
        (this, token)
    }

    pub fn read(&self) -> bool {
        let out;
        open_atomic_invariant!(self.inv => v => {
            let tracked (mut flag_perm, mut pend_perm, mut other_au) = v;
            out = self.value.load(Tracked(&mut pend_perm));
            proof { v = (flag_perm, pend_perm, other_au); }
        });
        return out;
    }

    pub fn flip(&self)
        atomically (au) {
            type FlipPred,
            (old_token: FlagToken) -> (new_token: FlagToken),
            ensures new_token.state@ != new_token.state@,
        }
    {
        let tracked mut au = au;
        loop {
            match self.try_cancel_two_flips(au) {
                Err(upd) => au = upd,
                _ => return,
            }

            match self.try_simple_flip(au) {
                Err(upd) => au = upd,
                _ => return,
            }

            match self.try_handshake(au) {
                Err(upd) => au = upd,
                _ => return,
            }
        }
    }

    fn try_cancel_two_flips(&self, au: FlipAU) -> Result<(), FlipAU> {
        let res;

        open_atomic_invariant!(self.inv => v => {
            let tracked (mut flag_perm, mut pend_perm, mut other_au) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 2);
            proof { v = (flag_perm, pend_perm, other_au); }
        });

        if res.is_ok() {            
            open_atomic_invariant!(self.inv => v => {
                let tracked (mut flag_perm, mut pend_perm, mut auth, mut other_au) = v;
                let tracked other_au = other_au.tracked_unwrap();

                open_atomic_update!(au => token => {
                    let ghost old = auth@;
                    auth.update(&mut token.state, !old);
                    token
                });

                open_atomic_update!(other_au => token => {
                    let ghost old = auth@;
                    auth.update(&mut token.state, !old);
                    token
                });

                proof { v = (flag_perm, pend_perm, None); }
            });

            return Ok(());
        }

        Err(au)
    }

    fn try_simple_flip(&self, au: FlipAU) -> Result<(), FlipAU> {
        let res;
        open_atomic_invariant!(self.inv => v => {
            let tracked (mut flag_perm, mut pend_perm, mut other_au) = v;
            res = self.value.compare_exchange(Tracked(&mut flag_perm), true, false);
            proof { v = (flag_perm, pend_perm, other_au); }
        });

        if res.is_ok() {
            open_atomic_invariant!(self.inv => v => {
                open_atomic_update!(other_au => token => {
                    let ghost old = auth@;
                    auth.update(&mut token.state, !old);
                    token
                });
            });

            return Ok(());
        }

        let res;
        open_atomic_invariant!(self.inv => v => {
            let tracked (mut flag_perm, mut pend_perm, mut other_au) = v;
            res = self.value.compare_exchange(Tracked(&mut flag_perm), false, true);
            proof { v = (flag_perm, pend_perm, other_au); }
        });

        if res.is_ok() {
            open_atomic_invariant!(self.inv => v => {
                open_atomic_update!(other_au => token => {
                    let ghost old = auth@;
                    auth.update(&mut token.state, !old);
                    token
                });
            });

            return Ok(());
        }

        Err(au)
    }

    fn try_handshake(&self, au: FlipAU) -> Result<(), FlipAU> {
        let res;
        open_atomic_invariant!(self.inv => v => {
            let tracked (mut flag_perm, mut pend_perm, mut other_au) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 0, 1);
            proof { v = (flag_perm, pend_perm, other_au); }
        });

        if res.is_err() {
            return Err(au);
        }

        let res;
        open_atomic_invariant!(self.inv => v => {
            let tracked (mut flag_perm, mut pend_perm, mut other_au) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 0);
            proof { v = (flag_perm, pend_perm, other_au); }
        });

        if res.is_err() {
            open_atomic_invariant!(self.inv => v => {
                let tracked (mut flag_perm, mut pend_perm, mut other_au) = v;
                assert(other_au is None);

                self.pending.store(Tracked(&mut pend_perm), 0);
                proof { v = (flag_perm, pend_perm, Some(au)); }
            });

            return Ok(());
        }

        Err(au)
    }
}

} // verus!
