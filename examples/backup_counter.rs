// rust_verify/tests/example.rs ignore --- wip

#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::tokens::frac::*;
use std::sync::Arc;

verus! {

pub type IncrementAU = AtomicUpdate<Token, Token, IncrementPred>;

pub struct K {
    pub primary_id: int,
    pub backup_id: int,
    pub count_id: int,
    pub hist_id: int,
}

pub struct V {
    pub primary_perm: PermissionU64,
    pub backup_perm: PermissionU64,
    pub count_auth: GhostVarAuth<u64>,
    pub trail: Tracked<Seq<Option<IncrementAU>>>,
    pub hist: GhostVar<Seq<IncrementAU>>,
    pub hist_auth: Option<GhostVarAuth<Seq<IncrementAU>>>,
}

pub open spec const COUTER_INV: int = 2;

pub struct CounterInv;
impl InvariantPredicate<K, V> for CounterInv {
    open spec fn inv(k: K, v: V) -> bool {
        let K { primary_id, backup_id, count_id, hist_id } = k;
        let V { primary_perm, backup_perm, count_auth, trail, hist, hist_auth } = v;

        &&& primary_perm.id() == primary_id
        &&& backup_perm.id() == backup_id
        &&& count_auth.id() == count_id
        &&& hist.id() == hist_id
        &&& hist_auth is Some ==> hist_auth->0.id() == hist_id

        &&& primary_perm.value() == count_auth@
        &&& backup_perm.value() <= count_auth@
        &&& trail@.len() == count_auth@
        &&& hist@.len() == count_auth@

        &&& forall |k| 0 <= k < count_auth@ ==> match trail@[k] {
            Some(tr) => tr == #[trigger] hist@[k],
            None => #[trigger] hist@[k].resolves(),
        }
    }
}

pub struct Inner {
    pub inv: Tracked<AtomicInvariant<K, V, CounterInv>>,
    pub primary: PAtomicU64,
    pub backup: PAtomicU64,
}

pub struct Token {
    pub count: GhostVar<u64>,
}

impl Token {
    pub open spec fn id(self) -> int {
        self.count.id()
    }
}

pub struct Counter {
    pub inner: Arc<Inner>,
}

impl Counter {
    pub open spec fn wf(self) -> bool {
        let k = self.inner.inv@.constant();
        let K { primary_id, backup_id, .. } = k;
        &&& self.inner.primary.id() == primary_id
        &&& self.inner.backup.id() == backup_id
    }

    pub open spec fn token_id(self) -> int {
        let k = self.inner.inv@.constant();
        let K { count_id, .. } = k;
        count_id
    }

    pub fn new() -> (out: (Self, Tracked<Token>))
        ensures
            out.0.wf(),
            out.0.token_id() == out.1@.id()
    {
        let (primary, Tracked(primary_perm)) = PAtomicU64::new(0);
        let (backup, Tracked(backup_perm)) = PAtomicU64::new(0);
        let tracked (count_auth, count) = GhostVarAuth::new(0);
        let tracked (hist_auth, hist) = GhostVarAuth::new(Seq::empty());
        let tracked hist_auth = Some(hist_auth);
        let trail = Tracked(Seq::tracked_empty());

        let ghost primary_id = primary.id();
        let ghost backup_id = backup.id();
        let ghost count_id = count_auth.id();
        let ghost hist_id = hist.id();

        let inv = Tracked(AtomicInvariant::new(
            K { primary_id, backup_id, count_id, hist_id },
            V { primary_perm, backup_perm, count_auth, trail, hist, hist_auth },
            COUTER_INV,
        ));

        let inner = Arc::new(Inner { inv, primary, backup });
        let handle = Arc::clone(&inner);

        vstd::thread::spawn(move || loop {
            let curr;

            open_atomic_invariant!(handle.inv.borrow() => v => {
                let tracked V { mut primary_perm, mut backup_perm, mut count_auth, mut trail, mut hist, mut hist_auth } = v;
                curr = handle.primary.load(Tracked(&primary_perm));
                proof { v = V { primary_perm, backup_perm, count_auth, trail, hist, hist_auth }; }
            });

            open_atomic_invariant!(handle.inv.borrow() => v => {
                let tracked V { mut primary_perm, mut backup_perm, mut count_auth, mut trail, mut hist, mut hist_auth } = v;

                assert(backup_perm.value() <= primary_perm.value());
                assert(curr <= primary_perm.value());

                handle.backup.store(Tracked(&mut backup_perm), curr);
                proof { v = V { primary_perm, backup_perm, count_auth, trail, hist, hist_auth }; }
            });
        });

        let tracked token = Token { count };
        let counter = Counter { inner };
        (counter, Tracked(token))
    }

    fn await_backup(&self, curr: u64)
        requires self.wf(),
    {
        loop {
            let backup;
            open_atomic_invariant!(self.inner.inv.borrow() => v => {
                let tracked V { mut primary_perm, mut backup_perm, mut count_auth, mut trail, mut hist, mut hist_auth } = v;
                backup = self.inner.backup.load(Tracked(&backup_perm));
                proof { v = V { primary_perm, backup_perm, count_auth, trail, hist, hist_auth }; }
            });

            if backup >= curr {
                break;
            }
        }
    }

    pub fn increment(&self)
        atomically (au) {
            type IncrementPred,
            (old_token: Token) -> (new_token: Token),
            requires
                old_token.id() == self.token_id(),
            ensures
                new_token.id() == old_token.id(),
                new_token.count@ == old_token.count@ + 1,
        },
        requires
            self.wf(),
    {
        let prev;
        open_atomic_invariant!(self.inner.inv.borrow() => v => {
            let tracked V { mut primary_perm, mut backup_perm, mut count_auth, mut trail, mut hist, mut hist_auth } = v;
            prev = self.inner.primary.fetch_add_wrapping(Tracked(&mut primary_perm), 1);
            proof { v = V { primary_perm, backup_perm, count_auth, trail, hist, hist_auth }; }
        });

        self.await_backup(prev.wrapping_add(1));
    }

    // pub fn get(&self) -> u64
    //     requires
    //         self.wf(),
    // {
    //     let curr;
    //     open_atomic_invariant!(self.inner.inv.borrow() => v => {
    //         let tracked V { mut primary_perm, mut backup_perm, mut count_auth, mut trail, mut hist, mut hist_auth } = v;
    //         curr = self.inner.primary.load(Tracked(&primary_perm));
    //         proof { v = V { primary_perm, backup_perm, count_auth, trail, hist, hist_auth }; }
    //     });
    //
    //     self.await_backup(curr);
    //     curr
    // }
}

} // verus!
