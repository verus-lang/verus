// rust_verify/tests/example.rs ignore --- wip
#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::tokens::frac::*;
use std::sync::Arc;

verus! {

type K = (int, int, int);
type V = (PermissionU64, PermissionU64, GhostVarAuth<u64>);

pub struct CounterInv;
impl InvariantPredicate<K, V> for CounterInv {
    open spec fn inv(k: K, v: V) -> bool {
        let (primary_id, backup_id, count_id) = k;
        let (primary_perm, backup_perm, count_auth) = v;
        &&& primary_perm.id() == primary_id
        &&& backup_perm.id() == backup_id
        &&& count_auth.id() == count_id
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
        let (primary_id, backup_id, _) = k;
        &&& self.inner.primary.id() == primary_id
        &&& self.inner.backup.id() == backup_id
    }

    pub open spec fn token_id(self) -> int {
        let (.., count_id) = self.inner.inv@.constant();
        count_id
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn new() -> (out: (Self, Tracked<Token>))
        ensures
            out.0.wf(),
            out.0.token_id() == out.1@.id()
    {
        let (primary, Tracked(primary_perm)) = PAtomicU64::new(0);
        let (backup, Tracked(backup_perm)) = PAtomicU64::new(0);
        let tracked (count_auth, count) = GhostVarAuth::new(0);
        let tracked inv = AtomicInvariant::new(
            (primary.id(), backup.id(), count_auth.id()),
            (primary_perm, backup_perm, count_auth),
            2
        );

        let inner = Arc::new(Inner { inv: Tracked(inv), primary, backup });
        let handle = Arc::clone(&inner);

        vstd::thread::spawn(move || loop {
            let curr;
            open_atomic_invariant!(handle.inv.borrow() => v => {
                let tracked (mut primary_perm, mut backup_perm, mut count_auth) = v;
                curr = handle.primary.load(Tracked(&primary_perm));
                proof { v = (primary_perm, backup_perm, count_auth); }
            });

            open_atomic_invariant!(handle.inv.borrow() => v => {
                let tracked (mut primary_perm, mut backup_perm, mut count_auth) = v;
                handle.backup.store(Tracked(&mut backup_perm), curr);
                proof { v = (primary_perm, backup_perm, count_auth); }
            });
        });

        let tracked token = Token { count };
        let counter = Counter { inner };
        (counter, Tracked(token))
    }

    fn await_backup(&self, curr: u64)
        requires
            self.wf(),
    {
        loop {
            let backup;
            open_atomic_invariant!(self.inner.inv.borrow() => v => {
                let tracked (mut primary_perm, mut backup_perm, mut count_auth) = v;
                backup = self.inner.backup.load(Tracked(&backup_perm));
                proof { v = (primary_perm, backup_perm, count_auth); }
            });

            if backup >= curr {
                break;
            }
        }
    }

    pub fn increment(&self)
        requires
            self.wf(),
    {
        let prev;
        open_atomic_invariant!(self.inner.inv.borrow() => v => {
            let tracked (mut primary_perm, mut backup_perm, mut count_auth) = v;
            prev = self.inner.primary.fetch_add_wrapping(Tracked(&mut primary_perm), 1);
            proof { v = (primary_perm, backup_perm, count_auth); }
        });

        self.await_backup(prev.wrapping_add(1));
    }

    pub fn get(&self) -> u64
        requires
            self.wf(),
    {
        let curr;
        open_atomic_invariant!(self.inner.inv.borrow() => v => {
            let tracked (mut primary_perm, mut backup_perm, mut count_auth) = v;
            curr = self.inner.primary.load(Tracked(&primary_perm));
            proof { v = (primary_perm, backup_perm, count_auth); }
        });

        self.await_backup(curr);
        curr
    }
}

} // verus!
