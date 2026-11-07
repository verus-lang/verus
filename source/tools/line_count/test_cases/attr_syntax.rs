use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;

verus! {

ghost struct EvenPredicate {}

impl InvariantPredicate<AtomicCellId, PermissionU32> for EvenPredicate {
    closed spec fn inv(id: AtomicCellId, perm: PermissionU32) -> bool {
        perm.id() == id && perm.value() % 2 == 0
    }
}

} // verus!

// #[verus_spec] with `with` parameters and outputs
#[verus_spec(r =>
    with
        Tracked(perm): Tracked<&PermissionU32>,
        Ghost(g): Ghost<u32>
        -> out: Ghost<u32>
    requires
        atomic.id() == perm.id(),
    ensures
        r == perm.value(),
)]
fn load(atomic: &PAtomicU32) -> u32 {
    proof_with!(Tracked(perm));
    let r = atomic.load(Tracked::assume_new());
    proof_with!(|= Ghost(g));
    r
}

// open_atomic_invariant_attr!
#[verus_spec(
    with
        Tracked(inv): Tracked<&AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>
    requires
        inv.constant() == atomic.id(),
)]
fn open_attr(atomic: &PAtomicU32) {
    let v;
    open_atomic_invariant_attr!(inv => perm => {
        proof_with!(Tracked(&perm));
        let x = atomic.load(Tracked::assume_new());
        v = x;
        proof! {
            assert(perm.value() % 2 == 0);
        }
    });
}

// #[verus_verify] on its own line is unaccounted, like the `verus! {` line
#[verus_verify]
struct S {
    x: u64,
    #[cfg(verus_keep_ghost_body)]
    perm: Tracked<PermissionU32>,
}

#[verus_verify]
enum E {
    A,
}

// specs on exec closures are spec
#[verus_spec]
fn closure() {
    let f = #[verus_spec(r =>
        ensures
            r == 7,
    )]
    || -> u64 {
        7
    };
    let x = f();
}

fn main() {}
