use vstd::prelude::*;
use vstd::atomic::*;
use vstd::simple_pptr::*;
use vstd::invariant::*;

verus! {
struct ModPredicate {}

impl InvariantPredicate<AtomicCellId, PermissionU64> for ModPredicate {
    closed spec fn inv(k: AtomicCellId, v: PermissionU64) -> bool {
        &&& v.id() == k
        &&& v.value() as int % 2 == 0
    }
}

fn atomic_caller(
    inv: &AtomicInvariant<AtomicCellId, PermissionU64, ModPredicate>,
    patomic: PAtomicU64,
)
    requires inv.constant() == patomic.id(),
{
    
    let old_v;

    // assert PRIVATE PRE of fetch_add_plus_1
    let old_v = fetch_add_plus_1(3) atomically {
        open_atomic_invariant!(inv => permu64 => { 
            // assert ATOMIC PRE of fetch_add_plus_1
            now(&mut permu64)
            // assume ATOMIC POST of fetch_add_plus_1
        });
    };
    // assume PRIVATE POST of fetch_add_plus_1 at POST

    assert(old_v as int % 2 == 0);

}

fn non_atomic_caller() {
    let (p, Tracked(perm)) = AtomicU64::new(0);

    let old_v = fetch_add_plus_1(3) with (&mut perm);

    assert(perm.value() == 4);
}

fn fetch_add_plus_1(&self, v: u64)
    AU: atomic_spec {
        (tracked p: &mut PermissionU64)
        requires
            old(p).id() == self.id(),
        ensures
            p.id() == old(p).id(),
            p.value() == wrapping_add(
                old(p).value,
                wrapping_add(v, 1))
    }   
    returns old(p).value();
{   
    let w = wrapping_add(v, 1);

    self.fetch_add(w) atomically {
        open_atomic_update!(AU => points_to => {
            now(&mut points_to);
        };
    });
}
}
