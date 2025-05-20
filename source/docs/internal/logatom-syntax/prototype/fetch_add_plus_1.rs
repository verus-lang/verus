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

// Atomic invariant
// +----------------+
// | PermissionU64  |
// +----------------+

fn atomic_caller(
    inv: &AtomicInvariant<AtomicCellId, PermissionU64, ModPredicate>,
    patomic: PAtomicU64,
)
    requires inv.constant() == patomic.id(),
{
    
    // assert PRIVATE PRE of fetch_add_plus_1
    let old_v = patomic.fetch_add_plus_1(3) atomically {
        open_atomic_invariant!(inv => permu64 => { 
            // assume inv's property
            assert(inv.inv(patomic.id(), permu64));
            assert(
              &&& permu64.id() == patomic.id()
              &&& permu64.value() as int % 2 == 0
            )
            // ✅ assert ATOMIC PRE of fetch_add_plus_1
            let ghost old_permu64 = permu64.value(); // 38
            assert(old_permu64 as int % 2 == 0);
            now(&mut permu64) // the atomic operation
            // assume ATOMIC POST of fetch_add_plus_1
            assert(
              &&& permu64.id() == patomic.id()
              // &&& permu64.value() == wrapping_add_u64(old_permu64, wrapping_add_u64(3, 1))
              &&& permu64.value() == wrapping_add_u64(old_permu64, 4) // 42
            )
            assert(permu64.value() as int % 2 == 0);
            // assert inv's property
        });
    };
    // assume PRIVATE POST of fetch_add_plus_1 at POST
    assert(old_v as int % 2 == 0);

}

fn non_atomic_caller() {
    let (p, Tracked(perm)) = AtomicU64::new(0);

    // assert PRIVATE PRE of fetch_add_plus_1
    // assert ATOMIC PRE of fetch_add_plus_1
    let old_v = fetch_add_plus_1(3) with (&mut perm);
    // assume ATOMIC POST of fetch_add_plus_1
    // assume PRIVATE POST of fetch_add_plus_1

    assert(perm.value() == 4);
}

// at the linarization point:
//   (reading the current value of the Atomic),
//   adding (v + 1) to the value of the Atomic and wrapping if we overflow


fn fetch_add_plus_1(patomic: PAtomicU64, v: u64) -> (r: u64)
    // Tracked(AU): Tracked<AtomicUpdate<PermissionU64, PermissionU64>>
    AU: atomic_spec { // AU indicates the linearization point
        (tracked p: PermissionU64) -> (out_p: tracked PermissionU64)
        requires // ATOMIC PRE
            p.id() == patomic.id(),
        ensures // ATOMIC POST
            out_p.id() == p.id(),
            out_p.value() == wrapping_add_u64(
                p.value,
                wrapping_add_u64(v, 1))
    }
    // requires
    //     forall |p| AU.req(p) <==> p.id() == self.id(),
    //     forall |p| AU.ens(p) <==> (out_p.id() == p.id() && ...),

    // AU: AtomicSpec
    //   (tracked p: &mut PermissionU64)
    //
    //   has_fired:
    requires true, // PRIVATE PRE
    ensures r == p.view().value, // PRIVATE POST
{   
    

    let w = wrapping_add_u64(v, 1);

    let old_v = patomic.fetch_add_wrapping(w) atomically {
        open_atomic_update!(AU => permu64 => {
            // assume ATOMIC PRE of fetch_add_plus_1
            assert(permu64.id() == patomic.id());
            // assert ATOMIC PRE of fetch_add_wrapping
            let ghost old_permu64 = permu64.view().value();
            now(&mut permu64);
            // assume ATOMIC POST of fetch_add_wrapping
            assert(permu64.id() == patomic.id());
            assert(permu64.view().value() as int ==
                wrapping_add_u64(old_permu64 as int, n as int)),
            // assert ATOMIC POST of fetch_add_plus_1
        });
    };
    // assume PRIVATE POST of fetch_add_plus_1
    
    old_v
}
}

// pub exec fn fetch_add_wrapping(
//     &self,
//     n: u64,
// ) -> ret : u64
// atomic_spec {
//   (perm: Tracked<&mut PermissionU64>),
//   requires // ATOMIC PRE
//     equal(self.id(), old(perm).view().patomic),
//   ensures // ATOMIC POST
//     perm.view().patomic == old(perm).view().patomic,
//     perm.view().value as int == wrapping_add_u64(old(perm).view().value as int, n as int),
// }
// requires true // PRIVATE PRE
// ensures equal(old(perm).view().value, ret), // PRIVATE POST
