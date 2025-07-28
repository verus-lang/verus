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

// AtomicUpdate
// open_atomic_update!
// 'atomically' syntax
// 'atomic' specs in pre-conditions and post-conditions

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
    let old_v = fetch_add_plus_1(patomic, 3) atomically {
        // transforming an atomic invariant into an atomic update
        open_atomic_invariant!(inv => permu64 => {
            /* open atomic update start */

            // assume inv's property
            assert(inv.inv(patomic.id(), permu64));
            assert(
              &&& permu64.id() == patomic.id()
              &&& permu64.value() as int % 2 == 0
            )

            // assert ATOMIC PRE of fetch_add_plus_1
            let ghost old_permu64 = permu64.value(); // 38
            assert(old_permu64 as int % 2 == 0);

            /* open atomic update end */
            now(&mut permu64) // the atomic operation
            /* close atomic update start */

            // assume ATOMIC POST of fetch_add_plus_1
            assert(
              &&& permu64.id() == patomic.id()
              &&& permu64.value() == wrapping_add_u64(old_permu64, 4) // 42
            )

            assert(permu64.value() as int % 2 == 0);
            // assert inv's property
            /* close atomic update end */
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

// at the linearisation point:
//   (reading the current value of the Atomic)PAtom,
//   adding (v + 1) to the value of the Atomic and wrapping if we overflow


fn fetch_add_plus_1(patomic: PAtomicU64, v: u64) -> (r: u64)
    // Tracked(AU): Tracked<AtomicUpdate<PermissionU64, PermissionU64>>
    atomic_update: atomic_spec { // AU indicates the linearisation point
        (tracked p: PermissionU64) -> (tracked out_p: PermissionU64)
        requires // ATOMIC PRE
            p.view().patomic == patomic.id(),
        ensures // ATOMIC POST
            out_p.view().id == p.id(),
            out_p.view().value == wrapping_add_u64(
                p.view().value,
                wrapping_add_u64(v, 1))
    }
    requires true, // PRIVATE PRE
    ensures r == p.view().value, // PRIVATE POST
{
    let w = wrapping_add_u64(v, 1);

    // assert PRIVATE PRE of fetch_add_wrapping
    let old_v = patomic.fetch_add_wrapping(w) atomically { update =>
        open_atomic_update!(atomic_update => (p: PermissionU64) => {
            // assume ATOMIC PRE of fetch_add_plus_1
            let ghost old_permu64 = p.view().value;

            // assert ATOMIC PRE of fetch_add_wrapping
            let (v, Tracked(out_p)) = update(p);
            // assume ATOMIC POST of fetch_add_wrapping

            return out_p; // -> (out_p: tracked PermissionU64)
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
// atomic_update: atomic_spec {
//   (tracked input_perm: APermissionU64) -> (tracked output_perm: APermissionU64)
//   requires // ATOMIC PRE
//     equal(self.id(), input_perm.view().patomic),
//   ensures { // ATOMIC POST
//     &&& output_perm.view().patomic == input_perm.view().patomic
//     &&& output_perm.view().value as int == wrapping_add_u64(input_perm.view().value as int, n as int)
//   }
// }
// requires true // PRIVATE PRE
// ensures // PRIVATE POST
//    equal(input_perm.view().value, ret),
