use vstd::prelude::*;
use vstd::atomic::*;
// use vstd::simple_pptr::*;
use vstd::logatom::AtomicUpdate;
use vstd::invariant::*;

verus! {
struct ModPredicate {}

impl InvariantPredicate<AtomicCellId, APermissionU64> for ModPredicate {
    closed spec fn inv(k: AtomicCellId, v: APermissionU64) -> bool {
        &&& v.view().patomic == k
        &&& v.view().value as int % 2 == 0
    }
}

fn atomic_caller(
    inv: &AtomicInvariant<AtomicCellId, APermissionU64, ModPredicate>,
    patomic: PAtomicU64,
)
    requires inv.constant() == patomic.id(),
{

    // assert PRIVATE PRE of fetch_add_plus_1
    // let old_v = fetch_add_plus_1(3) atomically {
    //     open_atomic_invariant!(inv => permu64 => {
    //         // assert ATOMIC PRE of fetch_add_plus_1
    //         now(&mut permu64)
    //         // assume ATOMIC POST of fetch_add_plus_1
    //     });
    // };
    // assume PRIVATE POST of fetch_add_plus_1 at POST
    //
    // assert(old_v as int % 2 == 0);

}

// fn non_atomic_caller() {
//     let (p, Tracked(perm)) = AtomicU64::new(0);
//
//     let old_v = fetch_add_plus_1(3) with (&mut perm);
//
//     assert(perm.value() == 4);
// }

fn fetch_add_plus_1(
    patomic: APAtomicU64,
    v: u64,

    /* (internal) */ Tracked(atomic_update): Tracked<AtomicUpdate<APermissionU64, APermissionU64>>,
    /* (internal) */ Tracked(input_perm): Tracked<APermissionU64>,
    ) -> (r: u64)


    // atomic_update: atomic_spec {
    //     (tracked p: APermissionU64) -> (tracked r: APermissionU64)
    //     requires // ATOMIC PRE
    //         p.id() == self.id(),
    //     ensures // ATOMIC POST
    //         r.id() == p.id(),
    //         r.value() == wrapping_add(
    //             p.value,
    //             wrapping_add(v, 1))
    // }
    // ensures r == p.view().value
{
    let tracked mut atomic_update = atomic_update;
    /* (internal) */ assume({
    /* (internal) */     &&& forall |input: APermissionU64| #![all_triggers] atomic_update.req(input) <==>
    /* (internal) */            input.view().patomic == patomic.id()
    /* (internal) */     &&& forall |input: APermissionU64, output: APermissionU64| #![all_triggers]
    /* (internal) */         atomic_update.ens(input, output) <==> {
    /* (internal) */             &&& output.view().patomic == input.view().patomic
    /* (internal) */             &&& output.view().value == wrapping_add_u64(input.view().value as int,
    /* (internal) */                    wrapping_add_u64(v as int, 1))
    /* (internal) */         }
    /* (internal) */     &&& atomic_update.has_fired() == false
    /* (internal) */ });

    assert(!atomic_update.has_fired());
    let w = v.wrapping_add(1);
    assert(w == wrapping_add_u64(v as int, 1));

    //     // assert PRIVATE PRE of fetch_add_wrapping
    /* (internal) */ assert(true);
    // let old_v2 = patomic.fetch_add_wrapping(w) atomically { update =>

    //     open_atomic_update!(atomic_update => permu64 => {
    /* (internal) */ assert(!atomic_update.has_fired());
    //     // assume ATOMIC PRE of atomic_update
    /* (internal) */ let tracked permu64: APermissionU64 =
                AtomicUpdate::<APermissionU64, APermissionU64>::assume_get_input();
    /* (internal) */ assume(atomic_update.req(permu64));
    assert(permu64.view().patomic == patomic.id());
    let ghost old_permu64 = permu64;

    //     // assert ATOMIC PRE of fetch_add_wrapping
    assert(equal(patomic.id(), permu64.view().patomic));
    //     let (v, Tracked(permu64)) = update(permu64); // atomic update of fetch_add_wrapping
    /* (internal) */ let tracked call_atomic_update: AtomicUpdate<APermissionU64, APermissionU64> =
        AtomicUpdate::<APermissionU64, APermissionU64>::assume_new();
    let (v2, Tracked(permu64)) = patomic.fetch_add_wrapping(w,

    /* (internal) */ Tracked(call_atomic_update),
    /* (internal) */ Tracked(permu64));
    //     // assume ATOMIC POST of fetch_add_wrapping
    /* (internal) */ assume(permu64.view().patomic == old_permu64.view().patomic);
    /* (internal) */ assume(permu64.view().value == wrapping_add_u64(old_permu64.view().value as int, w as int));
    assert(permu64.view().patomic == patomic.id());
    assert(permu64.view().value as int == wrapping_add_u64(old_permu64.view().value as int, w as int));
    //     // assert ATOMIC POST of atomic_update
    let ghost old_atomic_update = atomic_update;
    /* (internal) */ proof {
    /* (internal) */ atomic_update = AtomicUpdate::<APermissionU64, APermissionU64>::assume_new(); // havoc(atomic_update): forget everything about atomic_update
    /* (internal) */ }
    /* (internal) */ assume({
    /* (internal) */     &&& forall |input: APermissionU64| #![all_triggers]
    /* (internal) */         atomic_update.req(input) == old_atomic_update.req(input)
    /* (internal) */     &&& forall |input: APermissionU64, output: APermissionU64| #![all_triggers]
    /* (internal) */         atomic_update.ens(input, output) == old_atomic_update.ens(input, output)
    /* (internal) */ });
    /* (internal) */ assume(atomic_update.has_fired());
    assert(permu64.view().patomic == old_permu64.view().patomic);
    assert(permu64.view().value == wrapping_add_u64(old_permu64.view().value as int, wrapping_add_u64(v as int, 1)));
    /* (internal) */ assert(atomic_update.ens(old_permu64, permu64));
    //     }) // end of open_atomic_update!
    // };
    assume(v2 == old_permu64.view().value);

    v
}
}
