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
    /* (internal) */ assume({
    /* (internal) */     &&& forall |input: APermissionU64| #![all_triggers] atomic_update.req(input) <==>
    /* (internal) */            input.view().patomic == patomic.id()
    /* (internal) */     &&& forall |input: APermissionU64, output: APermissionU64| #![all_triggers]
    /* (internal) */         atomic_update.ens(input, output) <==> {
    /* (internal) */             &&& output.view().patomic == input.id()
    /* (internal) */             &&& output.view().value == wrapping_add_u64(input.view().value as int,
    /* (internal) */                    wrapping_add_u64(v as int, 1))
    /* (internal) */         }
    /* (internal) */     &&& atomic_update.has_fired() == false
    /* (internal) */ });

    assert(!atomic_update.has_fired());
    let w = v.wrapping_add(1);
    assert(w == wrapping_add_u64(v as int, 1));

    // WIP:
    // let old_v = patomic.fetch_add_wrapping(w) atomically {
    //     open_atomic_update!(atomic_update => permu64 => {
    //     // assume ATOMIC PRE of fetch_add_plus_1
    //     assert(permu64.id() == patomic.id());
    //     let ghost old_permu64 = permu64.view().value();
    //     // assert ATOMIC PRE of fetch_add_wrapping
    //     atomic_update(&mut permu64);
    //     // assume ATOMIC POST of fetch_add_wrapping
    //     assert(permu64.id() == patomic.id());
    //     assert(permu64.view().value() as int ==
    //         wrapping_add_u64(old_permu64 as int, n as int)),
    //     // assert ATOMIC POST of fetch_add_plus_1
    //     })
    // };

    /* (internal) */ {
        /* (internal) */ let tracked permu64: APermissionU64 =
            AtomicUpdate::<APermissionU64, APermissionU64>::assume_get_input();
        /* (internal) */ assume(atomic_update.req(permu64));
        // TODO change assert(permu64.id() == patomic.id());


        /* (internal) */ let tracked permu64: APermissionU64 =
            AtomicUpdate::<APermissionU64, APermissionU64>::assume_get_input();
        patomic.fetch_add_wrapping(w
        
        /* (internal) */ Tracked(atomic_update),
        /* (internal) */ Tracked(input_perm));
    }
    // }

    // self.fetch_add(w) atomically {
    //     open_atomic_update!(AU => points_to => {
    //         now(&mut points_to);
    //     };
    // });
    assume(false);
    unreached()
}
}
