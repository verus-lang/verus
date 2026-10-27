use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::cell::CellId;
use vstd::simple_pptr::MemContents;

verus! {

ghost struct EvenPredicate {}

impl InvariantPredicate<AtomicCellId, PermissionU32> for EvenPredicate {
    closed spec fn inv(id: AtomicCellId, perm: PermissionU32) -> bool {
        perm.id() == id && perm.value() % 2 == 0
    }
}

ghost struct EvenCell {}

impl InvariantPredicate<CellId, PointsTo<u8>> for EvenCell {
    open spec fn inv(cell_id: CellId, points_to: PointsTo<u8>) -> bool {
        points_to.id() == cell_id
          && (match points_to.mem_contents() {
              MemContents::Uninit => false,
              MemContents::Init(x) => x % 2 == 0,
          })
    }
}

// open_atomic_invariant!

fn open_one(atomic: &PAtomicU32, i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>)
    requires
        i@.constant() == atomic.id(),
{
    open_atomic_invariant!(i.borrow() => perm => {
        let y: u32 = atomic.load(Tracked(&perm));
        assume(y < 1000);
        let ghost z: int = y as int * 2;
        proof {
            if y == 0 {
                assert(z == 0);
            }
        }
        assert(y % 2 == 0);
    });
}

fn open_nested(
    a: &PAtomicU32,
    b: &PAtomicU32,
    i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    j: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
)
    requires
        i@.constant() == a.id(),
        j@.constant() == b.id(),
        i@.namespace() != j@.namespace(),
{
    open_atomic_invariant!(i.borrow() => perm_i => {
        open_atomic_invariant!(j.borrow() => perm_j => {
            b.store(Tracked(&mut perm_j), 4);
            proof {
                let tracked tmp = perm_i;
                perm_i = tmp;
            }
        });
    });
}

// open_local_invariant!

fn add_2(cell: &PCell<u8>, Tracked(inv): Tracked<&LocalInvariant<CellId, PointsTo<u8>, EvenCell>>)
    requires inv.constant() == cell.id(),
{
    open_local_invariant!(inv => points_to => {
        assert(points_to.is_init());
        assert(points_to.value() % 2 == 0);

        let x = cell.take(Tracked(&mut points_to));
        assert(x % 2 == 0);

        // Add 2 (wrap around if necessary)
        let x_plus_2 = if x == 254 { 0 } else { x + 2 };

        cell.put(Tracked(&mut points_to), x_plus_2);

        assert(points_to.is_init());
        assert(points_to.value() % 2 == 0);
    });
}

// open_atomic_invariant_in_proof!

proof fn lemma_atomic_even(
    tracked credit: OpenInvariantCredit,
    tracked i: &AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>,
)
    opens_invariants any
{
    open_atomic_invariant_in_proof!(credit => i => perm => {
        let v = perm.value();
        let tracked tmp = perm;
        perm = tmp;
        assert(v % 2 == 0);
    });
}

// open_local_invariant_in_proof!

proof fn lemma_cell_even(
    tracked credit: OpenInvariantCredit,
    tracked inv: &LocalInvariant<CellId, PointsTo<u8>, EvenCell>,
)
    opens_invariants any
{
    open_local_invariant_in_proof!(credit => inv => points_to => {
        assert(points_to.is_init());
        let v = points_to.value();
        assert(v % 2 == 0);
    });
}

fn use_credits(
    i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    Tracked(inv): Tracked<&LocalInvariant<CellId, PointsTo<u8>, EvenCell>>,
) {
    let credit1 = create_open_invariant_credit();
    let credit2 = create_open_invariant_credit();
    proof {
        lemma_atomic_even(credit1.get(), i.borrow());
        lemma_cell_even(credit2.get(), inv);
    }
}

} // verus!
