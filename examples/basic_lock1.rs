#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::cell::pcell;
use vstd::cell::CellId;
use vstd::atomic;
use vstd::modes::*;

verus!{

struct LockInv { }
impl<T> InvariantPredicate<(AtomicCellId, CellId), (atomic::PermissionBool, Option<pcell::PointsTo<T>>)> for LockInv {
    open spec fn inv(
        cell_ids: (AtomicCellId, CellId),
        ghost_stuff: (atomic::PermissionBool, Option<pcell::PointsTo<T>>),
    ) -> bool {
        ghost_stuff.0.id() == cell_ids.0
        && match ghost_stuff.1 {
            None => {
                // When there's no PointsTo, the lock must be taken, thus
                // the boolean value is 'true'.
                ghost_stuff.0.value() == true
            }
            Some(points_to) => {
                points_to.id() == cell_ids.1
                  && ghost_stuff.0.value() == false
            }
        }
    }
}

struct Lock<T> {
    pub atomic: PAtomicBool,
    pub cell: pcell::PCell<T>,
    pub inv: Tracked<AtomicInvariant<
        (AtomicCellId, CellId),
        (atomic::PermissionBool, Option<pcell::PointsTo<T>>),
        LockInv
    >>,
}

impl<T> Lock<T> {
    spec fn wf(self) -> bool {
        self.inv@.constant() == (self.atomic.id(), self.cell.id())
    }

    fn new(t: T) -> (lock: Self)
        ensures lock.wf()
    {
        let (atomic, Tracked(atomic_perm)) = PAtomicBool::new(false);
        let (cell, Tracked(cell_perm)) = pcell::PCell::new(t);
        let tracked inv = AtomicInvariant::new(
            (atomic.id(), cell.id()),
            (atomic_perm, Some(cell_perm)),
            1337);
        Lock { atomic, cell, inv: Tracked(inv) }
    }

    fn acquire(&self) -> (points_to: Tracked<pcell::PointsTo<T>>)
        requires self.wf(),
        ensures points_to@.id() == self.cell.id(),
    {
        loop
            invariant self.wf(),
        {
            let tracked points_to_opt = None;
            let res;
            open_atomic_invariant!(self.inv.borrow() => ghost_stuff => {
                let tracked (mut atomic_permission, mut points_to_inv) = ghost_stuff;
                res = self.atomic.compare_exchange(Tracked(&mut atomic_permission), false, true);
                proof {
                    tracked_swap(&mut points_to_opt, &mut points_to_inv);
                    ghost_stuff = (atomic_permission, points_to_inv);
                }
            });
            if res.is_ok() {
                return Tracked(points_to_opt.tracked_unwrap());
            }
        }
    }

    fn release(&self, points_to: Tracked<pcell::PointsTo<T>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(),
    {
        open_atomic_invariant!(self.inv.borrow() => ghost_stuff => {
            let tracked (mut atomic_permission, _) = ghost_stuff;
            self.atomic.store(Tracked(&mut atomic_permission), false);
            proof {
                ghost_stuff = (atomic_permission, Some(points_to.get()));
            }
        });
    }
}

}

fn main() { }
