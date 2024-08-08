use vstd::prelude::*;
use vstd::atomic_ghost::*;
use vstd::cell;
use vstd::cell::*;
use vstd::modes::*;

verus!{

struct_with_invariants!{
    struct Lock<T> {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<T>>, _>,
        pub cell: PCell<T>,
    }

    spec fn wf(self) -> bool {
        invariant on atomic with (cell) is (v: bool, g: Option<cell::PointsTo<T>>) {
            match g {
                None => {
                    // When there's no PointsTo, the lock must be taken, thus
                    // the boolean value is 'true'.
                    v == true
                }
                Some(points_to) => {
                    points_to.id() == cell.id()
                      && points_to.is_init()
                      && v == false
                }
            }
        }
    }
}

impl<T> Lock<T> {
    fn new(t: T) -> (lock: Self)
        ensures lock.wf()
    {
        let (cell, Tracked(cell_perm)) = PCell::new(t);
        let atomic = AtomicBool::new(Ghost(cell), false, Tracked(Some(cell_perm)));
        Lock { atomic, cell }
    }

    fn acquire(&self) -> (points_to: Tracked<cell::PointsTo<T>>)
        requires self.wf(),
        ensures points_to@.id() == self.cell.id(), points_to@.is_init()
    {
        loop
            invariant self.wf(),
        {
            let tracked mut points_to_opt = None;
            let res = atomic_with_ghost!(&self.atomic => compare_exchange(false, true);
                ghost points_to_inv => {
                    tracked_swap(&mut points_to_opt, &mut points_to_inv);
                }
            );
            if res.is_ok() {
                return Tracked(points_to_opt.tracked_unwrap());
            }
        }
    }

    fn release(&self, points_to: Tracked<cell::PointsTo<T>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(), points_to@.is_init()
    {
        atomic_with_ghost!(&self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(points_to.get());
            }
        );
    }
}

}

fn main() { }
