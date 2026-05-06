#![allow(unused_imports)]

use super::super::invariant::*;
use super::super::predicate::*;
use super::super::prelude::*;
use super::CellId;
use super::pcell::*;

use verus as verus_;
verus_! {

/** Verus's closest analogue of [`Cell`](std::cell::Cell).

An `InvCell` always allows reading and writing, even through a shared reference.
To reason about the value in an `InvCell`, the client must specify an "invariant predicate"
to constrain the allowed values.

### Examples

On construction of an `InvCell`, we can specify an invariant for the object that goes inside.
One way to do this is by providing a `spec_fn`, which implements the [`Predicate`] trait.

```rust,ignore
fn example1() {
    // We can create a cell with an invariant: `v == 5 || v == 13`.
    // Thus only 5 or 13 can be stored in the cell.
    let cell = InvCell::<u64, spec_fn(u64) -> bool>::new(5, Ghost(|v| v == 5 || v == 13));

    let ref1 = &cell;
    let ref2 = &cell;

    let x = ref1.get();
    assert(x == 5 || x == 13);

    ref1.set(13);

    let y = ref2.get();
    assert(y == 5 || y == 13);
}
```

It's often easier to implement the [`Predicate`] trait yourself. This way you can
have a configurable predicate without needing to work with higher-order functions.

```rust,ignore
pub struct FixedParity {
    pub parity: int,
}

impl Predicate<u64> for FixedParity {
    open spec fn predicate(&self, v: u64) -> bool {
        v % 2 == self.parity
    }
}

fn example2() {
    // Create a cell that can only store even integers
    let cell_even = InvCell::<u64, FixedParity>::new(20, Ghost(FixedParity { parity: 0 }));

    // Create a cell that can only store odd integers
    let cell_odd = InvCell::<u64, FixedParity>::new(23, Ghost(FixedParity { parity: 1 }));

    let x = cell_even.get();
    assert(x % 2 == 0);

    let y = cell_odd.get();
    assert(y % 2 == 1);
}
```
*/
#[verifier::accept_recursive_types(T)]
pub struct InvCell<T, Pred> {
    pcell: PCell<T>,
    perm_inv: Tracked<LocalInvariant<(Pred, CellId), PointsTo<T>, InvCellPred>>,
}

struct InvCellPred { }

impl<T, Pred: Predicate<T>> InvariantPredicate<(Pred, CellId), PointsTo<T>> for InvCellPred {
    closed spec fn inv(k: (Pred, CellId), perm: PointsTo<T>) -> bool {
        let (pred, pcell_id) = k;
        {
            &&& pred.predicate(*perm.value())
            &&& pcell_id === perm.id()
        }
    }
}

impl<T, Pred> InvCell<T, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.perm_inv@.constant().1 === self.pcell.id()
    }

    pub closed spec fn predicate(&self) -> Pred {
        self.perm_inv@.constant().0
    }
}

impl<T, Pred: Predicate<T>> InvCell<T, Pred> {
    pub open spec fn inv(&self, val: T) -> bool {
        self.predicate().predicate(val)
    }

    pub fn new(val: T, Ghost(pred): Ghost<Pred>) -> (cell: Self)
        requires
            pred.predicate(val),
        ensures
            cell.predicate() == pred,
    {
        let (pcell, Tracked(perm)) = PCell::new(val);
        let tracked perm_inv = LocalInvariant::new((pred, pcell.id()), perm, 0);
        InvCell { pcell, perm_inv: Tracked(perm_inv) }
    }

    pub fn set(&self, val: T)
        requires
            self.inv(val),
    {
        let _ = self.replace(val);
    }

    pub fn replace(&self, val: T) -> (old_val: T)
        requires
            self.inv(val),
        ensures
            self.inv(old_val),
    {
        proof {
            use_type_invariant(self);
        }
        let r;
        open_local_invariant!(self.perm_inv.borrow() => perm => {
            r = self.pcell.replace(Tracked(&mut perm), val);
        });
        r
    }

    pub fn get(&self) -> (val: T)
        where T: Copy
        ensures
            self.inv(val),
    {
        proof {
            use_type_invariant(self);
        }
        let r;
        open_local_invariant!(self.perm_inv.borrow() => perm => {
            r = *self.pcell.borrow(Tracked(&perm));
        });
        r
    }

    #[allow(non_shorthand_field_patterns)]
    pub fn into_inner(self) -> (val: T)
        ensures
            self.inv(val),
    {
        proof {
            use_type_invariant(&self);
        }
        let InvCell { pcell, perm_inv: Tracked(perm_inv) } = self;
        let tracked perm = perm_inv.into_inner();
        pcell.into_inner(Tracked(perm))
    }
}

}
