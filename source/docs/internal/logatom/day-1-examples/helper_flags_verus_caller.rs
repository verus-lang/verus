use vstd::prelude::*;

verus! {

//// Specification of FlagTracker as atomic operations

ghost struct FlagTrackerAbstractState {
    flag: bool,
}

impl FlagTrackerAbstractState {
    spec fn new() -> FlagTrackerAbstractState {
        FlagTrackerAbstractState {
            flag: false
        }
    }

    spec fn get(self) -> bool {
        self.flag
    }

    spec fn flip(self) -> FlagTrackerAbstractState {
        FlagTrackerAbstractState {
            flag: !self.flag,
        }
    }
}

pub struct FlagTracker { /* ... */ }

pub tracked struct FlagToken { /* ... */ }

impl FlagTracker {
    pub fn new() -> (res: (Self, FlagToken))
       ensures ({
            let (flag_tracker, token) = res;
            &&& flag_tracker.id() == token.id()
            &&& token.state() == FlagTrackerAbstractState::new(),
       });

    pub fn get(&self) -> (f: bool)
        atomic {
            with_tracked (tok: &FlagToken)
            requires tok.id() == self.id()
            ensures f == tok.state().get()
        };

    pub fn flip(&self) -> (f: bool)
        atomic {
            with_tracked (tok: &mut FlagToken)
            requires old(tok).id() == self.id()
            ensures tok.id() == self.id(),
                tok.state() == old(tok).state().flip()
        };
}

fn thread(flag: FlagTracker, ai: FlagAtomicInvariant) {
    open_atomic_invariant!(ai => flagt => {
        flag.flip() with (&mut flagt);
    })
}

fn main() {
    let (flag, Tracked(flagt)) = FlagTracker::new();
    assert(flagt.state().get() == false);
    let x = flag.get() with (&flagt); // return false
                                      //
    let tracked ai = FlagAtomicInvariant::new(flagt)

    let a = spawn(|| thread(flag, ai))
    let b = spawn(|| thread(flag, ai))

    a.join();
    b.join();

    let y = flag.get() with (&flagt); // return false
}

} // verus!
