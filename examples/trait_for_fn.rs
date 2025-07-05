use vstd::prelude::*;

verus! {

trait IntFn {
    spec fn call_int(&self, x: int) -> int;
}

impl IntFn for spec_fn(int) -> int {
    spec fn call_int(&self, x: int) -> int {
        self(x)
    }
}

proof fn use_IntFn() {
    let f: spec_fn(int) -> int = |x: int| x + 1;
    assert(f.call_int(2) == 3);
}

fn main() {
}

} // verus!
