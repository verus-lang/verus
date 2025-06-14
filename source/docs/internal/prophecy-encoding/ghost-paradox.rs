use builtin::*;
use builtin_macros::verus;

verus! {

fn main() {
    let mut a: Ghost<bool> = Ghost(true);
    let mut a_ref: &mut Ghost<nat> = &mut a;
    *a_ref = Ghost(!a@);
    finalize_mut_ref(a_ref); // i.e. resolve
    regain_access(a);
    assert(false);
}

} // verus!
