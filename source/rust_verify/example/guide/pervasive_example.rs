#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

#[cfg(not(vstd_todo))]
mod pervasive;
#[cfg(not(vstd_todo))]
use pervasive::seq::*;

#[cfg(vstd_todo)]
use vstd::seq::*;

verus! {

fn main() {
    proof {
        let s: Seq<int> = seq![0, 10, 20, 30, 40];
        assert(s.len() == 5);
        assert(s[2] == 20);
        assert(s[3] == 30);
    }
}

} // verus!
