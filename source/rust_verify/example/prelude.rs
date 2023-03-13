#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[cfg(not(vstd_todo))]
mod pervasive;
#[cfg(not(vstd_todo))]
use pervasive::prelude::*;

#[cfg(vstd_todo)]
use vstd::prelude::*;

verus! {
    proof fn lemma() {
        let a: Seq<nat> = seq![1, 2, 3];
        assert(a[1] == 2);
    }

    fn main() {}
}
