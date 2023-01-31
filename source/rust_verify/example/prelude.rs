mod pervasive; use pervasive::prelude::*;

verus! {
    proof fn lemma() {
        let a: Seq<nat> = seq![1, 2, 3];
        assert(a[1] == 2);
    }

    fn main() {}
}

