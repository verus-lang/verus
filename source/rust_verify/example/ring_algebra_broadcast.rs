use vstd::prelude::*;

verus! {
mod ring {
    use builtin::*;

    pub struct Ring {
        pub i: nat,
    }

    impl Ring {
        pub closed spec fn inv(&self) -> bool {
            self.i < 10
        }

        pub closed spec fn succ(&self) -> Ring {
            Ring { i: if self.i == 9 { 0 } else { self.i + 1 } }
        }

        pub closed spec fn prev(&self) -> Ring {
            Ring { i: if self.i == 0 { 9 } else { (self.i - 1) as nat } }
        }
    }

    #[verifier::broadcast_forall]
    pub proof fn Ring_succ(p: Ring)
        requires p.inv()
        ensures p.inv() && (#[trigger] p.succ()).prev() == p
    { }

    #[verifier::broadcast_forall]
    pub proof fn Ring_prev(p: Ring)
        requires p.inv()
        ensures p.inv() && (#[trigger] p.prev()).succ() == p
    { }

    reveal_group! {
    pub Ring_properties =>
        Ring_succ,
        Ring_prev,
    }
}

mod m2 {
    use crate::ring::*;
    
    reveal Ring_properties;

    proof fn p1(p: Ring) requires p.inv() {
        assert(p.succ().prev() == p);
    }

    proof fn p2(p: Ring) requires p.inv() {
        assert(p.prev().succ() == p);
    }

    proof fn p3(p: Ring) requires p.inv() {
        assert(p.succ().prev() == p);
        assert(p.prev().succ() == p);
    }
}
}