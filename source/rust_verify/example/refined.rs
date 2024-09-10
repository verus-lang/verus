use vstd::prelude::*;
use vstd::refined::*;

verus! {
    pub struct T {
        pub a: u8,
    }

    pub struct TPred {
    }

    impl RefinedPred<T> for TPred {
        open spec fn valid(v: T) -> bool {
            v.a == 0 || v.a == 2
        }
    }

    pub fn test_t(Tracked(rx): Tracked<RefinedT::<T, TPred>>) -> (res: Tracked<RefinedT::<T, TPred>>) {
        proof {
            rx.validate();
        };
        assert(rx@.a < 3);
        assert(rx@.a != 1);
        let tracked mut res = rx;
        proof {
            let v = res.take();
            let tracked mut newv =
                if v.a == 0 {
                    T{ a: 2u8 }
                } else if v.a == 1 {
                    T{ a: 100u8 }
                } else {
                    T{ a: 0u8 }
                };
            res = RefinedT::alloc(newv)
        };
        Tracked(res)
    }

    pub fn test_g(Tracked(rx): Tracked<RefinedG::<T, TPred>>) -> (res: Tracked<RefinedG::<T, TPred>>) {
        proof {
            rx.validate();
        };
        assert(rx@.a < 3);
        assert(rx@.a != 1);
        let tracked mut res = rx;
        proof {
            let v = res.take();
            let mut newv =
                if v.a == 0 {
                    T{ a: 2u8 }
                } else if v.a == 1 {
                    T{ a: 100u8 }
                } else {
                    T{ a: 0u8 }
                };
            res = RefinedG::alloc(newv)
        };
        Tracked(res)
    }

    pub fn main() {
        let tracked x = T{a: 0u8};
        let tracked rx = RefinedT::<T, TPred>::alloc(x);
        let Tracked(rx) = test_t(Tracked(rx));
        proof {
            rx.validate();
        };
        assert(rx@.a < 3);

        let x = T{a: 0u8};
        let tracked rx = RefinedG::<T, TPred>::alloc(x);
        let Tracked(rx) = test_g(Tracked(rx));
        proof {
            rx.validate();
        };
        assert(rx@.a < 3);
    }
}
