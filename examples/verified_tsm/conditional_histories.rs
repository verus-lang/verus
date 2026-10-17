//! Complete branching and scoped-let case from state_machines/conditional.rs.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub enum Foo {
    Bar(int),
    Qax(int),
    Duck(int),
}

verified_tokenized_state_machine!(

    X {
        fields {
            #[sharding(variable)]
            pub a: int,

            #[sharding(variable)]
            pub b: int,

            #[sharding(variable)]
            pub c: int,
        }

        init!{
            initialize(cond: bool) {
                init a = 0;
                init b = 1;
                if cond {
                    init c = 2;
                } else if cond {
                    init c = 3;
                } else {
                    init c = 4;
                }
            }
        }

        init!{
            initialize2(foo: Foo) {
                init a = 0;
                init b = 1;
                match foo {
                    Foo::Bar(x) => {
                        init c = 2;
                    }
                    Foo::Qax(y) => {
                        init c = 3;
                    }
                    Foo::Duck(z) => {
                        init c = 4;
                    }
                }
            }
        }

        transition!{
            add(n: int) {
                update a = 0;
                if n >= 0 {
                    update b = pre.b + n;
                } else {
                    update b = pre.b - n;
                    update c = 15;
                }
            }
        }

        transition!{
            add2(n: int) {
                update a = 0;
                if n >= 0 {
                    update c = 15;
                    update b = pre.b + n;
                } else {
                    update b = pre.b - n;
                }
            }
        }

        transition!{
            foo(n: int) {
                require(n >= 1);
                assert(n >= 1);
                let x: int = n + 2;
                if n >= 5 {
                    require(n < 10);
                    assert(x != 4);
                } else {
                    update c = 12;
                }
                require(n != 1001);
            }
        }

        #[inductive(foo)]
        fn foo_inductive(pre: Self, post: Self, n: int) { }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, cond: bool) { }

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, n: int) { }

        #[inductive(add2)]
        fn add2_inductive(pre: Self, post: Self, n: int) { }

    }
);

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut a), Tracked(mut b), Tracked(mut c)) =
            X::Instance::initialize(false);
        assert(c.value() == 4);
        instance.add(3, &mut a, &mut b, &mut c);
        assert(b.value() == 4);
        assert(c.value() == 4);
        instance.add(-2, &mut a, &mut b, &mut c);
        assert(b.value() == 6);
        assert(c.value() == 15);
        instance.add2(-2, &mut a, &mut b, &mut c);
        assert(b.value() == 8);
        instance.add2(2, &mut a, &mut b, &mut c);
        assert(b.value() == 10);
        instance.foo(2, &mut c);
        assert(c.value() == 12);
        instance.foo(6, &mut c);
        assert(c.value() == 12);
        let tracked (Tracked(instance), Tracked(a), Tracked(b), Tracked(bar)) =
            X::Instance::initialize2(Foo::Bar(9));
        assert(bar.value() == 2);
        let tracked (Tracked(instance), Tracked(a), Tracked(b), Tracked(qax)) =
            X::Instance::initialize2(Foo::Qax(9));
        assert(qax.value() == 3);
        let tracked (Tracked(instance), Tracked(a), Tracked(b), Tracked(duck)) =
            X::Instance::initialize2(Foo::Duck(9));
        assert(duck.value() == 4);
    }
}

} // verus!
