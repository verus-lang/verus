#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::tokenized_state_machine;

tokenized_state_machine!(
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
        fn foo_inductive(pre: X, post: X, n: int) { }
       
        #[inductive(initialize)]
        fn initialize_inductive(post: X, cond: bool) { }
     
        #[inductive(add)]
        fn add_inductive(pre: X, post: X, n: int) { }
     
        #[inductive(add2)]
        fn add2_inductive(pre: X, post: X, n: int) { }

    }
);

fn main() { }
