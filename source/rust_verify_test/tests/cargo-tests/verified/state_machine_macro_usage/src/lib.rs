use vstd::prelude::*;
use verus_state_machines_macros::*;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::thread::*;

verus! {

state_machine!{ Y {
            fields {
                pub x: int,
                pub y: int,
                pub z: int,
            }

            init!{
                initialize(x: int, y: int, z: int) {
                    init x = x;
                    init y = y;
                    require(y <= z);
                    if x == y {
                        init z = z;
                    } else {
                        init z = z + 1;
                    }
                }
            }

            transition!{
                tr1(b: bool, c: bool) {
                    require(b);
                    assert(pre.y <= pre.z);
                    require(c);
                    update z = pre.z + 1;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool { self.y <= self.z }

            #[inductive(initialize)]
            fn init_inductive(post: Self, x: int, y: int, z: int) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self, b: bool, c: bool) { }

}}

} // verus!
