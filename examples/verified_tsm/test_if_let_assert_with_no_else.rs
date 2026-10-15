use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

pub struct Y {
    pub a: int,
    pub b: int,
}

verified_state_machine_model!{ X {
            fields {
                pub m: IMap<int, int>,
            }

            transition!{
                tr(x: int, y: int, z: int, b: bool) {
                    if b {
                        let k: int = 9;
                        assert(k == x) by { assume(false); };
                        update m[y] = 12;
                    }

                    update m[z] = 13;
                }
            }
        }}

spec fn tr_weak(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool) -> bool {
    (b ==> (x == 9)) ==> ((b ==> post.m =~= pre.m.insert(y, 12).insert(z, 13)) && (!b ==> post.m
        =~= pre.m.insert(z, 13)))
}

proof fn test(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool)
    ensures
        X::State::tr(pre, post, x, y, z, b) <==> tr_weak(pre, post, x, y, z, b),
{
}

spec fn tr_strong(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool) -> bool {
    (b ==> (x == 9)) && (b ==> post.m =~= pre.m.insert(y, 12).insert(z, 13)) && (!b ==> post.m
        =~= pre.m.insert(z, 13))
}

proof fn test2(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool)
    ensures
        X::State::tr_strong(pre, post, x, y, z, b) <==> tr_strong(pre, post, x, y, z, b),
{
}

fn main() {
}

} // verus!
