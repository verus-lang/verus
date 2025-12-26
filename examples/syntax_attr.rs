#![feature(proc_macro_hygiene)]
#![allow(unused_imports)]

use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

fn main() {}

/// functions may be declared exec (default), proof, or spec, which contain
/// exec code, proof code, and spec code, respectively.
///   - exec code: compiled, may have requires/ensures
///   - proof code: erased before compilation, may have requires/ensures
///   - spec code: erased before compilation, no requires/ensures, but may have recommends
/// exec and proof functions may name their return values inside parentheses, before the return type
#[verus_spec(sum =>
    requires
        x < 100,
        y < 100,
    ensures
        sum < 200,
)]
fn my_exec_fun(x: u32, y: u32) -> u32
{
    x + y
}

verus! {

proof fn my_proof_fun(x: int, y: int) -> (sum: int)
    requires
        x < 100,
        y < 100,
    ensures
        sum < 200,
{
    x + y
}

spec fn my_spec_fun(x: int, y: int) -> int
    recommends
        x < 100,
        y < 100,
{
    x + y
}

} // verus!

/// exec code cannot directly call proof functions or spec functions.
/// However, exec code can contain proof blocks (proof { ... }),
/// which contain proof code.
/// This proof code can call proof functions and spec functions.
#[verus_spec(
    requires
        x < 100,
        y < 100,
)]
fn test_my_funs(x: u32, y: u32)
{
    // my_proof_fun(x, y); // not allowed in exec code
    // let u = my_spec_fun(x, y); // not allowed exec code
    proof! {
        let u = my_spec_fun(x as int, y as int);  // allowed in proof code
        my_proof_fun(u / 2, y as int);  // allowed in proof code
    }
}

verus! {

/// spec functions with pub or pub(...) must specify whether the body of the function
/// should also be made publicly visible (open function) or not visible (closed function).
pub open spec fn my_pub_spec_fun1(x: int, y: int) -> int {
    // function and body visible to all
    x / 2 + y / 2
}

/* TODO
pub open(crate) spec fn my_pub_spec_fun2(x: u32, y: u32) -> u32 {
    // function visible to all, body visible to crate
    x / 2 + y / 2
}
*/

// TODO(main_new) pub(crate) is not being handled correctly
// pub(crate) open spec fn my_pub_spec_fun3(x: int, y: int) -> int {
//     // function and body visible to crate
//     x / 2 + y / 2
// }
pub closed spec fn my_pub_spec_fun4(x: int, y: int) -> int {
    // function visible to all, body visible to module
    x / 2 + y / 2
}

pub(crate) closed spec fn my_pub_spec_fun5(x: int, y: int) -> int {
    // function visible to crate, body visible to module
    x / 2 + y / 2
}

} // verus!

/// Recursive functions must have decreases clauses so that Verus can verify that the functions
/// terminate.
#[verus_spec(
    requires
        0 < x < 100,
        y < 100 - x,
    decreases x,
)]
fn test_rec(x: u64, y: u64)
{
    if x > 1 {
        test_rec(x - 1, y + 1);
    }
}

verus! {

/// Multiple decreases clauses are ordered lexicographically, so that later clauses may
/// increase when earlier clauses decrease.
spec fn test_rec2(x: int, y: int) -> int
    decreases x, y,
{
    if y > 0 {
        1 + test_rec2(x, y - 1)
    } else if x > 0 {
        2 + test_rec2(x - 1, 100)
    } else {
        3
    }
}

/// To help prove termination, recursive spec functions may have embedded proof blocks
/// that can make assertions, use broadcasts, and call lemmas.
spec fn test_rec_proof_block(x: int, y: int) -> int
    decreases x,
{
    if x < 1 {
        0
    } else {
        proof {
            assert(x - 1 >= 0);
        }
        test_rec_proof_block(x - 1, y + 1) + 1
    }
}

/// Decreases and recommends may specify additional clauses:
///   - decreases .. "when" restricts the function definition to a condition
///     that makes the function terminate
///   - decreases .. "via" specifies a proof function that proves the termination
///     (although proof blocks are usually simpler; see above)
///   - recommends .. "when" specifies a proof function that proves the
///     recommendations of the functions invoked in the body
spec fn add0(a: nat, b: nat) -> nat
    recommends
        a > 0,
    via add0_recommends
{
    a + b
}

spec fn dec0(a: int) -> int
    decreases a,
    when a >= 0
    via dec0_decreases
{
    if a > 0 {
        dec0(a - 1)
    } else {
        0
    }
}

#[via_fn]
proof fn add0_recommends(a: nat, b: nat) {
    // proof
}

#[via_fn]
proof fn dec0_decreases(a: int) {
    // proof
}

} // verus!

/// variables may be exec, tracked, or ghost
///   - exec: compiled
///   - tracked: erased before compilation, checked for lifetimes (advanced feature, discussed later)
///   - ghost: erased before compilation, no lifetime checking, can create default value of any type
/// Different variable modes may be used in different code modes:
///   - variables in exec code are always exec
///   - variables in proof code are ghost by default (tracked variables must be marked "tracked")
///   - variables in spec code are always ghost
/// For example:
#[verus_spec(
    requires
        a < 100,
        b < 100,
)]
fn test_my_funs2(
    a: u32,  // exec variable
    b: u32,  // exec variable
)
{
    let s = a + b;  // s is an exec variable
    proof! {
        let u = a + b;  // u is a ghost variable
        my_proof_fun(u / 2, b as int);  // my_proof_fun(x, y) takes ghost parameters x and y
    }
}

verus! {

/// assume and assert are treated as proof code even outside of proof blocks.
/// "assert by" may be used to provide proof code that proves the assertion.
#[verifier::opaque]
spec fn f1(i: int) -> int {
    i + 1
}

} // verus!

#[verus_spec()]
fn assert_by_test() {
    proof! {
        assert(f1(3) > 3) by {
            reveal(f1);  // reveal f1's definition just inside this block
        }
        assert(f1(3) > 3);
    }
}

/// "assert by" can also invoke specialized provers for bit-vector reasoning or nonlinear arithmetic.
#[verus_spec()]
fn assert_by_provers(x: u32) {
    proof! {
        assert(x ^ x == 0u32) by (bit_vector);
        assert(2 <= x && x < 10 ==> x * x > x) by (nonlinear_arith);
    }
}

verus! {

/// "let ghost" currently requires the verus! macro
/// Variables in exec code may be exec, ghost, or tracked.
fn test_ghost(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    let ghost u: int = my_spec_fun(x as int, y as int);
    let ghost mut v = u + 1;
    assert(v == x + y + 1);
    proof {
        v = v + 1;  // proof code may assign to ghost mut variables
    }
    let ghost w = {
        let temp = v + 1;
        temp + 1
    };
    assert(w == x + y + 4);
}

/// Ghost(...) expressions and patterns currently require the verus! macro
/// Ghost(...) and Tracked(...) patterns can unwrap Ghost<...> and Tracked<...> values:
fn test_ghost_unwrap(
    x: u32,
    Ghost(y): Ghost<u32>,
)  // unwrap so that y has typ u32, not Ghost<u32>
    requires
        x < 100,
        y < 100,
{
    // Ghost(u) pattern unwraps Ghost<...> values and gives u and v type int:
    let Ghost(u): Ghost<int> = Ghost(my_spec_fun(x as int, y as int));
    let Ghost(mut v): Ghost<int> = Ghost(u + 1);
    assert(v == x + y + 1);
    proof {
        v = v + 1;  // assign directly to ghost mut v
    }
    let Ghost(w): Ghost<int> = Ghost(
        {
            // proof block that returns a ghost value
            let temp = v + 1;
            temp + 1
        },
    );
    assert(w == x + y + 4);
}

} // verus!

/// Trait functions may have specifications
trait T {
    #[verus_spec(r =>
        requires
            0 <= i < 10,
            0 <= j < 10,
        ensures
            i <= r,
            j <= r,
    )]
    fn my_uninterpreted_fun2(&self, i: u8, j: u8) -> u8;
}

#[verus_spec(ret =>
    with
        Tracked(y): Tracked<&mut u32>, Ghost(w): Ghost<u64> -> z: Ghost<u32>
    requires
        x < 100,
        *old(y) < 100,
    ensures
        *y == x,
        ret == x,
        z == x,
)]
fn test_mut_tracked(x: u32) -> u32 {
    proof!{
        *y = x;
    }
    #[verus_spec(with |=Ghost(x))]
    x
}

fn test_cal_mut_tracked(x: u32) {
    proof_decl!{
        let ghost mut z;
        let tracked mut y = 0u32;
        z = 0u32;
    }
    #[verus_spec(with Tracked(&mut y), Ghost(0) => Ghost(z))]
    let _ = test_mut_tracked(0u32);

    (#[verus_spec(with Tracked(&mut y), Ghost(0))]
    test_mut_tracked(0u32));

    return;
}