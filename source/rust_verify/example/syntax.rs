#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::modes::*;

#[verifier(external)]
fn main() {
}

verus! {

/// functions may be declared exec (default), proof, or spec, which contain
/// exec code, proof code, and spec code, respectively.
///   - exec code: compiled, may have requires/ensures
///   - proof code: erased before compilation, may have requires/ensures
///   - spec code: erased before compilation, no requires/ensures, but may have recommends
/// exec and proof functions may name their return values inside parentheses, before the return type
fn my_exec_fun(x: u32, y: u32) -> (sum: u32)
    requires
        x < 100,
        y < 100,
    ensures
        sum < 200,
{
    x + y
}

proof fn my_proof_fun(x: u32, y: u32) -> (sum: u32)
    requires
        x < 100,
        y < 100,
    ensures
        sum < 200,
{
    x + y
}

spec fn my_spec_fun(x: u32, y: u32) -> u32
    recommends
        x < 100,
        y < 100,
{
    x + y
}

/// exec code cannot directly call proof functions or spec functions.
/// However, exec code can contain proof blocks (proof { ... }),
/// which contain proof code.
/// This proof code can call proof functions and spec functions.
fn test_my_funs(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    // my_proof_fun(x, y); // not allowed in exec code
    // let u = my_spec_fun(x, y); // not allowed exec code
    proof {
        let u = my_spec_fun(x, y); // allowed in proof code
        my_proof_fun(u / 2, y); // allowed in proof code
    }
}

/// variables may be exec, tracked, or ghost
///   - exec: compiled
///   - tracked: erased before compilation, checked for lifetimes (advanced feature, discussed later)
///   - ghost: erased before compilation, no lifetime checking, can create default value of any type
/// Different variable modes may be used in different code modes:
///   - variables in exec code are always exec
///   - variables in proof code are ghost by default (tracked variables must be marked "tracked")
///   - variables in spec code are always ghost
/// For example:
fn test_my_funs2(
    a: u32, // exec variable
    b: u32, // exec variable
)
    requires
        a < 100,
        b < 100,
{
    let s = a + b; // s is an exec variable
    proof {
        let u = a + b; // u is a ghost variable
        my_proof_fun(u / 2, b); // my_proof_fun(x, y) takes ghost parameters x and y
    }
}

/// assume and assert are treated as proof code even outside of proof blocks.
/// "assert by" may be used to provide proof code that proves the assertion.
#[verifier(opaque)]
spec fn f1(i: int) -> int {
    i + 1
}

fn assert_by_test() {
    assert(f1(3) > 3) by {
        reveal(f1); // reveal f1's definition just inside this block
    }
    assert(f1(3) > 3);
}

/// "assert by" can also invoke specialized provers for bit-vector reasoning or nonlinear arithmetic.
fn assert_by_provers(x: u32) {
    assert(x ^ x == 0) by(bit_vector);
    assert(2 <= x && x < 10 ==> x * x > x) by(nonlinear_arith);
}

/// "assert by" can use nonlinear_arith with proof code,
/// where "requires" clauses selectively make facts available to the proof code.
proof fn test5_bound_checking(x: u32, y: u32, z: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
        z <= 0xffff,
{
    assert((x as int) * (z as int) == ((x * z) as int)) by(nonlinear_arith)
        requires
            x <= 0xffff,
            z <= 0xffff,
    {
        assert(0 <= (x as int) * (z as int));
        assert((x as int) * (z as int) <= 0xffff * 0xffff);
    }
}

/// The syntax for forall and exists quantifiers is based on closures:
fn test_quantifier() {
    assert(forall|x: u32, y: u32| x < 100 && y < 100 ==> my_spec_fun(x, y) >= x);
    assert(my_spec_fun(10, 20) == 30);
    assert(exists|x: u32, y: u32| my_spec_fun(x, y) == 30);
}

/// "assert forall by" may be used to prove foralls:
fn test_assert_forall_by() {
    assert forall(x: int, y: int) f1(x) + f1(y) == x + y + 2 by {
        reveal(f1);
    }
    assert(f1(1) + f1(2) == 5);
    assert(f1(3) + f1(4) == 9);

    // to prove forall|...| P ==> Q, write assert forall(...) P implies Q by {...}
    assert forall(x: int) x < 10 implies f1(x) < 11 by {
        assert(x < 10);
        reveal(f1);
        assert(f1(x) < 11);
    }
    assert(f1(3) < 11);
}

/// To extract ghost witness values from exists, use choose:
fn test_choose() {
    assume(exists|x: int| f1(x) == 10);
    proof {
        let x_witness = choose|x: int| f1(x) == 10;
        assert(f1(x_witness) == 10);
    }

    assume(exists|x: int, y: int| f1(x) + f1(y) == 30);
    proof {
        let (x_witness, y_witness): (int, int) = choose|x: int, y: int| f1(x) + f1(y) == 30;
        assert(f1(x_witness) + f1(y_witness) == 30);
    }
}

/// &&& and ||| are like && and ||, but have low precedence (lower than all other binary operators).
/// &&& must appear before each conjunct, rather than between the conjuncts (similarly for |||).
spec fn simple_conjuncts(x: int, y: int) -> bool {
    &&& 1 < x
    &&& y > 9 ==> x + y < 50
    &&& x < 100
    &&& y < 100
}
spec fn complex_conjuncts(x: int, y: int) -> bool {
    let b = x < y;
    &&& b
    &&& if false {
            &&& b ==> b
            &&& !b ==> !b
        } else {
            ||| b ==> b
            ||| !b
        }
    &&& false ==> true
}

/// ==> associates to the right, while <== associates to the left.
/// <==> is nonassociative.
/// === is SMT equality (equivalent to the builtin equal function).
/// !== is SMT disequality.
pub(crate) proof fn binary_ops<A>(a: A, x: int) {
    assert(false ==> true);
    assert(true && false ==> false && false);
    assert(!(true && (false ==> false) && false));

    assert(false ==> false ==> false);
    assert(false ==> (false ==> false));
    assert(!((false ==> false) ==> false));

    assert(false <== false <== false);
    assert(!(false <== (false <== false)));
    assert((false <== false) <== false);
    assert(2 + 2 !== 3);
    assert(a === a);

    assert(false <==> true && false);
}

/// struct and enum declarations may be declared exec (default), tracked, or ghost,
/// and fields may be declared exec (default), tracked or ghost.
tracked struct TrackedAndGhost<T, G>(
    tracked T,
    ghost G,
);

/// Proof code may manipulate tracked variables directly.
/// Both declarations and uses of tracked variables must be explicitly marked as "tracked".
proof fn consume(tracked x: int) {
}

proof fn test_tracked(
    tracked w: int,
    tracked x: int,
    tracked y: int,
    z: int
) -> tracked TrackedAndGhost<(int, int), int> {
    consume(tracked w);
    let tracked tag: TrackedAndGhost<(int, int), int> = TrackedAndGhost((tracked x, tracked y), z);
    let tracked TrackedAndGhost((a, b), c) = tracked tag;
    TrackedAndGhost((tracked a, tracked b), c)
}

/// Variables in exec code are always exec; ghost and tracked variables are not available directly.
/// Instead, the library types Ghost and Tracked are used to wrap ghost values and tracked values.
/// Ghost and tracked expressions ghost(expr) and tracked(expr) create values of type Ghost<T>
/// and Tracked<T>, where expr is treated as proof code whose value is wrapped inside Ghost or Tracked.
fn test_ghost(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    let u: Ghost<u32> = ghost(my_spec_fun(x, y));
    let mut v: Ghost<u32> = ghost(*u + 1);
    assert(*v == x + y + 1);
    proof {
        v = Ghost::new(*v + 1); // proof code may assign to exec variables of type Ghost/Tracked
    }
    let w: Ghost<u32> = ghost({
        // proof block that returns a ghost value
        let temp = *v + 1;
        temp + 1
    });
    assert(*w == x + y + 4);
}

/* TODO
fn test_consume(t: Tracked<int>)
    requires *t <= 7
{
    proof {
        let tracked x = t.get();
        assert(x <= 7);
        consume(tracked x);
    }
}
*/

} // verus!
