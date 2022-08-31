#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{modes::*, seq::*, vec::*};

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
        let u = my_spec_fun(x as int, y as int); // allowed in proof code
        my_proof_fun(u / 2, y as int); // allowed in proof code
    }
}

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
pub(crate) open spec fn my_pub_spec_fun3(x: int, y: int) -> int {
    // function and body visible to crate
    x / 2 + y / 2
}
pub closed spec fn my_pub_spec_fun4(x: int, y: int) -> int {
    // function visible to all, body visible to module
    x / 2 + y / 2
}
pub(crate) closed spec fn my_pub_spec_fun5(x: int, y: int) -> int {
    // function visible to crate, body visible to module
    x / 2 + y / 2
}

/// Recursive functions must have decreases clauses so that Verus can verify that the functions
/// terminate.
fn test_rec(x: u64, y: u64)
    requires
        0 < x < 100,
        y < 100 - x,
    decreases x
{
    if x > 1 {
        test_rec(x - 1, y + 1);
    }
}

/// Multiple decreases clauses are ordered lexicographically, so that later clauses may
/// increase when earlier clauses decrease.
spec fn test_rec2(x: int, y: int) -> int
    decreases x, y
{
    if y > 0 {
        1 + test_rec2(x, y - 1)
    } else if x > 0 {
        2 + test_rec2(x - 1, 100)
    } else {
        3
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
        my_proof_fun(u / 2, b as int); // my_proof_fun(x, y) takes ghost parameters x and y
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
    assert(x ^ x == 0u32) by(bit_vector);
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
    assert(x * z == mul(x, z)) by(nonlinear_arith)
        requires
            x <= 0xffff,
            z <= 0xffff,
    {
        assert(0 <= x * z);
        assert(x * z <= 0xffff * 0xffff);
    }
}

/// The syntax for forall and exists quantifiers is based on closures:
fn test_quantifier() {
    assert(forall|x: int, y: int| 0 <= x < 100 && 0 <= y < 100 ==> my_spec_fun(x, y) >= x);
    assert(my_spec_fun(10, 20) == 30);
    assert(exists|x: int, y: int| my_spec_fun(x, y) == 30);
}

/// "assert forall by" may be used to prove foralls:
fn test_assert_forall_by() {
    assert forall|x: int, y: int| f1(x) + f1(y) == x + y + 2 by {
        reveal(f1);
    }
    assert(f1(1) + f1(2) == 5);
    assert(f1(3) + f1(4) == 9);

    // to prove forall|...| P ==> Q, write assert forall|...| P implies Q by {...}
    assert forall|x: int| x < 10 implies f1(x) < 11 by {
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

/// To manually specify a trigger to use for the SMT solver to match on when instantiating a forall
/// or proving an exists, use #[trigger]:
fn test_single_trigger1() {
    // Use [my_spec_fun(x, y)] as the trigger
    assume(forall|x: int, y: int| f1(x) < 100 && f1(y) < 100 ==> #[trigger] my_spec_fun(x, y) >= x);
}
fn test_single_trigger2() {
    // Use [f1(x), f1(y)] as the trigger
    assume(forall|x: int, y: int|
        #[trigger] f1(x) < 100 && #[trigger] f1(y) < 100 ==> my_spec_fun(x, y) >= x
    );
}

/// To manually specify multiple triggers, use #![trigger]:
fn test_multiple_triggers() {
    // Use both [my_spec_fun(x, y)] and [f1(x), f1(y)] as triggers
    assume(forall|x: int, y: int|
        #![trigger my_spec_fun(x, y)]
        #![trigger f1(x), f1(y)]
        f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x
    );
}

/// Verus can often automatically choose a trigger if no manual trigger is given.
/// Use the command-line option --triggers to print the chosen triggers.
fn test_auto_trigger1() {
    // Verus automatically chose [my_spec_fun(x, y)] as the trigger.
    // (It considers this safer, i.e. likely to match less often, than the trigger [f1(x), f1(y)].)
    assume(forall|x: int, y: int| f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x);
}

/// If Verus prints a note saying that it automatically chose a trigger with low confidence,
/// you can supply manual triggers or use #![auto] to accept the automatically chosen trigger.
fn test_auto_trigger2() {
    // Verus chose [f1(x), f1(y)] as the trigger; go ahead and accept that
    assume(forall|x: int, y: int| #![auto] f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(3, y) >= 3);
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

/// In specs, <=, <, >=, and > may be chained together so that, for example, a <= b < c means
/// a <= b && b < c.  (Note on efficiency: if b is a complex expression,
/// Verus will automatically introduce a temporary variable under the hood so that
/// the expression doesn't duplicate b: {let x_b = b; a <= x_b && x_b < c}.)
proof fn chained_comparisons(i: int, j: int, k: int)
    requires
        0 <= i + 1 <= j + 10 < k + 7,
    ensures
        j < k,
{
}

/// In specs, e@ is an abbreviation for e.view()
/// Many types implement a view() method to get an abstract ghost view of a concrete type.
fn test_views() {
    let mut v: Vec<u8> = Vec::new();
    v.push(10);
    v.push(20);
    proof {
        let s: Seq<u8> = v@; // v@ is equivalent to v.view()
        assert(s[0] == 10);
        assert(s[1] == 20);
    }
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
/// The view x@ of a Ghost or Tracked x is the ghost or tracked value inside the Ghost or Tracked.
fn test_ghost(x: u32, y: u32)
    requires
        x < 100,
        y < 100,
{
    let u: Ghost<int> = ghost(my_spec_fun(x as int, y as int));
    let mut v: Ghost<int> = ghost(u@ + 1);
    assert(v@ == x + y + 1);
    proof {
        v@ = v@ + 1; // proof code may assign to the view of exec variables of type Ghost/Tracked
    }
    let w: Ghost<int> = ghost({
        // proof block that returns a ghost value
        let temp = v@ + 1;
        temp + 1
    });
    assert(w@ == x + y + 4);
}

fn test_consume(t: Tracked<int>)
    requires t@ <= 7
{
    proof {
        let tracked x = (tracked t).get();
        assert(x <= 7);
        consume(tracked x);
    }
}

/// Exec code can extract individual Ghost and Tracked values from Ghost and Tracked tuples
/// with "let Ghost((...))" and "let Tracked((...))".
/// The tuple pattern elements may further match on Trk and Gho from pervasives::modes.
fn test_ghost_tuple_match(t: Tracked<(bool, bool, Gho<int>, Gho<int>)>) -> Tracked<bool> {
    let g: Ghost<(int, int)> = ghost((10, 20));

    let Ghost((g1, g2)) = g; // g1 and g2 both have type Ghost<int>
    assert(g1@ + g2@ == 30);

    let Ghost((g1, g2)): (Ghost<int>, Ghost<int>) = g;
    assert(g1@ + g2@ == 30);

    let Tracked((b1, b2, Gho(g3), Gho(g4))) = t; // b1, b2: Tracked<bool> and g3, g4: Ghost<int>
    b2
}

/// Spec functions are not checked for correctness (although they are checked for termination).
/// However, marking a spec function as "spec(checked)" enables lightweight "recommends checking"
/// inside the spec function.
spec(checked) fn my_spec_fun2(x: int, y: int) -> int
    recommends
        x < 100,
        y < 100,
{
    // Because of spec(checked), Verus checks that my_spec_fun's recommends clauses are satisfied here:
    my_spec_fun(x, y)
}

/// Spec functions may omit their body, in which case they are considered
/// uninterpreted (returning an arbitrary value of the return type depending on the input values).
/// This is safe, since spec functions (unlike proof and exec functions) may always
/// return arbitrary values of any type,
/// where the value may be special "bottom" value for otherwise uninhabited types.
spec fn my_uninterpreted_fun1(i: int, j: int) -> int;

spec fn my_uninterpreted_fun2(i: int, j: int) -> int
    recommends
        0 <= i < 10,
        0 <= j < 10;

/// Trait functions may have specifications
trait T {
    proof fn my_uninterpreted_fun2(&self, i: int, j: int) -> (r: int)
        requires
            0 <= i < 10,
            0 <= j < 10,
        ensures
            i <= r,
            j <= r;
}

} // verus!
