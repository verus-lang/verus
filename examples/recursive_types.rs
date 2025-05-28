use vstd::prelude::*;

// TODO: add some of these explanations to the guide

verus! {

// If treated naively, recursive types can lead to nonterminating proofs:
/*
struct R { f: spec_fn(R) -> int }
proof fn bad()
    ensures false
{
    let f1 = |r: R| -> int {
        (r.f)(r) + 1
    };
    let r = R { f: f1 };
    // from r == R { f: f1 }:
    assert( r.f     == f1   );
    assert((r.f)(r) == f1(r));
    // from the definition of f1:
    assert(f1(r) == (r.f)(r) + 1);
    // taken together:
    assert(f1(r) == f1(r) + 1);
}
*/// To prevent this, Verus prohibits recursion in "negative positions" in a recursive type.
// Roughly, a negative position is anything on the left-hand side of a function type ->.
// For example, the "R" in spec_fn(R) -> int is in a negative position.
// Therefore, Verus rejects the definition "struct R { f: spec_fn(R) -> int }" with an error.
// If generics are treated naively, they could encode recursion in negative positions.
// For example, we could try to wrap the function type in a new type to hide the negative
// use of R:
/*
struct FnWrapper<A, B> { f: spec_fn(A) -> B } // error: A not allowed in negative position
struct R { f: FnWrapper<R, int> }
*/// To prevent this, Verus requires that type parameters used in negative positions (like A)
// be annotated with #[verifier::reject_recursive_types]:
/*
#[verifier::reject_recursive_types(A)]
struct FnWrapper<A, B> { f: spec_fn(A) -> B } // ok
struct R { f: FnWrapper<R, int> } // error: R not allowed in negative position
*/// Based on this annotation on A, Verus knows that the recursive R in FnWrapper<R, int> should
// be rejected, and it reports an error in the definition of R.
// Recursive types can be used in decreases clauses of recursive specifications and recursive proofs:
enum List<A> {
    Nil,
    Cons(A, Box<List<A>>),
}

spec fn len<A>(list: &List<A>) -> nat
    decreases list  // decreases can be used on values of type List<A> ,
{
    match list {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(tl),
    }
}

// To support this, Verus requires that struct and enum datatypes have a well-defined height (rank).
// For this, Verus requires that struct and enum datatypes have a non-recursive
// "ground" variant that can be used as a base case for defining the height.
// For example, the Nil variant in List can be used to construct List values of height 0,
// and then the Cons variant can be repeatedly applied to construct bigger and bigger values
// with height > 0.
// Attempting to declare a datatype with no ground variant will cause an error:
/*
enum UngroundedList<A> {
    // error: no ground variant; the only variant is Cons, which recursively uses UngroundedList
    Cons(A, Box<UngroundedList<A>>),
}
*/

// If generics are treated naively, they could encode datatypes with no ground variant:
/*
struct DataWrapper<A> { a: A }
enum UngroundedList<A> {
    // error: no ground variant; the only variant is Cons, which still recursively uses UngroundedList
    Cons(A, Box<DataWrapper<UngroundedList<A>>>),
}
*/

// To prevent this, Verus rejects a recursive type definition's ground variant
// from instantiating a type parameter A with the recursive type (UngroundedList)
// unless the type parameter A is marked #[verifier::accept_recursive_types].
// However, if DataWrapper marks A accept_recursive_types,
// then DataWrapper must have a ground variant that is not built from A.
// Because of this, Verus rejects the following:
/*
#[verifier::accept_recursive_types(A)]
struct DataWrapper<A> { a: A } // error: no ground variant without A
*/

// However, by adding a ground variant, we can provide a correct wrapper,
// making both DataOption and GroundedList properly grounded:
#[verifier::accept_recursive_types(A)]
enum DataOption<A> {
    None,
    Some(A),
}
  // ok
enum GroundedList<A> {
    Cons(A, Box<DataOption<GroundedList<A>>>),  // ok
}

// Overall, Verus parameters have one of three levels of acceptance of recursive types:
// - #[verifier::reject_recursive_types]
// - #[verifier::reject_recursive_types_in_ground_variants]
// - #[verifier::accept_recursive_types]
// reject_recursive_types is added to types that use the type parameter negatively,
// and accept_recursive_types may (optionally) be added to types that have a ground variant
// that doesn't use the type parameter.
// Typical example of reject_recursive_types:
#[verifier::reject_recursive_types(A)]
struct Set<A> {
    f: spec_fn(A) -> bool,
}

// Typical example of reject_recursive_types_in_ground_variants (which is the default):
struct Pair<A, B> {
    first: A,
    second: B,
}

// Typical example of accept_recursive_types:
#[verifier::accept_recursive_types(A)]
enum Option<A> {
    None,
    Some(A),
}

fn main() {
}

} // verus!
