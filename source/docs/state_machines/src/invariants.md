# Invariants

An _invariant_ on a transition system is a boolean predicate that must hold on any
reachable state of the system---i.e., a state reachable by starting at any `init`
and then executing a sequence of transitions.

Verus allows the user to specify an _inductive invariant_, that is, a predicate that
must satisfy the inductive criteria:

 * `init(state) ==> inv(state)`
 * `transition(pre, post) && inv(pre) ==> inv(post)`

By induction, any predicate satisfying the above criteria is necessarily a valid invariant
that holds for any reachable state.

There are many reasons the user might need to specify (and prove correct) such an invariant:

 * The invariant is needed to prove the _safety conditions_ of the state machine,
   that is, the [`assert` statements](./transition-language.md#the-assert-statement)
   that appear in any transitions or properties.
 
 * The invariant is needed to prove a [state machine refinement](./refinements-reference.md).

## Specifying the invariants

To make it easier to name individual clauses of the inductive invariant,
they are given as boolean predicates with `#[invariant]` attributes.
The boolean predicates should take a single argument, `&self`.

```rust,ignore
#[invariant]
pub fn inv_1(&self) -> bool { ... }

#[invariant]
pub fn inv_2(&self) -> bool { ... }
```

The state machine macro produces a single predicate `invariant` which is the conjunct of all the given invariants.

## Proving the inductive criteria

To prove that the invariants are correct,
the user needs to prove that every `init!` operation results in a state satisfying
the invariant, and that every `transition!` operation preserves the invariant
from one state to the next.
This is done by creating a lemma to contain the proof and annotating
it with the `inductive` attribute:

```rust,ignore
// For an `init!` routine:
#[inductive(init_name)]
fn initialize_inductive(post: Self) {
    // Proof here
}

// For a `transition!` routine:
#[inductive(transition_name)]
fn transition_inductive(pre: Self, post: Self, n: int) {
    // Proof here
} 
```

Verus requires one lemma for each `init!` and `transition!` routine, provided at least
one invariant predicate is specified.
(The lemma would be trivial for a `readonly!` transition, so for these, it is not required.)

 * For an `init!` operation, the lemma parameters should always be `post: Self, ...` where the `...` are the custom arguments to the transition.
 * For a `transition!` operation, the lemma parameters should always be `pre: Self, post: Self, ...`.

If the lemmas are omitted, then the Verus error will provide the expected type signatures in the console output.

Pre- and post-conditions for each lemma are automatically generated, so these should be left off. Specifically, the macro generates the following conditions:

```rust,ignore
// For an `init!` routine:
#[inductive(init_name)]
fn initialize_inductive(post: StateName, ...) {
    requires(init(post, ...));
    ensures(post.invariant());
    
    // ... The user's proof is placed here
} 

// For a `transition!` routine:
#[inductive(transition_name)]
fn transition_inductive(pre: StateName, post: StateName, ...) {
    requires(strong_transition(pre, post, ...) && pre.invariant());
    ensures(post.invariant());
    
    // ... The user's proof is placed here
}
```

Here, `init` and `strong_transition` refer to the relations generated from the DSL.
These contain all the predicates from the [`require` statements](./transition-language.md#the-require-statement) defined in the transition or initialization routine.

The `strong` indicates that we can assume the conditions given by any [`assert` statements](./transition-language.md#the-assert-statement) in addition to the `require` statements.
(Proof obligations for the `assert` statements are generated separately.)

## Example

(TODO should have an example)
