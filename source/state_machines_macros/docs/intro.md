# Overview

The `state_machines_macros` library provides two macros, `state_machine!` and `concurrent_state_machine!`. This overview will discuss the first.

The `state_machine!` framework provides a way to establish a basic state machine, consisting of four components:

 1. The state definition
 2. The transitions (including initialization procedures)
 3. Invariants on the state
 4. Proofs that the invariants hold

Here's a very simple example:

```rust
state_machine!(
    AdderMachine {
        //// The state definition
        
        fields {
            pub number: int,
        }
        
        //// The transitions

        #[init]
        fn initialize() {
            update(number, 0); 
        }   

        #[transition]
        fn add(&self, n: int) {
            update(number, self.number + 2*n);
        }
        
        //// Invariants on the state

        #[invariant]
        pub fn is_even(&self) -> bool {
            self.number % 2 == 0
        }
        
        //// Proofs that the invariants hold

        #[inductive(initialize)]
        fn initialize_inductive(post: AdderMachine) { } 

        #[inductive(add)]
        fn add_inductive(self: AdderMachine, post: AdderMachine, n: int) { } 

    }   
);
```

## State

The state definition is given inside a block labelled `fields` (a special keyword recognized by the `state_machine!` macro):

```rust
        fields {
            pub number: int,
        }
```

The fields are like you'd find in a struct: they must be named fields (i.e., there's no "tuple" option for the state). The fields are also implicitly `#[spec]`.

## Transitions

There are three different attributes that signify a transition: `#[init]`, `#[transition]`, and `#[readonly]`. The body of the transition is a transition "DSL" which is interpretted by the macro and turned into an appropriate relation: a 1-state relation for an `init`, and a 2-state relation for a `transition`.

Each transition is a deterministic function of its input arguments, so any intended non-determinism should be done via the arguments. The DSL allows the user to update fields; any field not updated is implied to remain the same. An `#[init]` transition is required to “update” each field, so that the intialization is fully determined.

2-state transitions take, as their first argument, an object `self`, which represents the starting state of the transition. Naturally, this argument is not available for `#[init]` transitions.

In summary, then, the three types of transitions are:

 * `#[init]`: A transition whose output yields the valid initial states of the state machine. Such a transition must “update” every field.
 * `#[transition]`: A "normal" transition, from one state (`self`) to another. It can update any subset of fields; all other fields are implicitly not updated, or equivalently, updated to `self.{field}`. No field can be updated more than once.
 * `#[readonly]`: A no-op transition where no `update` statements are allowed at all. The primary purpose of such a transition is to apply `assert` statements (see below).

The transition DSL has a simple grammar. A `Stmt` is given by the following grammar:

```
Stmt =
   | Stmt; Stmt;
   | update(field, E);
   | require(E);
   | assert(E);
   | if E { Stmt }
   | if E { Stmt } else { Stmt }
   | let id = E;
```

Here, `E` is an arbitrary Verus expression, which might be in terms of `self`, arguments to the transition, or variables declared in `let` statements.

### Updates

In an `update(field, e)` statement, the `field` must be a valid field name as defined in the `fields` block above. In the resulting relation that describes the transition/initialization, this becomes the predicate `post.field == e`.

### Requires

`require(E)` (where `E` is a `bool`) declares an enabling condition on the transition. 

### Asserts

`assert(E)` declares a _safety condition_ on the transition. This creates a proof obilgation for the validity of the state machine: the `assert` must follow from the invariants (see below), and from any enabling conditions (`require` statements) given prior to the `assert`. Because we require this to be proved, other proofs can assume that the predicate holds whenever this transition holds. However, the predicate doesn't count as an enabling condition, i.e., to show the the transition holds, we _don't_ need to show that the assertion holds.

## Invariants

To make it easier to name individual invariants, the invariants are given via the `#[invariant]` attribute:

```rust
#[invariant]
pub fn inv_1(&self) -> bool { ... }

#[invariant]
pub fn inv_2(&self) -> bool { ... }
```

The state machine macro produces a single predicate `invariant` which is the conjunct of all the given invariants.

## Inductive lemmas

The user needs to prove that every transition preserves the invariants. This is done by creating a lemma to contain the proof and annotating it with the `inductive` attribute:

```rust
#[inductive(initialize)]
fn initialize_inductive(post: AdderMachine) { } 

#[inductive(add)]
fn add_inductive(self: AdderMachine, post: AdderMachine, n: int) { } 
```

The macro requires one lemma for each `#[init]` and `#[transition]` routine. (The lemma would be trivial for a `#[readonly]` transition, so for these, it is not required.)

The arguments to a lemma regarding an `#[init]` routine should always be `post: StateName, ...` where the `...` are the custom arguments to the transition.
The arguments to a lemma regarding a `#[transition]` routine should always be `self: StateName, post: StateName, ...`.

Pre- and post-conditions for each lemma are automatically generated, so these should be left off. Specifically, the macro generates the following conditions:

```rust
// For an #[init] routine:
#[inductive(init_name)]
fn initialize_inductive(post: StateName, ...) {
    requires(init(post, ...))
    ensures(post.invariant())
    
    // ... The user's proof goes here
} 

// For a #[transition] routine:
#[inductive(init_name)]
fn initialize_inductive(self: StateName, post: StateName, ...) {
    requires(strong_transition(self, post, ...) && self.invariant())
    ensures(post.invariant())
    
    // ... The user's proof goes here
}
```

Here, `init` and `strong_transition` refer to the relations generated from the DSL. The `strong` indicates that we are assuming the conditions given by an `assert`. (Proof obligations for the `assert` statements are generated separately; currently, there is no place to provide an explicit proof.)
