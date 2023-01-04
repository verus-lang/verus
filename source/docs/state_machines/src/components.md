# Components of a State Machine

The `state_machines_macros` library provides two macros, `state_machine!` and `tokenized_state_machine!`. This overview will discuss the first.

The `state_machine!` framework provides a way to establish a basic state machine, consisting of four components:

 1. The state definition
 2. The transitions (including initialization procedures)
 3. Invariants on the state
 4. Proofs that the invariants hold

Here's a very simple example:

```rust,ignore
state_machine!{
    AdderMachine {
        //// The state definition
        
        fields {
            pub number: int,
        }
        
        //// The transitions

        init!{
            initialize() {
                init number = 0;
            }
        }   

        transition!{
            add(n: int) {
                update number = pre.number + 2*n;
            }
        }
        
        //// Invariants on the state

        #[invariant]
        pub fn is_even() -> bool {
            pre.number % 2 == 0
        }
        
        //// Proofs that the invariants hold

        #[inductive(initialize)]
        fn initialize_inductive(post: AdderMachine) {
            // Verus proves that 0 % 2 == 0
        }

        #[inductive(add)]
        fn add_inductive(pre: AdderMachine, post: AdderMachine, n: int) {
            // Verus proves that if `pre.number % 2 == 0` then
            // `post.number` is `pre.number + 2*n` is divisble by 2 as well.
        }
    }
}
```

## State

The state definition is given inside a block labelled `fields` (a special keyword recognized by the `state_machine!` macro):

```rust,ignore
        fields {
            pub number: int,
        }
```

The fields are like you'd find in a struct: they must be named fields (i.e., there's no "tuple" option for the state). The fields are also implicitly `#[spec]`.

## Transitions

There are four different types of "operations": `init!`, `transition!`, `readonly!`, and `property!`. The body of the operation is a "transition DSL" which is interpretted by the macro:

 * A `init!` becomes a 1-state relation representing valid initial states of the system
 * A `transition!` becomes a 2-state relation representing a transition from one state (`pre`) to the next (`post`)
 * A `readonly!` becomes a 2-state relation where the state cannot be modified.
 * A `property!` allows the user to add safety conditions on a single state (`pre`).

When exported as relations:

 * 1-state `init!` operations take 1 argument, `pre`.
 * 2-state operations (`transition!` and `readonly!`) take 2 arguments, `pre` and `post`.
 * `property!` operations are not exported as relations.

Each operation (transition or otherwise) is deterministic in its input arguments, so any intended non-determinism should be done via the arguments.
The DSL allows the user to update fields; any field not updated is implied to remain the same.
An `init!` transition is required to initialize each field, so that the intialization is fully determined.
The DSL provides four fundamental operations (`init`, `update`, `require`, `assert`)
as detailed in the [transition language reference](./transition-language.md).
They are allowed according to the following table:

|           | `init!` | `transition!` | `readonly!` | `property!` |
|-----------|---------|---------------|-------------|-------------|
| `init`    | yes     |               |             |             |
| `update`  |         | yes           |             |             |
| `require` | yes     | yes           | yes         | yes         |
| `assert`  |         | yes           | yes         | yes         |

The distinction between `readonly!` and `property!` is somewhat pedantic: after all,
both are expressed as predicates on states which are not modified, and both
allow `require` and `assert` statements.
The difference is that
a `readonly!` operation is exported as an actual transition between `pre` and `post`
(with `pre === post`) whereas a `property!` is not exported as a transition.

## Invariants

To make it easier to name individual invariants, the invariants are given via the `#[invariant]` attribute:

```rust,ignore
#[invariant]
pub fn inv_1(&self) -> bool { ... }

#[invariant]
pub fn inv_2(&self) -> bool { ... }
```

The state machine macro produces a single predicate `invariant` which is the conjunct of all the given invariants.

## Inductive lemmas

The user needs to prove that every transition preserves the invariants. This is done by creating a lemma to contain the proof and annotating it with the `inductive` attribute:

```rust,ignore
        #[inductive(initialize)]
        fn initialize_inductive(post: AdderMachine) { } 

        #[inductive(add)]
        fn add_inductive(pre: AdderMachine, post: AdderMachine, n: int) { } 
```

The macro requires one lemma for each `init!` and `transition!` routine. (The lemma would be trivial for a `readonly!` transition, so for these, it is not required.)

The arguments to a lemma regarding an `init!` routine should always be `post: StateName, ...` where the `...` are the custom arguments to the transition.
The arguments to a lemma regarding a `transition!` routine should always be `pre: StateName, post: StateName, ...`.

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
        #[inductive(init_name)]
        fn initialize_inductive(pre: StateName, post: StateName, ...) {
            requires(strong_transition(pre, post, ...) && pre.invariant());
            ensures(post.invariant());
            
            // ... The user's proof is placed here
        }
```

Here, `init` and `strong_transition` refer to the relations generated from the DSL. The `strong` indicates that we are assuming the conditions given by an `assert`. (Proof obligations for the `assert` statements are generated separately; currently, there is no place to provide an explicit proof.)

