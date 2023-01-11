# Transition Language

All four operations (`init!`, `transition!`, `readonly!` and `property!`) use
the transition language (although `property!` operations are not technically transitions).
The operations can be declared like so:

```rust,ignore
transition!{
    name(params...) {
        TransitionStmt
    }
}
```

The `TransitionStmt` language allows very simple control-flow with if-else and match
statements, and allows let-bindings.

```rust,ignore
TransitionStmt :=
   | TransitionStmt; TransitionStmt;
   | if $expr { TransitionStmt }
   | if $expr { TransitionStmt } else { TransitionStmt }
   | match $expr { ( $pat => { TransitionStmt } )* }
   | let $pat = $expr;
   | SingleStmt
```

There are four fundamental statements: `init`, `update`, `require`, and `assert`.
For convenience, there are also higher-level statements that can be expressed
in those terms.

```rust,ignore
SingleStmt :=
   | init $field_name = $expr;
   | update $field_name = $expr;
   | require $bool_expr;
   | assert $bool_expr (by { ... })? ;

   // Higher-level statements:

   | require let $pat = $expr;
   | assert let $pat = $expr;
   | update $field_name ([sub_idx] | .subfield)* = $expr;
   | remove ... | have ... | add ... | deposit ... | guard ... | withdraw ...
```

Each `$field_name` should be a valid field name as declared in the `fields` block of the state machine definition.

Each `$expr`/`$bool_expr` is an ordinary [Verus (spec-mode) expression](https://verus-lang.github.io/verus/guide/operators.html).
These expressions can reference the params or bound variables.
They can also reference the pre-state of the transition, `pre` (except in `init!` operations).
(Note that it is not possible to access `post` directly,
though this may be added in the future.)

## Core statements

### The `init` statement

The `init` statement is used only in `init!` operations.
Each field of the state must be initialized exactly once in each `init!` operation.
If there is any control-flow-branching, then each field must be initialized
exactly once in each branch.

Example:

```rust,ignore
state_machine!{ InitExample {
    fields {
        pub x: int,
        pub y: int,
    }

    // Okay.
    init!{
        initialize_1(x_init_value: int) {
            init x = x_init_value;
            init y = 0;
        }
    }

    // Not okay (y is not initialized)
    init!{
        initialize_2(x_init_value: int) {
            init x = x_init_value;
        }
    }

    // Not okay (y is not initialized in the second branch)
    init!{
        initialize_3(b: bool) {
            if b {
                init x = 0;
                init y = 1;
            } else {
                init x = 5;
            }
        }
    }
}}
```

### The `update` statement

The `update` statement is the counterpart of `init` for the `transition!` operations:
it sets the value of a field for a `post` state.

However, (unlike `init`), not every field needs to be updated.
Any field for which no `update` statement appears will implicitly maintain its value
from the `pre` state.

Example:

```rust,ignore
state_machine!{ TransitionExample {
    fields {
        pub x: int,
        pub y: int,
    }

    // Okay.
    transition!{
        transition_1(x_new_value: int) {
            update x = x_new_value;
        }
    }

    // Okay.
    transition!{
        transition_2(b: bool) {
            if b {
                update x = 0;
                update y = 1;
            } else {
                update x = 5;
            }
        }
    }

    // Not okay.
    // (The first 'update' is meaningless because it is immediately overwritten.)
    transition!{
        transition_3(b: bool) {
            update x = 0;
            update x = 1;
        }
    }
}}
```

### The `require` statement

The `require` statement adds an _enabling condition_ to the operation.
This is a condition that must hold in order for the operation to be performed.
A `require` can be used in any of the operation types.

### The `assert` statement

The `assert` statement declares a _safety condition_ on the transition. Verus creates a proof obilgation for the validity of the state machine: the `assert` must follow from the state invariants, and from any enabling conditions (`require` statements) given prior to the `assert`.

If the user needs to provide manual proofs, they can do so using an assert-by:

```rust,ignore
assert $bool_expr by {
    /* proof here */
};
```

(TODO need a better example here)

Because we demand that the `assert` statement is proved,
clients of the state machine may assume that the condition holds whenever the transition is enabled (i.e., all its `require` conditions hold).
other proofs can assume that the predicate holds whenever this transition is enabled.
Therefore, the `assert` statement is not itself an enabling condition; that is, clients do not need to show the condition holds in order to show that the operation is enabled.

## High-level statements

### `require let` and `assert let`

You can write,

```rust,ignore
require let $pat = $expr;
```

where `$pat` is a _refutable_ pattern.
This is roughly equivalent to writing the following (which would ordinarily be disallowed
because of the refutable pattern).

```rust,ignore
require ($expr matches $pat);
let $pat = $expr;
```

The `assert let` statement is similar, but for `assert` instead of `require`.

Example:

```rust,ignore
state_machine!{ RequireLetExample {
    fields {
        x_opt: Option<int>,
    }

    transition!{
        add_1() {
            require let Some(x) = pre.x_opt;
            update x_opt = Some(x + 1);
        }
    }

    // Equivalent to:
    transition!{
        add_1_alternative() {
            require pre.x_opt.is_Some();
            let x = pre.x_opt.get_Some_0();
            update x_opt = Some(x + 1);
        }
    }
}}
```

### Update with subscript and fields

_**Note:** This feature is currently in-development._

To update nested data structures, you can use fields (for structs)
or subscripts (for maps or sequences) in `update` statements.
For example,

```rust,ignore
update field.x.y[idx].z[key] = expr;
```

### `remove` / `have` / `add` / `deposit` / `guard` / `withdraw`

These are complex operations used specially for specific sharding strategies
in a `tokenized_state_machine`.
See the [strategy reference](strategy-reference.md) for details.
