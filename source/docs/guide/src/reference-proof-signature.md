# Proof fn signature

The general form of a `proof` function signature takes the form:

```verus-grammar
V@[proof_fn_item] ::= V@[proof_fn_proved] | V@[proof_fn_axiom]

V@[proof_fn_proved] ::=
    R@[visibility]? broadcast? proof fn R@[function_name] R@[generics]?(R@[args...]) ( -> V@[proof_return_type] )?
        R@[where_clause]?
        V@[requires_clause]?
        V@[ensures_clause]?
        V@[returns_clause]?
        V@[invariants_clause]?
        V@[decreases_clause]?
    { V@[proof_stmt]* }

V@[proof_fn_axiom] ::=
    R@[visibility]? broadcast? axiom fn R@[function_name] R@[generics]?(R@[args...]) ( -> V@[proof_return_type] )?
        R@[where_clause]?
        V@[requires_clause]?
        V@[ensures_clause]?
        V@[returns_clause]?
        V@[invariants_clause]?
        V@[decreases_clause]?
        ;

V@[proof_return_type]       ::= V@[proof_return_type_named] | V@[proof_return_type_anon]
V@[proof_return_type_named] ::= ( tracked? R@[pattern] : R@[type] )
V@[proof_return_type_anon]  ::= R@[type]
```

## Function specification

The elements of the function specification are given by the signature clauses.

**The precondition.**
The V@[requires_clause] is the precondition.

**The postcondition.**
The V@[ensures_clause]
and the
V@[returns_clause]
together form the postcondition.

**The invariants.**
The V@[invariants_clause] specifies which invariants can be opened by the function.
For proof functions, the default is `open_invariants none`.
See [this page](./reference-opens-invariants.md) for more details.

## Function arguments

All arguments and return values need to have `ghost` or `tracked` mode.
Arguments are `ghost` by default, and they can be declared `tracked` with the `tracked` keyword.

See [here](./reference-var-modes.md#cheat-sheet) for more information.
