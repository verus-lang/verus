# Exec fn signature

The general form of an `exec` function signature takes the form:

```verus-grammar
V@[exec_fn_with_verus_sig] ::=
    R@[visibility]? exec? fn R@[function_name] R@[generics]?(R@[args...]) ( -> V@[return_type_and_name] )?
        R@[where_clause]?
        V@[requires_clause]?
        V@[ensures_clause]?
        V@[returns_clause]?
        V@[invariants_clause]?
        V@[unwind_clause]?
```

## Function specification

The elements of the function specification are given by the signature clauses.

**The precondition.**
The V@[requires_clause] is the precondition.

**The postcondition.**
The V@[ensures_clause] and the V@[returns_clause] together form the postcondition.

**The invariants.**
The V@[invariants_clause] specifies what invariants can be opened by the function.
For exec functions, the default is `open_invariants any`.
See [this page](./reference-opens-invariants.md) for more details.

**Unwinding.**
The V@[unwind_clause] specifies whether the function might exit "abnormally" by unwinding,
and under what conditions that can happen.
See [this page](./reference-unwind-sig.md) for more details.

## Function arguments

All arguments and return values need to have `exec` mode. To embed ghost/tracked variables into the signature, use the `Tracked` and `Ghost` types.

See [here](./reference-var-modes.md#cheat-sheet) for more information.
