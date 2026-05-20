# Spec fn signature

The general form of a `spec` function signature takes the form:

```verus-grammar
V@[spec_fn_with_verus_sig] ::=
    R@[visibility]? spec fn R@[function_name] R@[generics]?(R@[args...]) -> R@[type]
        R@[where_clause]?
        V@[recommends_clause]?
        V@[decreases_clause]?
```

## The `recommends` clause

The `recommends` clauses is a "soft precondition", which is sometimes checked for the sake
of diagnostics, but is not a hard requirement for the function to be well-defined.

See [this guide page](./spec_vs_proof.md#recommends) for motivation and overview.

## The `decreases` clause

The `decreases` clause is used to ensure that recursive definitions are well-formed.
Note that if the `decreases` clauses has a `when`-subclause, it will restrict the function definition
to the domain.

See [the reference page for `decreases`](./reference-decreases.md) for more information,
or see [the guide page on recursive functions](./recursion.md) for motivation and overview.
