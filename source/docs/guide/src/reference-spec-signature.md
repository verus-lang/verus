# Spec fn signature

The general form of a `spec` function signature takes the form:

```verus-grammar
V@[spec_fn_item] ::=
    R@[visibility]? uninterp? V@[openness]? spec fn R@[function_name] R@[generics]?(R@[args...]) -> R@[type]
        R@[where_clause]?
        V@[recommends_clause]?
        V@[spec_decreases_clause]?

V@[openness] ::= closed
           | open
           | open ( R@[visibility] )
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

## The openness clause

Openness defines the visibility of the body, which may be more restricted than the visibility
of the function name. Specifically:

 * `open` means the body is visible everywhere, to all crates.
 * <code>open(R@[visibility])</code> means the body is visible to the given visibility specifier.
   * e.g., `open(crate)`, `open(self)`, `open(super)`, `open(in some::module::path)`
 * `closed` means the body is visible only within the module where the function is defined; i.e., it is equivalent to `open(self)`.

The openness specifier is required whenever the body is given.

## The `uninterp` specifier

The `uninterp` specifier declares the function as _uninterpreted_, meaning the body of the 
spec function is not given.

> [!NOTE]
> Uninterpreted functions are usually not useful unless they are used
> in combination with axioms that define the properties of the function. A common use case
> for an uninterpreted function is to define the spec interpretation of a type from a
> trusted (i.e., unverified) library.
>
> However, it is always sound to declare an `uninterp` function with no additional axioms.
