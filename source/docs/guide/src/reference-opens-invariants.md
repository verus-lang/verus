# opens_invariants

The `opens_invariants` clause may be applied to any `proof` or `exec` function.

This indicates the set of _names_ of tracked invariants that may be opened by the function.
At this time, it has three forms.  See [the documentation for `open_local_invariant`](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_local_invariant.html#avoiding-reentrancy) for more information about why Verus enforces these restrictions.

```
fn example()
    opens_invariants any
{
    // Any invariant may be opened here
}
```

or:

```
fn example()
    opens_invariants none
{
    // No invariant may be opened here
}
```

or:

```
fn example()
    opens_invariants [ $EXPR1, $EXPR2, ... ]
{
    // Only invariants with names in [ $EXPR1, $EXPR2, ... ] may be opened.
}
```

### Defaults

For `exec` functions, the default is `opens_invariants any`.

For `proof` functions, the default is `opens_invariants none`.
