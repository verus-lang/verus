# Specifications on FnOnce

For any function object, i.e., a value of any type that implements `FnOnce`
(for example, a named function, or a closure) the signature can be reasoned about generically
via the Verus built-in functions `call_requires` and `call_ensures`. 

 * `call_requires(f, args)` is a predicate indicating if `f` is safe to call with the given `args`. For any non-static call, Verus requires the developer to prove that `call_requires(f, args)` is satisfied at the call-site.
 * `call_ensures(f, args, output)` is a predicate indicating if it is possible for `f` to return the given `output` when called with `args`. For any non-static call, Verus will assume that `call_ensures(f, args, output)` holds after the call-site.
 * At this time, the `opens_invariants` aspect of the signature is not treated generically. Verus conservatively treats any non-static call as if it might open any invariant.

The `args` is always given as a tuple (possibly a 0-tuple or 1-tuple).

See [the tutorial chapter](./exec_funs_as_values.md) for examples and more tips.

For any function with a Verus signature (whether a named function or a closure), Verus generates
axioms resembling the following:

```
(user-declared requires clause) ==> call_requires(f, args)
call_ensures(f, args, output) ==> (user-declared ensures clauses)
```

Using implication (`==>`) rather than a strict equivalence (`<==>`) in part to allow
[flexible signatures in traits](./reference-signature-inheritance.md).
However, our axioms use this form for all functions, not just trait functions.
This form reflects the [proper way to write specifications for higher-order functions](./exec_funs_as_values.md#an-important-note).
