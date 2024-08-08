# `reveal`, `reveal_with_fuel`, `hide`

These attributes control whether and how Verus will unfold the definition of a spec function
while solving. For a spec function `f`:

 - `reveal(f)` directs Verus to unfold the definition of `f` when it encounters a use of `f`.
 - `hide(f)` directs Verus to treat `f` as an uninterpreted function without reasoning
   about its definition.

Technically speaking, Verus handles "function unfolding" by
creating axioms of the form `forall |x| f(x) == (definition of f(x))`.
Thus, `reveal(f)` makes this axiom accessible to the solver,
while `hide(f)` makes this axiom inaccessible.

By default, functions are always revealed when they are in scope. This can be changed
by marking the function with the `#[verifier::opaque]` attribute.

The `reveal_with_fuel(f, n)` directive is used for recursive functions.
The integer `n` indicates how many times Verus should unfold a recursive function.
Limiting the fuel to a finite amount is necessary to avoid 
[trigger loops](multitriggers.md#matching-loops-what-they-are-and-to-avoid-them).
The default fuel (absent any `reveal_with_fuel` directive) is 1.
