# assert ... by(bit_vector)

Invoke Verus's bitvector solver to prove the given predicate.
This is particularly useful for bitwise operators
and integer arithmetic on finite-width integers.
Internally, the solver uses a technique called _bit-blasting_, which represents each numeric variable
by its binary representation as a bit vector, and every operation as a boolean circuit.


```
assert(P) by(bit_vector);
```

```
assert(P) by(bit_vector)
  requires Q;
```

The prover does not have access to any prior context except that which is given in
the `requires` clause, if provided. If the `requires` clause is provided, then the
bit vector solver attempts to prove `Q ==> P`. Verus will also check (using its normal solver)
that `Q` holds from the prior proof context.

The expressions `P` and `Q` may only contain expressions that the bit solver understands.
This includes:

 * Variables of type `bool` or finite-width integer types (`u64`, `i64`, `usize`, etc.)
   * All free variables are treated symbolically. Even if a variable is defined via a `let`
     statement declared outside the bitvector assertion, this definition is not visible
     to the solver.
 * Integer and boolean literals
 * Non-truncating arithmetic (`+`, `-`, `*`, `/`, and `%`)
 * Truncating arithmetic (`add`, `sub`, `mul` functions)
 * Bit operations (`&`, `|`, `^`, `!`, `<<`, `>>`)
 * Equality and inequality (`==`, `!=`, `<`, `>`, `<=`, `>=`)
 * Boolean operators (`&&`, `||`, `^`) and conditional expressions
 * The `usize::BITS` constant

## Internal operation

Verus's bitvector solver encodes the expression by representing all integers using an SMT "bitvector" type.
Most of the above constraints arise 
because of the fact that Verus has to choose a fixed bitwidth for any given expression.

Note that, although the bitvector solver cannot handle free variables of type
`int` or `nat`, it _can_ handle other kinds of expressions that are typed `int` or `nat`.
For example, if `x` and `y` have type `u64`, then `x + y` has type `int`,
but the Verus bitvector solver knows that `x + y` is representable with 65 bits.

### Handling `usize` and `isize`

If the expression uses any symbolic values whose width is architecture-dependent,
and the architecture bitwidth has not been specified via a [`global` directive](./reference-global.md),
Verus will generate multiple queries, one for each possible bitwidth (32 bits or 64 bits).
