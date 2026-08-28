# The `bit_vector` prover mode

> [!TIP]
> See the [guide page](./bitvec.md) for practical tips on using the `bit_vector` solver.

### Methods of invocation

**By assertion.**
The `bit_vector` solver can be invoked via an [`assert-by` statement](./reference-assert-by-prover.md):

```
assert(Q) by(bit_vector);
```

Proves `Q` via the the `bit_vector` solver.

```
assert(Q) by(bit_vector) requires P;
```

Proves `P ==> Q` via the the `bit_vector` solver.

**As a proof function.**
The `bit_vector` solver can be invoked with a `by(bit_vector)` on a [proof function](./reference-proof-signature.md).

```
proof fn example(...) by(bit_vector)
    requires P
    ensures Q
{ }
```

This proves `P ==> Q` via the `bit_vector` solver.

### Supported predicates

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

## Solver operation

Verus's bitvector solver encodes the expression by representing all integers using an SMT "bitvector" type.
Most of the above constraints arise 
because of the fact that Verus has to choose a fixed bitwidth for any given expression.

Note that, although the bitvector solver cannot handle free variables of type
`int` or `nat`, it _can_ handle some expressions that are typed `int` or `nat` provided
Verus can bound the the bitwidth needed to represent the number.
For example, if `x` and `y` have type `u64`, then `x + y` has type `int`,
but the Verus knows that `x + y` is representable with 65 bits.

### Handling `usize` and `isize`

If the expression uses any symbolic values whose width is architecture-dependent,
and the architecture bitwidth has not been specified via a [`global` directive](./reference-global.md),
Verus will generate multiple queries, one for each possible bitwidth (32 bits or 64 bits).
