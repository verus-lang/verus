# Integers: Nonlinear Arithmetic and Bit Manipulation

Some properties about integers are very difficult (or expensive) to reason about fully automatically.
To tackle these properties, Verus offers several dedicated proof strategies.

One such property is **nonlinear arithmetic**,
which involves equations that multiply, divide, or take the remainder of integer variables 
(e.g., `x * (y * z) == (x * y) * z`).  As discussed earlier in this guide, determining the truth of such formulas
is undecideable in general, meaning that general-purpose SMT solvers like Z3 can only make a best-effort attempt
to solve them.  These attempts rely on heuristics that can be unpredictable.  Hence, by default, Verus 
disables Z3's nonlinear arithmetic heuristics.  When you need to prove such properties, Verus offers the two dedicated
proof strategies described below.  First, the `integer_ring` feature can reliably prove a limited subset of nonlinear properties.  For properties
outside that subset, Verus offers a way to invoke Z3's nonlinear heuristics in a way that will hopefully provide
better reliability.

## 1. Proving General Properties with Z3 
To prove a nonlinear formula that cannot be solved using `integer_ring` feature,
you can selectively turn on Z3's nonlinear reasoning heuristics.
As described below, you can do this either inline in the midst of a larger
function, or in a dedicated proof function.

### Inline Proofs with `assert(...) by(nonlinear_arith)`
To prove a nonlinear property in the midst of a larger function,
you can write `assert(...) by(nonlinear_arith)`.  This creates
a separate Z3 query just to prove the asserted property,
and for this query, Z3 runs with its nonlinear heuristics enabled.
The query does not include ambient facts (e.g., knowledge that stems
from the surrounding function's `requires` clause
or from preceding variable assignments) other than each variable's type invariants
(e.g., the fact that a `nat` is non-negative).  To include additional
context in the query, you can specify it in a `requires` clause for the `assert`,
as shown below.
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bound_checking}}
```

### Modular Proofs with `proof fn ... by(nonlinear_arith)`
You can also use `by(nonlinear_arith)` in a proof function's signature. By including `by(nonlinear_arith)`, the query for this function runs with nonlinear arithmetic reasoning enabled.



## 2. Proving Ring-based Properties with Singular

While general nonlinear formulas cannot be solved consistently, certain
sub-classes of nonlinear formulas can be.  For example, nonlinear formulas that
consist of a series of congruence relations (i.e., equalities modulo some
divisor `n`).  As a simple example, we might like to show that `a % n == b % n
==> (a * c) % n == (b * c) % n`.

Verus offers a deterministic proof strategy to discharge such obligations.
As shown below, to use this strategy, you must state the desired property
as a proof function annotated with `by(integer_ring)`.


Verus will then discharge the proof obligation using a dedicated algebra solver
called [Singular](https://www.singular.uni-kl.de/).  As hinted at by the
annotation, this proof technique is only complete (i.e., guaranteed to succeed)
for properties that are true for all
[rings](https://en.wikipedia.org/wiki/Ring_(mathematics)).   Formulas that rely
specifically on properties of the integers may not be solved successfully.

Using this proof technique requires a bit of additional configuration of your Verus installation.

### Setup

1. Install Singular
    - To use Singular's standard library, you need more than just the Singular executable binary. 
      Hence, when possible, we strongly recommend using your system's package manager.  Here are 
      some suggested steps for different platforms.
        - Mac: `brew install Singular` and set the `VERUS_SINGULAR_PATH` environment variable when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/local/bin/Singular`). For more options, see Singular's [OS X installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-os-x.html). 

        - Debian-based Linux: `apt-get install singular` and set the `VERUS_SINGULAR_PATH` environment variable when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/bin/Singular`). For more options, see Singular's [Linux installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-linuxunix.html).

        - Windows: See Singular's [Windows installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-windows.html).

2. Compiling Verus with Singular Support
    - The `integer_ring` functionality is conditionally compiled when the `singular` feature is set.
      To add this feature, add the `--features singular` flag when you invoke `vargo build` to compile Verus.




### Details/Limitations
- This can be used only with **int** parameters.
- Formulas that involve inequalities are not supported.   
- Division is not supported.
- Function calls in the formulas are treated as uninterpreted functions.  If a function definition is important for the proof, you should unfold the definition of the function in the proof function's `requires` clause.
- When using an `integer_ring` lemma, the divisor of a modulus operator (`%`) must not be zero. If a divisor can be zero in the ensures clause of the `integer_ring` lemma, the facts in the ensures clause will not be available in the callsite.

To understand what `integer_ring` can or cannot do, it is important to understand how it
handles the modulus operator, `%`. Since `integer_ring` does not understand inequalities,
it cannot perform reasoning that requires that `0 <= (a % b) < b`.
As a result, Singular's results might be confusing if you think of `%` primarily
as the programming language operator.

For example, suppose you use `a % b == x` as a precondition.
Encoded in Singular, this will become `a % b == x % b`, or in more traditional "mathematical"
language, `a ≡ x (mod b)`. This does _not_ imply that `x` is in the range `[0, b)`,
it only implies that `a` and `x` are in the same equivalence class mod b.
In other words, `a % b == x` implies `a ≡ x (mod b)`, but not vice versa.

For the same reason, you cannot ask the `integer_ring` solver to prove a postcondition
of the form `a % b == x`, unless `x` is 0. The `integer_ring` solver can prove
that `a ≡ x (mod b)`, equivalently `(a - x) % b == 0`, but this does _not_ imply
that `a % b == x`.

Let's look at a specific example to understand the limitation.

```rust
proof fn foo(a: int, b: int, c: int, d: int, x: int, y: int) by(integer_ring)
    requires
        a % b == x,
        c % d == y
    ensures
        x == y,
{
}
```

This theorem statement appears to be trivial, and indeed, Verus would solve it easily
using its default proof strategy. 
However, `integer_ring` will not solve it. On failure, Verus prints information about
the Singular query, which we can inspect to understand why (this is cleaned up a bit):

```
ring ring_R=integer, (a, b, c, d, x, y, tmp_0, tmp_1, tmp_2), dp;
    ideal ideal_I =
      (a - (b * tmp_0)) - x,
      (c - (d * tmp_1)) - y;
    ideal ideal_G = groebner(ideal_I);
    reduce(x - y, ideal_G);
    quit;
```

We can see here that `a % b` is translated to `a - b * tmp_0`,
while `c % d` is translated to `c - d * tmp_1`.
Again, since there is no constraint that `a - b * tmp_0` or `c - d * tmp_1`
is bounded, it is not possible to conclude 
that `a - b * tmp_0 == c - d * tmp_1` after this simplification has taken place.

## 3. Combining `integer_ring` and `nonlinear_arith`.

As explained above, the `integer_ring` feature has several limitations, it is not possible to get an arbitary nonlinear property only with the `integer_ring` feature. Instead, it is a common pattern to have a `by(nonlinear_arith)` function as a main lemma for the desired property, and use `integer_ring` lemma as a helper lemma.

To work around the lack of support for inequalities and division, you can often write a helper proof discharged with `integer_ring` and use it to prove properties that are not directly supported by `integer_ring`. Furthermore, you can also add additional variables to the formulas. For example, to work around division, one can introduce `c` where `b = a * c`, instead of `b/a`.

#### Example 1: `integer_ring` as a helper lemma to provide facts on modular arithmetic
In the `lemma_mod_difference_equal` function below, we have four inequalities inside the requires clauses, which cannot be encoded into `integer_ring`. In the ensures clause, we want to prove `y % d - x % d == y - x`. The helper lemma `lemma_mod_difference_equal_helper` simply provides that `y % d - x % d` is equal to `(y - x)` modulo `d`. The rest of the proof is done by `by(nonlinear_arith)`.

```rust
pub proof fn lemma_mod_difference_equal_helper(x: int, y:int, d:int, small_x:int, small_y:int, tmp1:int, tmp2:int) by(integer_ring)
    requires
        small_x == x % d,
        small_y == y % d,
        tmp1 == (small_y - small_x) % d,
        tmp2 == (y - x) % d,
    ensures
        (tmp1 - tmp2) % d == 0
{}
pub proof fn lemma_mod_difference_equal(x: int, y: int, d: int) by(nonlinear_arith)
    requires
        d > 0,
        x <= y,
        x % d <= y % d,
        y - x < d
    ensures
        y % d - x % d == y - x
{
    let small_x = x % d;
    let small_y = y % d;
    let tmp1 = (small_y - small_x) % d;
    let tmp2 = (y - x) % d;
    lemma_mod_difference_equal_helper(x,y,d, small_x, small_y, tmp1, tmp2);
}
```

In the `lemma_mod_between` function below, we want to prove that `x % d <= z % d < y % d`. However, `integer_ring` only supports equalities, so we cannot prove `lemma_mod_between` directly. Instead, we provide facts that can help assist the proof. The helper lemma provides 1) `x % d - y % d == x - y  (mod d)` and 2) ` y % d - z % d == y - z  (mod d)`. The rest of the proof is done via `by(nonlinear_arith)`.

```rust
pub proof fn lemma_mod_between_helper(x: int, y: int, d: int, small_x:int, small_y:int, tmp1:int) by(integer_ring)
    requires
        small_x == x % d,
        small_y == y % d,
        tmp1 == (small_x - small_y) % d,
    ensures
        (tmp1 - (x-y)) % d == 0
{}

// note that below two facts are from the helper function, and the rest are done by `by(nonlinear_arith)`.
// x % d - y % d == x - y  (mod d)
// y % d - z % d == y - z  (mod d)
pub proof fn lemma_mod_between(d: int, x: int, y: int, z: int) by(nonlinear_arith)
    requires
        d > 0,
        x % d < y % d,
        y - x <= d,
        x <= z < y
    ensures
        x % d <= z % d < y % d
{
    let small_x = x % d;
    let small_y = y % d;
    let small_z = z % d;
    let tmp1 = (small_x - small_z) % d;
    lemma_mod_between_helper(x,z,d, small_x, small_z, tmp1);

    let tmp2 = (small_z - small_y) % d;
    lemma_mod_between_helper(z,y,d, small_z, small_y, tmp2);    
}
```


#### Example 2: Proving properties on bounded integers with the help of `integer_ring`

Since `integer_ring` proofs only support `int`, you need to include explicit bounds when you want to prove properties about bounded integers. For example, as shown below, in order to use the proof `lemma_mod_after_mul` on `u32`s, `lemma_mod_after_mul_u32` must ensure that all arguments are within the proper bounds before passing them to `lemma_mod_after_mul`.  

If a necessary bound (e.g., `m > 0`) is not included, Verus will fail to verify the proof.

```rust
proof fn lemma_mod_after_mul(x: int, y: int, z: int, m: int) by (integer_ring)
    requires (x-y) % m == 0
    ensures (x*z - y*z) % m == 0
{}

proof fn lemma_mod_after_mul_u32(x: u32, y: u32 , z: u32, m: u32)   
    requires
        m > 0,
        (x-y) % (m as int) == 0,
        x >= y,
        x <= 0xffff,
        y <= 0xffff,
        z <= 0xffff,
        m <= 0xffff,
    ensures (x*z - y*z) % (m as int) == 0
{ 
  lemma_mod_after_mul(x as int, y as int, z as int, m as int);
  // rest of proof body omitted for space
}
```

The desired property for `nat` can be proved similarly.

The next example is similar, but note that we introduce several additional variables(`ab`, `bc`, and `abc`) to help with the integer_ring proof.

```rust
pub proof fn multiple_offsed_mod_gt_0_helper(a: int, b: int, c: int, ac: int, bc: int, abc: int) by (integer_ring)
    requires
        ac == a % c,
        bc == b % c,
        abc == (a - b) % c,
    ensures (ac - bc - abc) % c == 0
{}

pub proof fn multiple_offsed_mod_gt_0(a: nat, b: nat, c: nat) by (nonlinear_arith) 
    requires
        a > b,
        c > 0,
        b % c == 0,
        a % c > 0,
    ensures (a - b) % (c as int) > 0
{
    multiple_offsed_mod_gt_0_helper(
      a as int, 
      b as int, 
      c as int, 
      (a % c) as int, 
      (b % c) as int, 
      ((a - b) % (c as int)) as int
    );
}
```

More `integer_ring` examples can be found in [this folder](https://github.com/verus-lang/verus/tree/main/source/rust_verify/example/integer_ring), and this [testcase file](https://github.com/verus-lang/verus/blob/main/source/rust_verify_test/tests/integer_ring.rs).

### Examining the encoding
Singular queries will be logged to the directory specified with `--log-dir` (which defaults to `.verus-log`) in a separate file with a `.singular` suffix. You can directly run Singular on this file. For example, `Singular .verus-log/root.singular --q`. 
The output is `0` when Singular successsfully verifies the query.
