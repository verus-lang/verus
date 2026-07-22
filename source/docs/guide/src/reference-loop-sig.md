# Loop signatures

> [!TIP]
> See the [guide's chapter on loops](./while.md) for an introduction to verifying loops.

Loops are only permitted in executable code.  Loops may be annotated with a V@[loop_sig]:

```verus-grammar
V@[verus_loop]  ::= loop V@[loop_sig] { V@[exec_stmt]* }
V@[verus_while] ::= while V@[exec_expr] V@[loop_sig] { V@[exec_stmt]* }
V@[verus_for]   ::= for V@[exec_expr] in V@[exec_expr] V@[loop_sig] { V@[exec_stmt]* }

V@[loop_sig] ::=
    ( invariant ( V@[spec_expr] ),+ )?
    ( invariant_except_break ( V@[spec_expr] ),+ )?
    ( ensures ( V@[spec_expr] ),+ )?
    ( decreases ( V@[spec_expr] ),+ )?
```

### Invariant clauses

The `invariant`, `invariant_except_break`, and `ensures` clauses are used to specify
properties before and after iterations. Specifically:

 * `invariant` should hold true at the beginning of each iteration, and on loop exit.
 * `invariant_except_break` should hold true at the beginning of each iteration.
 * `ensures` should hold true at loop exit.

("Loop exit" refers to a control flow step that leads to the program point immediately following the loop definition. It does not include "return" statements or labeled "break" statements that reference other loops besides the one in question.)

Verus _may_ assert or assume these predicates at various points in order to verify
correctness of the loop and its enclosing function.
See [Loop Verification Conditions](./reference-loop-vcs.md) for details.

> [!NOTE]
> Thus, loop signatures should be viewed as hints for verifying the enclosing function
> as a whole, not as formal specifications of the loop in a strict sense.
>
> In particular, the handling of **loop exit** is dependent on the specific configuration
> and structure of the loop. Therefore, Verus may or may not enforce the `ensures` or `invariant`
> predicates at loop exit. There are two scenarios where loop exit conditions are not required
> to hold:
>
>  * When [`loop_isolation=false`](./reference-loop-vcs-loop-isolation-false.md),
>    the `invariant` predicates are not asserted at loop exit,
>    and `ensures` clauses are ignored entirely.
>  * For a [`while loop with no break statements`](./reference-loop-vcs-loop-isolation-true-while.md),
>    the final iteration—the one where the conditional expression evaluates to "false"
>    and the loop body fails to be avaluated—is treated specially.
>    If the conditional expression has side-effects, it can invalidate the invariant
>    before loop exit. See [this example](./reference-loop-vcs-loop-isolation-true-while.md#side-effect-condition-example).

### Decreases clauses

If the `decreases` clause is provided, Verus checks that
the sequence of expressions "decreases" from one iteration
to the next, as specified by the [lexicographic decreases relation](./reference-decreases-to.md).

The `decreases` clause may be omitted if the
[`#[verifier::exec_allows_no_decreases_clause]` attribute](./reference-attributes.md#verifierexec_allows_no_decreases_clause) is provided.

> [!WARNING]
> The use of the `decreases` clause prevents some common infinite-looping scenarios,
> but it is still possible to write non-terminating code in Verus.
> At this time, Verus does not formally verify non-termination.
