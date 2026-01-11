# Quantifier Profiling

Sometimes the verification of a Verus function will time out, meaning that the solver couldn't 
determine whether all of the proof obligations have been satisfied.  Or verification might 
succeed but take longer than we would like.  One common cause for both of these phenomena
is [quantifiers](quants.md).  If quantifiers (and their associated triggers) are
written too liberally (i.e., they trigger too often), then the SMT solver may generate too many
facts to sort through efficiently.  To determine if this is the case for your Verus code, you
can use the built-in quantifier profiler.

As a concrete example, suppose we have the following three functions defined:

```rust
{{#include ../../../../examples/trigger_loops.rs:def_f_g}}
```

and we use them in the following proof code:

```rust
{{#include ../../../../examples/trigger_loops.rs:trigger_forever2}}
```

Notice that we have three quantifiers in the `requires` clause; the first will
trigger on `g(x)`, which will be useful for proving the assertion about `g(4)`.
The second quantifier triggers on both `f(x, y)` and `h(x, y)` and says that
they're equal.  The last quantifier is manually triggered on `f(x, y)`, but it
then introduces two more expressions that have a similar shape, namely `f(x +
1, 2 * y)` and `f(2 * x, y + x)`.  Each of these has new arguments to `f`, so
this will cause quantifier 3 to trigger again, creating an infinite cycle of
instantations.  Notice that each such instantiation will also cause quantifier
2 to trigger as well.

If we run Verus on this example, it will quickly time out.  When this happens, you
can run Verus with the `--profile` option to launch the profiler.  We strongly
recommend combining that option with `--rlimit 1`, so that you don't generate too
much profiling data (the more you generate, the longer the analysis takes).  With
`--profile`, if verification times out, the profiler automatically launches.
If you want to profile a function that is verifying successfully but slowly, you 
can use the `--profile-all` option.  You may want to combine this with the 
`--verify-function` option to target the function you're interested in.

If we run the profiler on the example above, we'll see something along the lines of:

```
error: function body check: Resource limit (rlimit) exceeded
  --> ../examples/trigger_loops.rs:66:7
   |
66 | proof fn trigger_forever2()
   |       ^^^^^^^^^^^^^^^^^^^^^

note: Analyzing prover log for (profile rerun) trigger_loops::trigger_forever2 ...

Z3 4.12.5
note: Log analysis complete for (profile rerun) trigger_loops::trigger_forever2

note: Profile statistics for trigger_loops::trigger_forever2

note: Observed 17,963 total instantiations of user-level quantifiers

note: Cost * Instantiations: 2269911826 (Instantiated 8,981 times - 49% of the total, cost 252746) top 1 of 3 user-level quantifiers.
  --> ../examples/trigger_loops.rs:70:93
   |
70 | ...   forall|x: nat, y: nat| f(x + 1, 2 * y) && f(2 * x, y + x) || f(y, x) ==> #[trigger] f(x, y),
   |       ------------------------------------------------------------------------------------^^^^^^^
   |       |
   |       Triggers selected for this quantifier

note: Cost * Instantiations: 397732566 (Instantiated 8,981 times - 49% of the total, cost 44286) top 2 of 3 user-level quantifiers.
  --> ../examples/trigger_loops.rs:69:32
   |
69 |         forall|x: nat, y: nat| h(x, y) == f(x, y),
   |         -----------------------^^^^^^^----^^^^^^^
   |         |
   |         Triggers selected for this quantifier

note: Cost * Instantiations: 3 (Instantiated 1 times - 0% of the total, cost 3) top 3 of 3 user-level quantifiers.
  --> ../examples/trigger_loops.rs:68:24
   |
68 |         forall|x: nat| g(x),
   |         ---------------^^^^
   |         |
   |         Triggers selected for this quantifier

verification results:: 0 verified, 1 errors
error: aborting due to 1 previous error
```

The profiler measures two aspects of quantifier performance.  First, it collects a basic count of how
many times each quantifier is instantiated.  Second, it attempts to calculate a "cost" for each 
quantifier.  The cost of a quantifier is the sum of cost of its instantiations.  The cost of an instantiation `i`
is roughly `1 + sum_{(i, n) \in edges} cost(n) / in-degree(n)` where each `n` is an instantiation caused 
by instantiation `i`.  In other words, instantiation `i` produced a term that caused the solver to create
another instantiation (of the same or a different quantifier) `n`.  This heuristic attempts to place more
weight on quantifiers whose instantiations themselves cause other expensive instantiations.  By default,
the profiler will sort by the product of these two metrics.

In the example above, we see that the top quantifier is quantifer 3 in the Verus code, which is indeed the 
troublemaker.  The use of the cost metric elevates it above quantifier 2, which had the same number of 
instantiations but is really an "innocent bystander" in this scenario.  And both of these quantifiers
are instantiated vastly more than quantifier 3, indicating that quantifier 3 is not the source of the 
problem.  If all of the quantifiers have a small number of instantiations, that may be a sign that 
quantifier instantiation is not the underlying source of the solver's poor performance.

