# Trigger annotations

To every quantifier expression (`forall`, `exists`, `choose`) in the program, including "implicit"
quantifiers such as in `broadcast` lemmas.

There are many implications of triggers on proof automation that Verus developers should be
aware of. See [the relevant chapter of the guide](./quants.md), particulary the section
on [multiple triggers and matching loops](./multitriggers.md).

This page explains the procedure Verus uses to determine these triggers from Verus source code.

## Terminology: trigger groups and trigger expressions

Every quantifier has a number of _quantifier variables_. To control how the solver instantiates
these variables, trigger groups are used.

 * To every quantifier, Verus determines a collection of _trigger groups_.
 * Every _trigger group_ is a collection of _trigger expressions_.

By necessity, any trigger group is only well-formed if every quantifier variable is used
by at least one trigger expression in the group.

Note that:

 * The SMT solver will instantiate any quantifier whenever _any_ trigger group fires.
 * However, a trigger group will only fire if _every_ expression in the group matches.

Therefore:

 * Having more trigger groups makes the quantifier be instantiated _more_ often.
 * A trigger group with more trigger expressions will fire _less_ often.

## Selecting trigger groups

Verus determines the collection of trigger groups as follows:

 * Verus finds all applicable `#[trigger]` and `#[trigger(n)]` annotations in the body
   of the quantifier.
      * In the case of nested quantifiers, every `#[trigger]` or `#[trigger(n)]` annotation
        is applicable to exactly one quantifier expression: the _innermost_ quantifier
        which binds a variable used by the trigger expression.
 * All applicable expressions marked by `#[trigger]` become a trigger group.
 * All applicable expressions marked by `#[trigger(n)]` for the same `n` become a trigger group.
 * Every annotation <code>#![trigger EXPR<sub>1</sub>, ..., EXPR<sub>k</sub>]</code> at
   the root of the quantifier expression becomes a trigger group.
 * If, after all of the above, no trigger groups have been identified, Verus _may_ use
   heuristics to determine the trigger group(s) based on the body of the quantifier expression.
     * If `#![all_triggers]` is provided, Verus uses an "aggressive" strategy, choosing all trigger
      groups that can reasonably be inferred as applicable from the body.
     * If `#![auto]` is provided, Verus uses a "conservative" strategy, choosing a single
      trigger group that is judged as optimal by various heuristics.
     * If neither `#![all_triggers]` nor `#![auto]` are provided, Verus uses the same
       "conservative" strategy as it does for `#![auto]`.
 * If, after all of the above, Verus is unable to find any trigger groups, it produces
   an error.

## Trigger logging

By default, Verus often prints verbose information about selected triggers in cases where
Verus's heuristics are "un-confident" in the selected trigger groups.
You can silence this information on a case-by-case basis using the `#![auto]` attribute.
When `#![auto]` is applied to a quantifier, this tells Verus
that you want the automatically selected triggers
even when Verus is un-confident, in which case this logging will be silenced.

The behavior can be configured through the command line:

<div class="table-wrapper">
<table>
<colgroup>
   <col span="1" style="width: 30%;">
   <col span="1" style="width: 70%;">
</colgroup>
<thead><tr><th>Option</th><th>Behavior</th></tr></thead>
<tbody>
<tr><td><code>--triggers-mode silent</code></td><td>Do not show automatically chosen triggers</td></tr>
<tr><td><code>--triggers-mode selective</code></td><td><strong>Default.</strong> Show automatically chosen triggers only when heuristics are un-confident, and when <code>#![auto]</code> has not been supplied</td></tr>
<tr><td><code>--triggers</code></td><td>Show all automatically chosen triggers for verified modules</td></tr>
<tr><td><code>--triggers-mode verbose</code></td><td>Show all automatically chosen triggers for verified modules and imported definitions from other module</td></tr>
</tbody></table>
</div>

See more triggers logging options in `verus --help`
