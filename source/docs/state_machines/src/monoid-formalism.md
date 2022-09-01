Here, we provide justification for the concurrent state machine features in terms of a (pen-and-paper) monoid formalism.

Let the state machine have state `S = { f1: T1, f2: T2, ... }` with an invariant `Inv : S -> bool`.

We define a monoid `M`:

```
enum M {
    Unit,
    State(g1: S1, g2: S2, ...),
    Fail,
}
```

Each `Si` is a partial monoid defined in terms of `Ti` and its respective sharding strategy.

We let `Unit`, of course, be the unit, and we define `x · Fail = Fail` for all `x`. The composition of two `State` elements is defined pairwise, and if any of the compositions fails due to partiality, we go to the `Fail` state.

The sharding strategies are as follows, given in terms of a type `T`:

 * Strategy `variable`: We let `S` be `Option<T>` with `None` as the unit, and the composition `Some(...) · Some(...)` to be undefined.
 * Strategy `constant`: We let `S` be `Option<T>` with `None` as the unit, and the composition `Some(x) · Some(y) = if x == y { Some(x) } else { undefined }`.


For each strategy we have some map `W : S -> T`. (In all cases, the map is either the identity or `Some(_)`.) Now, define a predicate `P : M -> bool`:

```
P(Unit) = false
P(Fail) = false
P(State(g1, g2, ...)) = ∃ f1, f2, ... Inv(S(f1, f2, ...)) && Wi(fi) = gi
```

Now let `V : M -> bool` be given by:

```
V(x) = ∃ z , P(x · z)
```

The predicate `V` makes `M` a partial commutative monoid. From this, we can construct propositions (γ, m) where γ is a location and m : M under the standard rules, e.g., `(γ, m1) * (γ, m2) <==> (γ, m1 · m2)` and so on.

Now, the concurrent state machine framework produces a variety of tokens.

  * The `Instance` token (γ, c1, ..., ck) contains all the data for the fields of `constant` sharding strategy. It represents the proposition `(γ, State(...))` with fields `gi = Some(ci)` and all other fields unital. Note that this proposition is freely duplicable (because `Some(ci) · Some(ci) = Some(ci)`).
  * For (non-constant) field `f`, we create separate tokens for that field. Each token represents the same proposition as the `Instance` (which, again, is freely duplicable) and some proposition specific to the field, described below:
    * For a field `fi` of `variable` strategy, we have a token `(instance, fi)` which represents the proposition `(γ, State(...))` with field `gi = Some(fi)` (and all other fields unital).
