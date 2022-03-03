# Core state machine semantics

The core state machine language supports `require` and `assert`, which take on their usual meaning (e.g., as in IVy). `update(f, x)` means `post.f := x`.

We implicitly set `post.x := self.x` at the beginning of the transition definition; thus, a field which is never updated is implicitly not changed for the transition.

The variable `self` always refers to the begin state; `post` is updated as we go, and its value at the end of the transition then gives the after-state of the transition.

# Monoidal state machine semantics

Let M be a partial monoid, let `a · b` be composition and let `a ## b` indicate that the monoidal sum of `a · b` is well-defined.

Let `a <= b` mean that there exists c such `a ## c` and `a · c = b`. If `a <= b`, then the value `b - a` can be defined but is not necessarily unique; for now, let's just consider monoids where it is unique for simplicity. (Otherwise, we have to handle the nondeterminism where we use `b - a` below.)

Suppose the state machine has a field `f` of type `M` with the sharding strategy corresponding to `M`'s monoidal structure. We allow 3 new operations into the state machine DSL, `remove`, `have`, and `add`.

Considered as members of the state machine description language, these three new operations have semantics given in terms of the "core semantics":

 * `remove(f, x)` is equivalent to `require(post.f >= x); post.f := post.f - x`
 * `have(f, x)` is equivalent to `require(post.f >= x);`
 * `add(f, x)` is equivalent to `assert(post.f ## x); post.f := post.f · x`

### Meaning of operations in terms of monoid updates

The interesting feature, then, is that a transition given in terms of `remove`, `have`, and `add` (rather than the "atomic" `update`) allows that transition to be interpretted as a token exchange. Specifically, `remove(f, x)` means that a token of value `x` is given as input (left-hand side of the exchange), `add(f, x)` is an output (right-hand side of the exchange). Finally, `have(f, x)`, which does not _consume_ the value `x`, can be taken as a _read-only_ input to the exchange (in the Burrow sense). 

To be a bit more precise, if we have a transition, say,

```
remove(f, x);
have(f, y);
add(f, z);
```

this can be interpretted as the exchange, `x · y --> z · y`. Furthermore, this exchange is valid subject to the transition satisfying inductiveness and its inherent safety conditions.

This fact now allows us to understand why the operational meanings of `remove` and `add` are given as they are.

 * The operational meaning of `remove(f, x)` contains `require(post.f >= x)`. When the user provides the token containing value `x`, that token is the justification for meeting this enabling condition.
 * The dual operation `add(f, z)` on the other hand contains `assert(post.f ## z)`, i.e., a _safety_ condition, not an enabling condition. This needs to be a safety condition, because the exchange produces `z`, which is then given to the user. Therefore, its the responsibility of the protocol correctness to show that conjuring the token `z` is allowed.

### More specific sharding strategies

The above applies to a general monoid; however, the aim of the state machine language is to provide more specific "sharding" or "tokenizing" strategies.

The plan is for these all to roughly follow the remove/have/add paradigm. For example, consider the `map` strategy, which applies to the datatype `map<K, V>`. We give `map<K, V>` a partial-monoidal structure where `a ## b` iff the keys of `a` and `b` are disjoint, and `a · b` is map union. The tokenizing strategy results in "singleton tokens" `(k, v)` each of which represents a singleton map. Thus input and output tokens (usually) take on singleton values and the map operations in the transition definitions reflect this, e.g.,

 * `add_key_value(f, k, v)` means `add(f, map[k := v])`
 * `remove_key(f, k)` means `remove(f, map[k := post.f[k]])` or equivalently `assert k in post.f.domain; post.f := post.f.remove(k)`

Similarly for multiset & option strategies.

### Deposit, withdraw, guarding

A field `f` can be marked as a "storage" field, which means that instead of tokenizing like the other fields, it represents the _stored_ values. (That is, we can define the interpretation function I, as an extension PCM, to simply return the value of this field.)

We can then define `deposit` and `withdraw` similar to `add` and `remove`. However, stored objects are in some sense dual to the ordinary tokenized objects, and therefore the  are flipped:

 * `deposit(f, x)` is operationally equivalent to `assert(post.f ## x); post.f := post.f · x`
 * `withdraw(f, x)` is operationally equivalent to `assert(post.f >= x); post.f := post.f - x`

However, note that _both_ conditions are `assert` statement here. The deposited tokens come externally from the protocol, and the monoidal structure of those tokens might differ from the monoidal structure used on the field `f`. The existence of a token to deposit does not _a priori_ guarantee that the protocol "has room for it". (For example, in the RwLock example, the client needs to provide a particular token in order to perform a lock release, i.e., a deposit.)

Guards are easy:

 * `guard(f, x)` is operationally equivalent to `assert(post.f >= x);`
 
Guards are only allowed in `readonly` transitions. Guards correspond to output tokens which are borrowed, and whose lifetimes are bounded by the input lifetimes.

### Command reference

Here is a list of planned commands and their definitions, organized by “sharding type”:

Basics:

 * `sharding(variable)` field of type `T`
   * `update(f, x)` --> `post.f := x`.

Monoidal:

 * `sharding(monoid)` field of type `T` with an arbitrary (partial) monoid structure
   * `remove(f, x)` --> `require(post.f >= x); post.f := post.f - x`
   * `have(f, x)` --> `require(post.f >= x);`
   * `add(f, x)` --> `assert(post.f ## x); post.f := post.f · x`
 * `sharding(option)` field of type `Option<T>`
   * `Option<T>` is given a monoidal structure where `None` is unit and `Some(x) · Some(y)` is undefined.
   * `remove_some(f, x)` --> `remove(f, Some(x))`
   * `have_some(f, x)` --> `have(f, Some(x))`
   * `add_add(f, x)` --> `add(f, Some(x))`
 * `sharding(multiset)` field of type `Multi<T>`
   * `Option<T>` is given a monoidal structure where (·) is given by multiset addition.
   * `remove_element(f, x)` --> `remove(f, {x})`
   * `have_element(f, x)` --> `have(f, {x})`
   * `add_element(f, x)` --> `add(f, {x})`
     * Note that the safety condition posed by `add_element` is trivial, since (·) is always defined for the multiset monoid.
 * `sharding(map)` field of type `Map<K, V>`
   * `Map<K, V>` is given a monoidal structure where (·) is map union (undefined in the case of overlapping keys)
   * `remove_kv(f, k, v)` --> `remove(f, [k := v])`
   * `have_kv(f, k, v)` --> `have(f, [k := v])`
   * `add_kv(f, k, v)` --> `add(f, [k := v])`

Storage:

 * For field of type `T` with an arbitrary (partial) monoid structure (I'm not currently planning a storage strategy for a generic monoid, but the real strategies below are given in terms of the general definitions.) 
   * `withdraw(f, x)` --> `assert(post.f >= x); post.f := post.f - x`
   * `guard(f, x)` --> `assert(post.f >= x);`
   * `deposit(f, x)` --> `assert(post.f ## x); post.f := post.f · x`
 * `storage(option)` field of type `Option<T>`
   * `Option<T>` is given a monoidal structure where `None` is unit and `Some(x) · Some(y)` is undefined.
   * `withdraw_some(f, x)` --> `withdraw(f, Some(x))`
   * `guard_some(f, x)` --> `guard(f, Some(x))`
   * `deposit_add(f, x)` --> `deposit(f, Some(x))`
 * `storage(multiset)` field of type `Multi<T>`
   * `Option<T>` is given a monoidal structure where (·) is given by multiset addition.
   * `withdraw_element(f, x)` --> `withdraw(f, {x})`
   * `guard_element(f, x)` --> `guard(f, {x})`
   * `deposit_element(f, x)` --> `deposit(f, {x})`
 * `storage(map)` field of type `Map<K, V>`
   * `Map<K, V>` is given a monoidal structure where (·) is map union (undefined in the case of overlapping keys)
   * `withdraw_kv(f, k, v)` --> `withdraw(f, [k := v])`
   * `guard_kv(f, k, v)` --> `guard(f, [k := v])`
   * `deposit_kv(f, k, v)` --> `deposit(f, [k := v])`
