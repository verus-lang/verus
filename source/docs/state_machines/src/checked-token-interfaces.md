# Checked tokens: raw and generic interfaces

`verified_tokenized_state_machine!` accepts the same machine syntax as
`tokenized_state_machine!`, but the operations on the ghost resources it generates are
proved rather than trusted. Two attributes select how clients see those resources:

* `#[verified_raw_tokens]` exposes the machine's resource algebra directly. A client
  owns fragments of the whole product algebra and calls operations whose
  preconditions are stated over fragments.
* `#[verified_generic_tokens]` generates the interface of the trusted
  `tokenized_state_machine!`: one token type per field, `Instance` methods with the
  same signatures and specifications, and implementations of the `vstd::tokens`
  traits. Every method body is a proof that calls the corresponding raw operation.

The two interfaces share the generated model and its proofs. The generic interface is
a layer over the raw one: it adds no assumptions and no external bodies. This chapter
describes the shared model, then each interface, then how they differ.

## The shared model

For a machine with fields `f_1 … f_n`, the macro generates:

* `State`, the record of field values, and `State::invariant`, the conjunction of
  the `#[invariant]` predicates.
* `Fragment`, the product `F = F_1 × … × F_n` of one resource algebra per field.
  `F_i` is determined by the field's sharding strategy. A `variable` field
  contributes an exclusive component. A `map` field contributes a partial map
  composed by disjoint union, a `count` field natural numbers under addition, a
  `persistent_*` field an agreement component, and so on. The macro proves that
  `Fragment::op` is associative and commutative and that `Fragment::unit()` is its
  identity.
* `Protocol`, which implements `vstd::resource::tsm::Machine` with
  `embed : State → Fragment`. `embed(s)` is the fragment that owns all of `s`. A
  machine with storage fields also implements
  `vstd::resource::tsm_storage::StorageMachine`, where `storage(s)` is the map of
  currently deposited values.

A fragment `a` is valid when it can be completed to the whole of some state that
satisfies the invariant:

```text
completes(a)  :=  ∃ c, s.  invariant(s) ∧ a · c = embed(s)
```

Ownership of `a` at a location `γ` is a `vstd::resource::tsm::Token<Protocol>`. It
wraps a `vstd` `Resource` whose carrier is `a` and whose validity is `completes`. For
storage machines it is `StorageToken<Protocol>`, which wraps a `vstd` storage-protocol
resource. Validity of a composition then means that the owned fragments, together
with some frame, are the image of one invariant-satisfying state. This is the usual
authoritative-style argument, with `embed` playing the role of the authority.

Each transition `t(x)` becomes a frame-preserving update. If the operation consumes
`a` and produces `a'`, the macro proves:

```text
∀ c, s.  invariant(s) ∧ a · c = embed(s)
    ⇒ ∃ s'.  invariant(s') ∧ a' · c = embed(s')
```

`vstd::resource::tsm::frame_update` is this statement. For storage, the conclusion
additionally fixes the storage update:

```text
storage(s') = (storage(s) ∪ deposit) \ dom(withdraw)
```

and requires the deposit to be disjoint from `storage(s)` (`frame_exchange` in
`tsm_storage.rs`). Transitions with `birds_eye` reads or nondeterministic results use
the nondeterministic variants, in which `s` may determine the output.

These obligations are discharged from the user's `#[inductive]` lemmas (which give
`invariant(s')`) and from the safety conditions of `assert` statements. The update
is then justified by the `vstd` theorems that turn frame-preserving updates on the
model into updates of the underlying resource. The trusted base is therefore the
`vstd` `Resource` and storage-protocol primitives, as for any other use of those
libraries.

## The raw interface

With `#[verified_raw_tokens]`, the client works with values of type `M::Token`,
which is `Token<Protocol>` or `StorageToken<Protocol>`. A single token owns an
arbitrary fragment, so it may own parts of several fields at once. Fragments are
built and taken apart explicitly:

* `token.fragment()` and `token.loc()` observe the owned fragment and its location.
* `token.split(l, r)` requires `l · r == token.fragment()` and returns tokens owning
  `l` and `r`. `join` is its inverse.
* Fragment values are ordinary spec values of the generated `Fragment` record. For
  example, the exclusive component of a `variable` field `auth` is
  `f.auth->Some_0->Exclusive_0`.

Initialization and transitions are associated functions of `Protocol`:

```rust
let tracked token = MapOperands::Protocol::initialize(empty);
let tracked token = MapOperands::Protocol::add_one(token, 3nat, 30int);
let tracked token = MapOperands::Protocol::remove_one(token, 3nat);
```

`initialize` returns a token with `fragment() == embed(s0)` for the initial state
`s0`. A transition `t` takes the following arguments:

* the owned token;
* optionally a borrowed token `&shared` at the same location, for state that `t`
  reads but does not change;
* the deposited values, if `t` deposits;
* the transition parameters.

It returns the new token, plus the withdrawn values if `t` withdraws. Its
precondition is `Protocol::t_requires(owned, shared, deposit, x)`, which quantifies
over all completions of the combined fragment:

```text
∀ c, s.  invariant(s) ∧ (owned · shared) · c = embed(s)
    ⇒ enabled_t(s, x)                   -- t's require statements hold at s
      ∧ deposit = deposited_t(s, x)     -- the caller deposits exactly what t deposits
      ∧ owns_t(s, owned, shared, x)     -- owned contains every component t removes or
                                        -- updates; shared contains what t only reads
```

The postcondition gives the output fragment. For a deterministic transition it is
an explicit function of the input, `t_fragment`. Otherwise it is characterized by
`t_outputs`, which states that some completion `(c, s)` and some successor `s'` exist
with the following properties:

* the strong transition relation holds between `s` and `s'`;
* `invariant(s')` holds;
* the output, composed with `shared · c`, is `embed(s')`;
* the withdrawn map is `(storage(s) ∪ deposit) \ dom(storage(s'))`.

A client usually needs only consequences of this statement. Its witnesses can be
extracted with `t_witness`. Readonly transitions and properties take a borrowed
token and ensure facts about every completion. Storage guards return a shared
reference into the guarded storage map.

So the raw interface puts the separation-logic reasoning in the client: the client
chooses fragments and proves the quantified preconditions. It is the more
expressive of the two interfaces:

* One tracked value may carry an arbitrary combination of components.
* Any fragment-level fact the model supports can be used.

It also exposes the representation of the product algebra. Its operations are not
compatible with clients written against `tokenized_state_machine!`.

## The generic interface

With `#[verified_generic_tokens]` the macro generates the declarations that
`tokenized_state_machine!` would generate. The method signatures and their
`requires`/`ensures` clauses are produced by the same code
(`concurrency_tokens::exchange_parts`). A client of the trusted macro is therefore,
up to the differences listed below, also a client of this interface:

```rust
let tracked (Tracked(inst), Tracked(unused), Tracked(owner)) =
    P::Instance::initialize(free, Map::tracked_empty(), Map::tracked_empty());
let tracked o1 = inst.insert(1, 10, u1, 10, 10);   // consumes an `unused` token
let tracked g  = inst.peek(1, &o1);                // storage guard
```

### Representation

Each field token is a tracked struct with three parts:

* the token's ghost data (e.g. key and value for a `map` token);
* an `Option` of a raw protocol token;
* an `Option` of a private resource, used only by placeholders (see below).

A type invariant fixes the meaning. Either the raw token is present and its fragment
is exactly `ι_i(e)`, or the token is a placeholder. Here `ι_i` injects field `i`'s
component into the product, with every other component the unit, and `e` is the
singleton element given by the ghost data:

* `Exclusive(v)` for a `variable` token;
* `{k ↦ v}` for a `map`, `imap`, `persistent_map` or `persistent_imap` token;
* `{x}` for a `set`, `iset`, `persistent_set` or `persistent_iset` token, and the
  one-element multiset `{x}` for a `multiset` token;
* `Some(v)` for an `option` or `persistent_option` token;
* `true` for a `bool` or `persistent_bool` token;
* `n` for a `count` token, and a lower bound `m ≥ n` for a `persistent_count`
  token that reports `n` (so that `weaken` needs no update).

A field token is therefore ownership of `ι_i(e)` at `γ`. The collection types
(`<field>_map`, a `vstd::tokens::MapToken` or `IMapToken`; `<field>_set`;
`<field>_multiset`; and `Option<field>` for `option` and `bool` fields) are
collections of such tokens. Their fragments compose to `ι_i(m)` for the whole
collection `m`. Collections are built and taken apart one token at a time, so they
are finite; for `imap` and `iset` fields this is an added requirement (see below).

Persistent tokens hold a leaked `&'static` raw token instead of an owned one. Their
fragments are idempotent, so a shared reference is all an operation needs (they are
only ever observed), and the token types are `Copy`, as in the trusted macro.

The tokens implement the `vstd::tokens` traits (`ValueToken`, `KeyValueToken`,
`ElementToken`, `SimpleToken`, `MonotonicCountToken`, and the `Unique*` variants
where the strategy is exclusive). The trait lemmas are proved:

* **Agreement and uniqueness:** follow from validity of the composition of two
  tokens' fragments.
* **Instance identifiers:** are a function `tsm_instance_id` of the location.

`count` tokens provide the `CountToken` operations `count`, `join`, `split` and
`arbitrary` as inherent methods but do not implement the trait: its `weaken_shared`
returns a shared reference to a token with a smaller count, and no such token
exists to borrow from (a `&Self` cannot be made from a part of `self`).

The trusted interface also lets clients create a token with `arbitrary()`, for
example as a placeholder for `tracked_swap`. Here a placeholder owns a freshly
allocated private resource instead of a fragment. Its instance identifier is drawn
from a range disjoint from the identifiers of real instances: `vstd` proves that
`tsm_instance_id(loc, true)` and `tsm_instance_id(loc', false)` are never equal. No
placeholder carries the identifier of a real instance, so every precondition of the
form `t.instance_id() == self.id()` implies that `t` owns a fragment at `γ`. The
trait lemmas hold for placeholders because each owns its own resource.

`Instance` holds the ghost location `γ` and is `Copy`. It is not itself a resource.

Constants need more. `inst.c()` must equal `s.c` in every completion `s` of an
operation's fragments, so some fragment of the operation must contain the
agreement element `κ = ι_c(Agree(c))`, and the instance must know `c`. A machine
with `constant` fields therefore allocates, at initialization, a descriptor: an
agreement resource on `(c, γ)` at a fresh location `δ`, leaked to a `&'static`
reference. The instance holds the descriptor (so it stays `Copy`; the descriptor's
type does not involve the machine's protocol types), `inst.c()` reads it, and
instance identifiers are `tsm_instance_id(δ)`. Every token (and every `Unit`) holds
the same descriptor and its own copy of `κ` (`κ · κ = κ`, so copies are split off
freely): two holders of one identifier hold descriptors at `δ`, which agree, so
their constants and locations agree. An operation that reads a constant observes a
copy of `κ` from one of its tokens, so `κ` is part of its shared fragment.

### Operations

An operation's body proceeds in five steps:

1. **Join.** Consume the input tokens and compose their fragments,
   `a = ι_{i1}(e_1) · … · ι_{ik}(e_k)`. Borrowed inputs (and the instance's
   constants token, if a constant is read) are composed into a separate shared
   fragment `h`. A `&mut` token (a `variable` that the transition updates) is
   consumed and later replaced.
2. **Establish the raw precondition.** Prove `t_requires(a, h, deposit, x)` from
   the trusted-style precondition, which is stated over the tokens' ghost data. The
   key fact is that each `ι_i(e_j)` is included in `a · h · c = embed(s)`. This
   determines the corresponding part of field `i` in `s`, e.g. `s.owner[k] = v`.
   From that, the `require` statements and the ownership condition of `t` follow for
   every completion. The per-strategy facts are `vstd` lemmas
   (`vstd::resource::tsm_generic`, `tsm_collections`), proved once.
3. **Call the raw operation.**
4. **Characterize the output.** From `t_outputs`, prove that the output fragment
   equals `ι_{j1}(e'_1) · … · ι_{jm}(e'_m)` for exactly the elements named in the
   trusted-style postcondition. For storage operations, also prove that the
   withdrawn map contains the promised values.
5. **Split and wrap.** Split the output fragment and wrap each part in its field
   token.

Steps 2 and 4 are generated as separate proof functions, each verified in its own
solver context (`#[verifier::spinoff_prover]`). The proof cost of an operation is
then independent of the size of the rest of the generated module.

Storage operations deposit and withdraw through the raw protocol's storage map. With
one `storage_map` or `storage_imap` field its keys and values are the field's own;
`storage_option` fields use an index key; several storage fields of different kinds
use the raw protocol's tagged carrier (`__StorageKey`/`__StorageValue`). A machine
without storage fields uses the plain `vstd::resource::tsm::Token`.

### Differences from the trusted interface

* **Operations that consume no token.** Because `Instance` is not a resource, an
  operation that consumes no token has nothing to perform the update on. In a
  machine with storage fields, such operations take an extra argument of type
  `Unit`, which owns the unit fragment at `γ`. `Instance::unit_from_<field>(&mut t)`
  obtains one from any (non-persistent) token of the instance by splitting
  `ι_i(e) = ε · ι_i(e)`. In a machine without storage the unit is split off the
  instance's own token (`Token::empty`), so the signature is unchanged.
* **`count` tokens** do not implement `CountToken` (see above).
* **Finite `imap`/`iset` collections.** An operation that consumes or produces a
  token collection of an `imap`, `iset`, `persistent_imap` or `persistent_iset`
  field additionally requires the operand to be finite, and an initial value of
  such a field must be provably finite in the generated proof (e.g. `IMap::empty()`
  or finitely many `insert`s; not `ISet::full()`, nor `IMap::new` over a range).
  Infinitely many tokens cannot be split off one resource.
* **Type parameters.** A machine with type parameters and a persistent field (or a
  constant whose type mentions a type parameter, or an operation without storage
  that consumes no token) requires its type parameters to be `'static`: it holds
  leaked `&'static` raw tokens.
* **Supported fields.** The interface currently supports:
  * every sharding strategy: `variable`, `constant`, `not_tokenized`, `option`,
    `persistent_option`, `map`, `persistent_map`, `imap`, `persistent_imap`, `set`,
    `persistent_set`, `iset`, `persistent_iset`, `multiset`, `bool`,
    `persistent_bool`, `count`, `persistent_count`, `storage_option`,
    `storage_map` and `storage_imap`;
  * any number of storage fields;
  * machines with or without type parameters;
  * consumed token collections for `map`, `imap`, `set`, `iset`, `multiset`,
    `option` and `bool` fields, and produced collections for all collection
    strategies;
  * guards with one output.

  Borrowed token collections (`have f >= (e)` for a collection strategy; the
  `vstd::tokens` collection types give no access to their tokens through a shared
  reference), general withdrawals from a tagged `storage_imap`, and labels are
  rejected at expansion time.

## Comparison

| | `#[verified_raw_tokens]` | `#[verified_generic_tokens]` |
| --- | --- | --- |
| Client-held resource | `Token`: an arbitrary fragment of the product algebra | One type per field; each owns `ι_i(e)` for a singleton `e` |
| Splitting and combining | Explicit, by fragment arithmetic (`split`, `join`) | By the operations' signatures and token collections |
| Operation preconditions | Quantified over all completions of the input fragments; proved by the client | Stated over tokens' ghost data, as in the trusted macro; the completion argument is generated |
| Operation postconditions | Output fragment, or an existential over a completion and successor state | Values of the output tokens, as in the trusted macro |
| `Instance` | None; the location is that of the token | `Copy` value carrying the location (and a shared token with the constants) |
| Operations without input tokens | Take a token of the instance (it may own the unit fragment) | Take a `Unit` in machines with storage; unchanged otherwise |
| `vstd::tokens` traits | Not implemented | Implemented, with proofs |
| Source compatibility with `tokenized_state_machine!` clients | No | Yes, except for `Unit` (storage machines), `count` tokens without `CountToken`, and `'static` type parameters (see above) |
| Field kinds and statement forms | Those supported by the verified backend | A subset (see above), on top of the raw backend |
| Trusted code added | None | None |

Use the generic interface to port a client of `tokenized_state_machine!`, or when
ownership naturally divides along fields. Use the raw interface in three cases:

* a single tracked value must carry components of several fields;
* a proof needs facts about fragments that the per-field contracts do not state;
* the machine uses a field kind or statement form the generic interface does not
  support yet.

Both interfaces allow a storage payload to contain the machine's own tokens.
Verus's strict-positivity check applies to the resulting datatype cycle and rejects
negative occurrences, such as a token type in the argument of a `spec_fn`.

Without either attribute, the macro selects one of several field-specific interfaces
based on the machine's fields. Those are outside the scope of this chapter.
