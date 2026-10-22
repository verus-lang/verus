# Checked tokens: raw and generic interfaces

`verified_tokenized_state_machine!` accepts the same machine syntax as
`tokenized_state_machine!`, but the operations on the ghost resources it generates are
proved rather than trusted. It offers two interfaces to those resources:

* The **generic interface** is the default. It generates the interface of the trusted
  `tokenized_state_machine!`: one token type per field, `Instance` methods with the
  same signatures and specifications, and implementations of the `vstd::tokens`
  traits. Every method body is a proof that calls the corresponding raw operation.
  `#[verified_generic_tokens]` selects it explicitly; the attribute is optional.
* `#[verified_raw_tokens]` exposes the machine's resource algebra directly. A client
  owns fragments of the whole product algebra and calls operations whose
  preconditions are stated over fragments.

The two interfaces share the generated model and its proofs. The generic interface is
a layer over the raw one: it adds no assumptions and no external bodies. This chapter
describes the shared model, then each interface, then how they differ.

The attributes are written before the machine name, e.g.
`verified_tokenized_state_machine!{ #[verified_raw_tokens] X { .. } }`. Combining the
two, repeating one, or giving one arguments is an error. The former
`#[verified_field_tokens]` attribute marked the earlier default, a set of
field-shape-specific interfaces; it was removed together with them and is now
rejected with a diagnostic. The former `#[verified_local_ready(..)]` attribute,
which selected the transitions with a local-ready API, is rejected likewise: the
raw interface now generates that API for every transition it supports (see
"Local readiness" below).

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
  currently deposited values, an `IMap<__StorageKey, __StorageValue>` tagged by
  storage field (see "Storage" below).

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

All deposits and withdrawals of one transition form one such exchange, so a
transition cannot deposit into a location it withdrew from earlier: replacing a
stored value (`withdraw f -= Some(a); deposit f += Some(b);` on a `storage_option`
field, or the same key of a `storage_map`) needs two values at one location. The
trusted macro accepts such a transition; the checked macro rejects it (with either
interface) at the deposit if the location is syntactically the same (a
`storage_option` field's single location, keys with the same text, the keys of
general `Map::empty().insert(k, v)` operands), and otherwise the storage proof fails
at the deposit, with the same hint. The workaround splits the transition in two,
with the intermediate state explicit in the machine (a withdrawn location is "in
flight" until the second transition deposits): see
[`storage_replace_in_two_transitions.rs`](../../../../examples/verified_tsm/storage_replace_in_two_transitions.rs),
whose clients replace a value by calling both operations.

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
* the withdrawn map is `(storage(s) ∪ deposit) \\ dom(storage(s'))`.

A client usually needs only consequences of this statement. Its witnesses can be
extracted with `t_witness`. Readonly transitions and properties take a borrowed
token and ensure facts about every completion. Storage guards return a shared
reference into the guarded storage value.

### Local readiness

The raw interface adds, for every transition, readonly transition and property
(not initializers), operations whose precondition is local, except for the forms
listed at the end of this section. (The generic interface has none: every generic
operation already has a token-level precondition and a generated readiness proof.)

The local-ready API of `t` is in its own namespace: the associated items of the
generated type `local_ready::t` in the machine module (`M::local_ready::t::<T>` for a
machine with type parameters `T`), so its names cannot collide with other
transitions' generated items or with the machine's own functions.
`local_ready::t::precondition(owned, shared, deposit, x)` states
`t`'s `require`s (`local_ready::t::declared_requires`), its ownership condition and
its deposit (`local_ready::t::deposited`) over the state observed in
`owned · shared` alone (`Protocol::__observed`), without quantifying over
completions. A value that a `remove` or `have` binds by a pattern (`[k => let v]` of
a map, `Some(let x)` of an option, exclusive or persistent, also refutable) is the
supplied fragments' (`owned`'s entry if it has one, else `shared`'s): such a
transition's local state is `local_ready::t::local_state(owned, shared, x)`, the
observation with these entries (a transition whose operand keys a `let` or a
pattern binds also names its local state so, as does one whose `require` has a
quantifier or whose operand reads `pre`: a quantifier's trigger cannot be in the
observation's conditionals). The generated lemma
`local_ready::t::ready` proves that the precondition implies
`Protocol::t_requires`, for every completion; `local_ready::t::run` and
`local_ready::t::run_with_shared` are `Protocol::t` and `Protocol::t_with_shared`
with the local precondition, and `local_ready::t::observed` also returns ghost
`before`, `after` and `frame` values of one compatible completion together with the
withdrawn map (a `TransitionObservation`). On a machine without storage fields the
operations are over the plain `Token` and have no deposit or withdrawal:
`local_ready::t::precondition(owned, shared, x)`, `local_ready::t::run(owned, x)`
returns the token, and the `TransitionObservation` has no `withdrawn` field.

```rust
// Before: let tracked token = M::Protocol::put_two_local(token, deposit, a, b);
let tracked token = M::local_ready::put_two::run(token, deposit, a, b);
```

These states describe some completion, not a distinguished global history.

A readonly transition or property without a `guard` has the raw operation of a
mutating transition (the token is passed and returned; nothing is deposited or
withdrawn), and the same local-ready API. One with a `guard` borrows the token:
`local_ready::t::precondition(f, x)` is stated over the borrowed fragment `f` (its
local state, if named, is `local_ready::t::local_state(f, x)`),
`local_ready::t::ready(f, x)` proves `Protocol::t_requires(f, x)`, and
`local_ready::t::run(&token, x)` returns the same shared reference into the storage
as `Protocol::t`, with `*out == Protocol::t_guarded(token.fragment(), x)`.

```rust
// `property! { peek(k: int) { have m >= [k => let v]; guard stored >= [k => Tok { v }]; } }`
let tracked g = M::local_ready::peek::run(&token, k);
```

The local precondition is stated over the supplied components; a client
establishes it from what its tokens show (a `require` over a component the client
does not hold cannot be established). The generated `ready` lemma is proved for
every transition that gets the API. The macro skips (without an error) the
transitions of the following syntactic forms, whose readiness proof the macro
cannot generate; they keep their other raw operations (`Protocol::t`,
`Protocol::t_requires`, ...), and `local_ready::t` does not exist:

* a closure (`|x| ..`, not a quantifier's binder) in an operand of a `remove`,
  `have`, `add`, `deposit`, `withdraw` or `guard`, in the value of a `let`, in an
  `if` condition, or in a `match` scrutinee or arm guard (a closure in a `require`,
  `assert` or `update` is fine);
* a `have` of a `map`, `imap`, `set` or `iset` field, or of their `persistent_`
  versions, after an `add` to the same field on some path (e.g. `remove m -= [k => 0];
  add m += [k => 1]; have m >= [j => 1];`); `option`, `multiset`, `count` and `bool`
  fields are not affected;
* a `require` that the local requirement cannot state (one under a binding other
  than a `let`, `if`, `match`, `remove` or `have`; TSM itself rejects these).

The rule is in `verified_readiness::local_ready_supported`.

So the raw interface puts the separation-logic reasoning in the client: the client
chooses fragments and proves the quantified preconditions. It is the more
expressive of the two interfaces:

* One tracked value may carry an arbitrary combination of components.
* Any fragment-level fact the model supports can be used.

It also exposes the representation of the product algebra. Its operations are not
compatible with clients written against `tokenized_state_machine!`.

## The generic interface

By default (or with `#[verified_generic_tokens]`) the macro generates the declarations that
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
(`<field>_map`, a `vstd::tokens::MapToken`; `<field>_set`, a `SetToken`;
`<field>_multiset`; and `Option<field>` for `option` and `bool` fields) are finite
collections of such tokens. Their fragments compose to `ι_i(m)` for the whole
collection `m`.

The collections of `imap`, `iset`, `persistent_imap` and `persistent_iset` fields
may be infinite (e.g. `init m = IMap::new(|k| true, |k| None)`, or
`ISet::full()`). `vstd::tokens::IMapToken` holds one tracked token per key, and no
`vstd` primitive splits one resource into infinitely many, so these fields use
generated collection types in reservation style instead: `<field>_map` (or
`<field>_set`) holds one raw token owning `ι_i(bm)` for a possibly infinite part
`bm`, plus finitely many individual tokens. `remove(k)` splits the token for `k` off
the bulk on demand; `insert` adds an individual token. An operation that consumes a
sub-collection splits it off the bulk in one step, and one that produces a
collection hands out its fragment as a new bulk. A borrowed sub-collection `e`
(`have f >= (e)`) is observed through the bulk and the individual tokens for the
keys of `e`; the joined observation is valid, so each element of `e` is exactly
owned in it, and it includes `ι_i(e)`. The types provide the methods of
`IMapToken`/`ISetToken` (`empty`, `insert`, `remove`, `map`/`set`, `dom`,
`index`, `contains`, `instance_id`, `into_map`, `from_map`); `into_map` and
`from_map` require finite maps. For finite collections, `into_imap_token` and
`from_imap_token` (`into_iset_token`/`from_iset_token`) convert to and from
`vstd::tokens::IMapToken` (`ISetToken`).

A borrowed collection of a finite strategy (`have f >= (e)` for `map`, `set`,
`multiset`, `option`, `bool` and their persistent variants) is observed token by
token: the `vstd::tokens` collection types provide `borrow(k)`, a shared
reference to the token for `k` (`MultisetToken::borrow` is proved from the
multiset's fold), the observations are joined, and the joined observation is
valid, so each element of `e` is exactly (or, for persistent strategies, up to
agreement) owned in it. For a multiset this shows each element of `e` at least
once, so the borrowed part `e` must not contain an element twice: shared
references to two tokens do not show that the tokens are distinct resources. The
generated operation checks this first (`forall|x| e.count(x) <= 1`), so a machine
states it with a `require`; otherwise verification reports "the borrowed part of
multiset field `f` must not contain an element twice" at the `have` statement.
Separate singleton borrows (`have f >= {x}; have f >= {y}`) need no such
condition: the model requires each of them once, also for `x == y`.

In a machine without type parameters, persistent tokens hold a leaked `&'static`
raw token instead of an owned one. Their fragments are idempotent, so a shared
reference is all an operation needs (they are only ever observed), and the token
types are `Copy`, as in the trusted macro. In a machine with type parameters a
leaked reference would need the parameters to be `'static`, so persistent tokens
own their raw tokens there and are not `Copy`; `clone` duplicates the raw token.
Without storage it takes `&self` (`Token::duplicate`); a storage-protocol
resource can only be split (`x = x · x`), so in a machine with storage `clone`
takes `&mut self`, and so does `weaken` of a `persistent_count` token, which then
provides its operations as inherent methods instead of `MonotonicCountToken`
(whose `weaken` takes `&self`).

The tokens implement the `vstd::tokens` traits (`ValueToken`, `KeyValueToken`,
`ElementToken`, `SimpleToken`, `MonotonicCountToken`, and the `Unique*` variants
where the strategy is exclusive). The trait lemmas are proved:

* **Agreement and uniqueness:** follow from validity of the composition of two
  tokens' fragments.
* **Instance identifiers:** are a function `tsm_instance_id` of the location.

`count` tokens provide the `CountToken` operations `count`, `join`, `split` and
`arbitrary` as inherent methods but do not implement the trait: its
`weaken_shared(&self, n)` returns a `&Self` whose count is `n`. Such a reference
must point to a token value reachable from `self` (the only memory with the
lifetime of `&self`), and a token's value determines its count, so `self` would
have to contain tokens for every smaller count. Each such token owns its count by
the type invariant, and owned counts add up, so a token of count `n` cannot also
contain tokens of the smaller counts; a variant that owns nothing would carry the
instance's identifier without owning a fragment, which the operations'
preconditions rely on. Observations of the parts of a token (which could be
shared) do not add up either: a shared observation shows inclusion, not the sum of
disjoint parts.

The trusted interface also lets clients create a token with `arbitrary()`, for
example as a placeholder for `tracked_swap`. Here a placeholder owns a freshly
allocated private resource instead of a fragment. Its instance identifier is drawn
from a range disjoint from the identifiers of real instances: `vstd` proves that
`tsm_instance_id(loc, true)` and `tsm_instance_id(loc', false)` are never equal. No
placeholder carries the identifier of a real instance, so every precondition of the
form `t.instance_id() == self.id()` implies that `t` owns a fragment at `γ`. The
trait lemmas hold for placeholders because each owns its own resource.

`Instance` holds the ghost location `γ` and is `Copy`. It is not itself a resource.
(If an operation of a machine without storage consumes and borrows no token, or a
guard borrows no token, it also holds a leaked `&'static` token owning the unit
fragment, from which such operations take their unit or guard. In a machine with
type parameters and without storage it owns that token instead, so the parameters
need not be `'static`. A storage token can be split but not duplicated, so an
instance owning one would not be clonable: in a machine with type parameters and
storage, a guard that borrows no token borrows a `Unit` of the instance instead,
an extra last argument `&Unit`.) Its type invariant also states that some
invariant-satisfying state has the instance's constants: the initial state is
one. An operation that observes no fragment (such as a property whose assertion
reads only constants, or one whose borrowed collections are all empty) reasons
about that state.

Constants need more. `inst.c()` must equal `s.c` in every completion `s` of an
operation's fragments, so some fragment of the operation must contain the
agreement element `κ = ι_c(Agree(c))`, and the instance must know `c`. A machine
with `constant` fields therefore allocates, at initialization, a descriptor: an
agreement resource on `(c, γ)` at a fresh location `δ`, leaked to a `&'static`
reference. The instance holds the descriptor (so it stays `Copy`; the descriptor's
type does not involve the machine's protocol types), `inst.c()` reads it, and
instance identifiers are `tsm_instance_id(δ)`. If a constant's type mentions a type
parameter, a leaked descriptor would need the parameters to be `'static`; every
holder then owns a copy of the descriptor instead (agreement resources duplicate),
and `Instance` is not `Copy`: `clone` duplicates its descriptor (and its unit
token, if it owns one). Every token (and every `Unit`) holds
the same descriptor and its own copy of `κ` (`κ · κ = κ`, so copies are split off
freely): two holders of one identifier hold descriptors at `δ`, which agree, so
their constants and locations agree. An operation that reads a constant observes a
copy of `κ` from one of its tokens, so `κ` is part of its shared fragment. (The
observation of a borrowed collection, also of an `imap`/`iset` field, joins the
copies of `κ` of its tokens, so a read-only operation whose only borrowed inputs
are collections finds `κ` there, or, if they are all empty, reasons about the
instance's reachable state.)

### Operations

An operation's body proceeds in five steps:

1. **Join.** Consume the input tokens and compose their fragments,
   `a = ι_{i1}(e_1) · … · ι_{ik}(e_k)`. Borrowed inputs (and a copy of `κ`, if a
   constant is read) are composed into a separate shared fragment `h`. A `&mut` token (a `variable` that the transition updates) is
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

### Storage

The raw protocol's storage is one map `IMap<M::__StorageKey, M::__StorageValue>`,
the storage of vstd's `StorageResource<K, V, P>`, for every machine with storage
fields (also one with a single storage field, or with storage fields of one
payload type). The two generated enums have one variant per storage field `f`:

```rust
tokenized_state_machine!{ M { fields {
    #[sharding(storage_map)]    pub m: Map<Foo, Bar>,
    #[sharding(storage_option)] pub o: Option<Baz>,
} ... } }

pub enum __StorageKey   { m(Foo), o }       // a key variant per storage field
pub enum __StorageValue { m(Bar), o(Baz) }  // its payload
```

A `storage_map` or `storage_imap` field's entry at `k` is stored under
`__StorageKey::f(k)`, a `storage_option` field's value under `__StorageKey::f`,
always as `__StorageValue::f(v)`. Each enum takes the machine's type parameters
that its variants mention. The state's storage `s.__storage()` is the union of
the fields' tagged parts `__tag_f(s.f)` (`__tag_f(s.f.to_imap())` for a
`storage_map`); with several storage fields not all `storage_option`, it is
defined per key (`State::__storage_dom`/`__storage_val`, which keeps the solver's
work per key independent of the number of fields), equal to the union
extensionally (clients compare with `=~=`). A machine without storage fields uses the plain
`vstd::resource::tsm::Token`.

For each storage field `f` the machine's module has helpers (generic over the
type parameters the storage types mention): `__tag_f`/`__untag_f` (spec) between
the field's value and its tagged part, the tracked conversions `__pack_f` (a
field's `Option<V>`, or a finite `Map<K, V>`, to its tagged part) and `__unpack_f`
(back, for a finite tagged part), `__borrow_f` (a reference to a stored payload)
and `__unwrap_f` (the payload of one tracked `__StorageValue`). Tagging and
untagging a tracked map move its entries one by one, so they need a finite
domain.

Raw clients therefore pass and receive tagged maps: the initializer takes the
initial storage (`initialize(IMap::tracked_empty())`, or `__pack_f` of the
initial value), a deposit is the tagged map of the deposited values (built with
`tracked_insert(M::__StorageKey::f(k), M::__StorageValue::f(v))`, or
`M::__pack_f(Some(v))`), a withdrawal returns one
(`M::__unwrap_f(w.tracked_remove(M::__StorageKey::f(k)))`), and a guard returns a
reference into one (`M::__borrow_f(g, k)`). A transition's deposited value is
the union of its deposits' tagged parts (one deposit: the tagged part itself).
Comparisons of client-built maps with the machine's values are extensional
(`assert(d =~= M::State::t_deposited(pre))`). The examples
`raw_forms_storage_option.rs`, `raw_forms_storage_map.rs`,
`raw_forms_storage_many_fields.rs` and `tagged_storage_api.rs` show these forms.

A storage guard guards from the joined observation of its borrowed tokens; a guard
that borrows no token guards from the instance's unit token. For the general
operands of the trusted interface (`guard f >= (e)`), whose output types
`&Option<V>` and `&Map<K, V>` are not references into the guarded storage, the
generic interface returns references into the storage instead: `&V` for
`guard f >= (Some(v))` and `Option<&V>` for any other operand of a
`storage_option` field. For a `storage_map` field it returns a map of references
into the storage, `Map<K, &V>` with the domain of `m` and `*out[k] == m[k]`;
for a `storage_imap` field `IMap<K, &V>`, built key by key, so its operand must
have a finite domain, which the machine states with a `require`. A guard may
have several outputs.

### Differences from the trusted interface

* **Operations that consume no token.** Because `Instance` is not a resource, an
  operation that consumes no token has nothing to perform the update on. In a
  machine with storage fields, such operations take an extra argument of type
  `Unit`, which owns the unit fragment at `γ`. Units come from three sources:
  `Instance::unit_from_<field>(&mut t)` splits one off any (non-persistent) token
  of the instance (`ι_i(e) = ε · ι_i(e)`); the initializer `<init>_with_unit` is
  `<init>` that also returns a `Unit` (for machines whose only tokenized state is
  storage and constants, which have no field token); and `Unit::split` divides a
  unit into two (`ε = ε · ε`). In a machine without storage the unit is split off
  a borrowed token of the operation, or else the instance's own token
  (`Token::empty`), so the signature is unchanged.
* **`count` tokens** do not implement `CountToken` (see above).
* **No deposit into a location withdrawn earlier in the same transition** (a
  replace of a stored value; see "The shared model" above): such a transition is
  rejected at the deposit; split it in two with the intermediate state explicit,
  as in
  [`storage_replace_in_two_transitions.rs`](../../../../examples/verified_tsm/storage_replace_in_two_transitions.rs).
* **Guards of general operands** return references into the guarded storage
  (`&V`, `Option<&V>`, or `Map<K, &V>`/`IMap<K, &V>`, see "Storage" above)
  instead of `&Option<V>` or `&Map<K, V>`.
* **General `storage_imap` operands need a finite domain.** A general deposit
  into, withdrawal from or guard of a `storage_imap` field, and its initial
  value, are tagged into (or taken out of) the storage map key by key, so the
  operand's domain must be finite; the machine states it with a `require`
  (for a withdrawal, also in an invariant). Verification reports a diagnostic
  at the operand otherwise. Singleton operands and `storage_map` fields (finite
  maps) need nothing.
* **Persistent tokens and `Instance` in machines with type parameters** are not
  `Copy` where they own their resources (see above); clients call `clone` (with
  `&mut self` for persistent tokens of a machine with storage).
* **`imap`/`iset` collection types.** For `imap`, `iset`, `persistent_imap` and
  `persistent_iset` fields, `<field>_map`/`<field>_set` are generated types (see
  above), not `vstd::tokens::IMapToken`/`ISetToken`; client code that names
  `IMapToken<K, V, M::field>` must name `M::field_map` instead. Their `into_map`
  and `from_map` require finite maps.
* **Guards without borrowed tokens in machines with type parameters and
  storage** take an extra argument `&Unit` (see above), as operations that
  consume no token take a `Unit`; the type parameters need no `'static` bound.
* **Supported fields.** The interface currently supports:
  * every sharding strategy: `variable`, `constant`, `not_tokenized`, `option`,
    `persistent_option`, `map`, `persistent_map`, `imap`, `persistent_imap`, `set`,
    `persistent_set`, `iset`, `persistent_iset`, `multiset`, `bool`,
    `persistent_bool`, `count`, `persistent_count`, `storage_option`,
    `storage_map` and `storage_imap`;
  * any number of storage fields;
  * machines with or without type parameters;
  * consumed token collections for `map`, `imap`, `set`, `iset`, `multiset`,
    `option` and `bool` fields, borrowed token collections for all collection
    strategies, and produced (also infinite, for `imap` and `iset` strategies)
    collections for all collection strategies;
  * guards with or without borrowed tokens, of singleton and general operands,
    with any number of outputs;
  * operations without any token (with a `Unit`, see above), and properties that
    read only constants or nothing;
  * labeled machines: init and transition labels (also with the machine's type
    parameters) are the first parameters of the generated operations.

  General deposits into, withdrawals from and guards of `storage_imap` fields,
  and their initial values, need operands of a finite domain, which the
  machine states with a `require` (see "Differences" above; verification
  reports a diagnostic at the operand otherwise). A borrowed multiset part
  needs a similar `require` (see above).

## Comparison

| | `#[verified_raw_tokens]` | Generic (default, or `#[verified_generic_tokens]`) |
| --- | --- | --- |
| Client-held resource | `Token`: an arbitrary fragment of the product algebra | One type per field; each owns `ι_i(e)` for a singleton `e` |
| Splitting and combining | Explicit, by fragment arithmetic (`split`, `join`) | By the operations' signatures and token collections |
| Operation preconditions | Quantified over all completions of the input fragments; proved by the client (or local, with the generated `local_ready::t` operations) | Stated over tokens' ghost data, as in the trusted macro; the completion argument is generated |
| Operation postconditions | Output fragment, or an existential over a completion and successor state | Values of the output tokens, as in the trusted macro |
| `Instance` | None; the location is that of the token | `Copy` value carrying the location (and shared resources); with type parameters, possibly an owned copy (`clone`) |
| Operations without input tokens | Take a token of the instance (it may own the unit fragment) | Take a `Unit` in machines with storage; unchanged otherwise |
| `vstd::tokens` traits | Not implemented | Implemented, with proofs |
| Source compatibility with `tokenized_state_machine!` clients | No | Yes, except for `Unit` (storage machines), `count` tokens without `CountToken`, the outputs of guards of general operands, finite domains of general `storage_imap` operands, and non-`Copy` persistent tokens and instances of machines with type parameters (see above) |
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

Without an attribute the macro generates the generic interface. Earlier versions
instead selected one of several field-specific interfaces from the exact shape of the
machine's fields (with `#[verified_field_tokens]` as an explicit marker, and
`#[verified_local_ready]` on that route); those interfaces have been removed.
`#[verified_local_ready(..)]` then selected the raw transitions with a local-ready
API; it was removed when that API became the raw interface's default.
