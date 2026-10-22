# Tokenized state machines upgrade

Use `verified_tokenized_state_machine!` to generate resource definitions and
protocol proofs that Verus checks. The proofs use the existing PCM and storage
protocol libraries. The macro adds no axioms and no executable locks.
`tokenized_state_machine!` remains available.

Keep the machine fields, transitions, invariants, and executable algorithm.
By default the checked macro generates the interface of the trusted macro: the
same field token types, `Instance` methods, signatures and specifications, and
the `vstd::tokens` traits. A client of `tokenized_state_machine!` is therefore,
up to the differences listed in Change 2, also a client of the checked macro.

Each section gives signatures and uses from existing examples. The signatures
omit bodies, visibility, attributes, and contracts unless a contract changes.
They use current Verus mode syntax. A signature block is a comparison, not a
complete program.

“Before” means the original VerusSync example. “After” means the current
checked example. This chapter does not describe upgrades between checked
implementation versions, except for the note at the end of Change 3.

The first section describes changes to generated TSM APIs and proofs.
The second section describes changes to example and application code.
A machine name in an API example belongs to that example, not to the TSM library.
For implementation details, see the
[implementation comparison](tsm-implementation-comparison.md) and
[Checked tokens: raw and generic interfaces](state_machines/src/checked-token-interfaces.md).

## Changes to the TSM system itself

### Change 1: Generate checked proofs

Replace the macro import and invocation. The machine declaration uses the same
`fields`, `init!`, `transition!`, `property!`, and sharding syntax.

The example is Counting2,
[counting_to_2.rs](../../examples/state_machines/tutorial/counting_to_2.rs), which
verifies unchanged with either macro (its import selects the macro by
`cfg(verus_verified_tsm)`).

**Before — declaration:**

```rust
use verus_state_machines_macros::tokenized_state_machine;

tokenized_state_machine!(X {
    // The Counting2 declaration.
});
```

**After — declaration:**

```rust
use verus_state_machines_macros::verified_tokenized_state_machine;

verified_tokenized_state_machine!(X {
    // The Counting2 declaration.
});
```

**Generated signatures in `X::Instance` (retained):**

```rust
proof fn initialize() -> (tracked out: (
    Tracked<Self>, Tracked<counter>, Tracked<inc_a>, Tracked<inc_b>,
));
proof fn tr_inc_a(
    tracked &self,
    tracked counter: &mut counter,
    tracked inc_a: &mut inc_a,
);
```

**Use (retained):**

```rust
globals.instance.borrow().tr_inc_a(&mut c, &mut token);
```

The old macro trusts generated resource operations. The new macro proves them:
every `Instance` method is a proof that calls an operation of the machine's
resource algebra (the raw interface, Change 3). `Instance` and persistent tokens
are `Copy`, and their `clone` methods promise `out == *self`, as before.
`Instance::id()` returns `vstd::tokens::InstanceId`. The `vstd::tokens` traits
(`ValueToken`, `KeyValueToken`, `ElementToken`, `SimpleToken`,
`MonotonicCountToken` and their `Unique*` variants) are implemented with proofs.

For a mathematical model with no token or property client, use
`verified_state_machine_model!`. The ordinary
[Adder](../../examples/state_machines/adder.rs) example uses unannotated fields
and runs unchanged with either macro.
Their generated state relation signatures are retained:

```rust
// Before: state_machine! — methods on X::State.
spec fn initialize(post: Self) -> bool;
spec fn add(pre: Self, post: Self, n: int) -> bool;

// After: verified_state_machine_model! — methods on X::State.
spec fn initialize(post: Self) -> bool;
spec fn add(pre: Self, post: Self, n: int) -> bool;
```

This entrypoint generates states and relations. It does not generate token or
property methods.

### Change 2: Differences in the generated interface

The following differences can require client changes. Their reasons are given
in [Checked tokens: raw and generic interfaces](state_machines/src/checked-token-interfaces.md).

#### Operations without input tokens take a `Unit` in storage machines

`Instance` is not a resource. In a machine with storage fields, an operation that
consumes no token takes an extra `tracked Unit` argument, which owns the unit
fragment of the instance. `Instance::unit_from_<field>(&mut t)` obtains one from
any non-persistent token `t` of the instance; `<init>_with_unit` is the
initializer `<init>` that also returns a `Unit` (for a machine with no such
token, e.g. one whose only tokenized state is storage); `Unit::split` makes two
units of one. Machines without storage are unchanged.

The example is the `Bank` machine of
[generic_tokens_kinds.rs](../../examples/verified_tsm/generic_tokens_kinds.rs)
(module `option_storage`),
whose `store` operation consumes only a token collection:

```rust
// Trusted macro:
proof fn store(tracked &self, m: Map<int, int>, tracked free: SetToken<int, free>,
    tracked vault: IMap<int, int>) -> (tracked out: MapToken<int, int, claims>);
// Checked macro:
proof fn store(tracked &self, m: Map<int, int>, tracked free: SetToken<int, free>,
    tracked vault: IMap<int, int>, tracked unit: Unit) -> (tracked out: MapToken<int, int, claims>);
```

```rust
let tracked u = inst.unit_from_epoch(&mut epoch);
let tracked c = inst.store(m, free, deposit, u);
```

#### Persistent tokens and instances of machines with type parameters

In a machine with type parameters, persistent tokens own their resources (a
leaked `&'static` resource would need the parameters to be `'static`), so they
are not `Copy`: clients call `clone`, which takes `&mut self` in a machine with
storage (and so does `weaken` of a `persistent_count` token there, an inherent
method). Likewise the instance is not `Copy` if a constant's type mentions a
type parameter (it owns its descriptor) or if it owns a unit token; `clone`
duplicates them. The Interner example (Change 5) shows this. In a machine with
type parameters and storage, a guard that borrows no token takes an extra
argument `&Unit` (a unit of the instance, see above), so that no parameter
needs to be `'static`.

#### Guards of general operands

A guard of a general operand returns a reference into the guarded storage
instead of `&Option<V>` or `&Map<K, V>`: `&V` for `guard f >= (Some(v))`,
`Option<&V>` for another operand of a `storage_option` field, and a map of
references `Map<K, &V>` for a `storage_map` field (`IMap<K, &V>` for a
`storage_imap` field, whose operand needs a finite domain). The guarded storage
holds the payloads tagged by field, so no `&Map<K, V>` or `&IMap<K, V>` of the
operand exists in it. A client that compared the output with the operand
(`*g == m`) compares domains and entries instead
(`g.dom() == m.dom()`, `*g[k] == m[k]`).

#### Count tokens and infinite collections

* `count` tokens provide `count`, `join`, `split` and `arbitrary` as inherent
  methods but do not implement `vstd::tokens::CountToken`.
* For `imap`, `iset`, `persistent_imap` and `persistent_iset` fields,
  `<field>_map`/`<field>_set` are generated types with the methods of
  `IMapToken`/`ISetToken`, not those `vstd::tokens` types; their `into_map` and
  `from_map` require finite maps. Client code that names
  `IMapToken<K, V, M::field>` must name `M::field_map` instead, or convert a
  finite collection with `into_imap_token`/`from_imap_token`
  (`into_iset_token`/`from_iset_token`).

#### Unsupported forms

Some statement forms need conditions the trusted interface does not state, which
the machine states with a `require` (verification reports a diagnostic at the
statement otherwise): a borrowed multiset part (`have f >= (e)`) must not
contain an element twice, and the general operands of a `storage_imap` field
(deposits, withdrawals, guards, and its initial value) need a finite domain;
they are tagged into the storage map key by key (a withdrawal's finiteness may
also come from an invariant). The complete list is in
[Checked tokens: raw and generic interfaces](state_machines/src/checked-token-interfaces.md).
Such a machine needs the raw interface (Change 3) or a rewritten transition.

A transition that deposits into a storage location it withdrew from earlier (a
replace: `withdraw f -= Some(a); deposit f += Some(b);`, or the same key of a
`storage_map`) is rejected with either interface, at the deposit: the checked
macro proves a transition's storage update as one exchange whose deposit is
disjoint from the current storage. Split the transition in two, with the
intermediate state explicit (a field recording that the location is in flight),
and call both operations where the client replaced the value; see
[storage_replace_in_two_transitions.rs](../../examples/verified_tsm/storage_replace_in_two_transitions.rs).

### Change 3: Select the raw interface explicitly

`#[verified_raw_tokens]` exposes the machine's resource algebra instead of field
tokens. A client owns fragments of the product algebra and proves preconditions
quantified over all completions. With `#[verified_raw_tokens]`,
`#[verified_local_ready(t, ..)]` adds raw operations for the named transitions
whose precondition is stated over the supplied fragments; the macro proves that it
implies readiness for every completion. They are the associated items of the type
`M::local_ready::t`: `local_ready::t::run(..)` is `Protocol::t(..)` with the local
precondition `local_ready::t::precondition(..)` (earlier checked versions named
these `Protocol::t_local(..)` and `Protocol::t_local_requires(..)`; likewise
`t_local_ready`, `t_local_with_shared`, `t_observed` and `t_local_state` are now
`ready`, `run_with_shared`, `observed` and `local_state`). On the default interface the attribute is
accepted and only its names are checked: the generic operations already have
token-level preconditions.

```rust
verified_tokenized_state_machine!{
    #[verified_raw_tokens]
    #[verified_local_ready(add_one)]
    MapOperands {
        // The machine.
    }
}
```

`#[verified_generic_tokens]` selects the default interface explicitly.

The raw protocol's storage value is one map `IMap<M::__StorageKey,
M::__StorageValue>`, tagged by storage field: the key `__StorageKey::f(k)`
(`__StorageKey::f` for a `storage_option`) holds `__StorageValue::f(v)`. Raw
clients pass and receive such maps: `initialize(IMap::tracked_empty())`, a
deposit built with `tracked_insert(M::__StorageKey::f(k), M::__StorageValue::f(v))`
or `M::__pack_f(Some(v))` (`M::__pack_f(m)` for a finite `Map`), a withdrawal
taken apart with `M::__unwrap_f(w.tracked_remove(M::__StorageKey::f(k)))`, and a
guard read with `M::__borrow_f(g, k)`; see
[Checked tokens: raw and generic interfaces](state_machines/src/checked-token-interfaces.md).
Raw clients of earlier checked versions port as follows: those that passed
`IMap<K, V>` (one map field) or `IMap<int, V>` (options of one value type, keyed
by index) tag their keys and values (the `M::__StorageKey::__pack_f`-style
helpers of the earlier tagged carrier are now `M::__pack_f`). Comparisons of
client-built maps with the machine's deposited values are extensional (`=~=`).

Earlier checked versions generated one of several field-shape-specific interfaces
by default, marked by `#[verified_field_tokens]`, with `#[verified_local_ready]`
selecting physical readiness on that route. Those interfaces were removed, and
`#[verified_field_tokens]` is rejected with a diagnostic. Clients written for
them (`InstanceInfo`, generated `*_collection` owners, empty-token bases) port to
the trusted macro's interface, i.e. back to their original form.

### Change 4: Check resource proof obligations

The generated resource proofs do not justify an `assume`, an admitted proof,
or an `external_body` in the client. Prove induction, domain, arithmetic, and
termination obligations. Use modern `proof fn`, tracked modes, and wrappers
where older examples use earlier Verus syntax.

## Changes to examples

This section covers user-written helpers, structures, invariants, and
executable methods. These changes are specific to the named clients.
They are not additional methods supplied by the TSM system.

### Change 5: Prove generic equality in Interner

The Interner example is [interner.rs](../../examples/state_machines/interner.rs).
It verifies unchanged with the checked macro (its trusted helper stays
`external_body`); the change below removes that assumption.

**Before — user helper:**

```rust
#[verifier::external_body]
fn compute_eq<T>(a: &T, b: &T) -> (res: bool)
    ensures res <==> (a == b),
{
    unimplemented!();
}
```

**After — user helper interface:**

```rust
pub trait VerifiedEq: Sized {
    fn compute_eq(&self, other: &Self) -> (res: bool)
        ensures res == (*self == *other);
}

fn compute_eq<T: VerifiedEq>(a: &T, b: &T) -> (res: bool)
    ensures res <==> (a == b),
{
    a.compute_eq(b)
}
```

**Use (retained):**

```rust
let eq = compute_eq(&val, &self.store[idx]);
```

The `T: VerifiedEq` bound requires a checked equality implementation.
The example provides one for `u64`. This requirement replaces the trusted stub.

`InternSystem<T>` has a persistent field; its persistent tokens own their
resources (Change 2), so the client's `self.frag.borrow().clone()` duplicates
one, and the client structures need no bound on `T`:

```rust
struct Interner<T> { inst: Tracked<InternSystem::Instance<T>>, /* .. */ }
```

### Change 6: Constrain the supplied Disk authority

The Disk example is [disk_example.rs](../../examples/state_machines/disk_example.rs).
`DiskInterp` is `AuthFrag::auth<nat, Block>` in both examples.

**Before — user function signature and body:**

```rust
spec fn state_interp_fn(
    inst: AuthFrag::Instance<nat, Block>, state: DiskSM::State,
) -> DiskInterp {
    AuthFrag![inst => auth => state.disk]
}
```

**After — user function signature and body:**

```rust
spec fn state_interp_fn(
    inst: AuthFrag::Instance<nat, Block>,
    interp: DiskInterp,
    state: DiskSM::State,
) -> bool {
    interp.instance_id() == inst.id() && interp.value() == state.disk
}
```

**Before — precondition of `take_step`:**

```rust
equal(interp1, state_interp_fn(inst, state1)),
```

**After — precondition of `take_step`:**

```rust
state_interp_fn(*inst, interp1, state1),
```

The old expression describes an authority token in a specification. The new
predicate constrains the actual authority passed to `take_step`. It does not
create ownership.

### Change 7: Update Rc and Arc invariants and overflow handling

#### Add an identity field for the invariant

[Rc](../../examples/state_machines/tutorial/rc.rs) and
[Arc](../../examples/state_machines/arc.rs) verify unchanged with the checked
macro. Without their assumed increment bound (`--no-cheating`), the checked
versions add an identity field for the invariant predicate. Rc has these fields:

**Before — fields in `MyRc`:**

```rust
pub inst: Tracked<RefCounter::Instance<MemPerms<S>>>,
```

**After — fields in `MyRc`:**

```rust
pub inst: Tracked<RefCounter::Instance<MemPerms<S>>>,
pub instance_id: Ghost<Loc>,
```

The checked invariant includes `self.instance_id@ == self.inst@.id()`.
The new field supplies identity to the invariant predicate. It cannot supply
a resource.

#### Handle overflow in the executable clone

The Rc example is [rc.rs](../../examples/state_machines/tutorial/rc.rs).

**Before — user method on `MyRc<S>`:**

```rust
fn clone(&self) -> (s: Self);
```

**After — user method on `MyRc<S>`:**

```rust
fn clone(&self) -> (s: Option<Self>);
```

**Before — use in `main`:**

```rust
let a5 = MyRc::new(Sequence::Cons(5, nil.clone()));
```

**After — use in `main`:**

```rust
let a5 = MyRc::new(Sequence::Cons(5, match nil.clone() {
    Some(rc) => rc,
    None => { return; },
}));
```

The checked method returns `None` at `u64::MAX`. It proves the increment bound
instead of assuming it. Arc uses the same failure policy. This change affects
the example's executable method. It does not change any token clone method.

### Check the complete client

Verify the client. Compile and run its executable example. Use `--no-cheating`
for an example that must contain no assumed proofs. Review existing trusted
specifications separately in a larger application.

Counting2, CountingN, RefCell, Rc, Arc, and Interner include executable uses.
An empty `main` or a tracked history checks proof code but does not run a
synchronization algorithm.

### Testing a client with both macros

A client that needs none of the changes in Change 2 can select the macro with a
cfg and be verified with both, as Verus's own state-machine examples are:

```rust
#[cfg(not(verus_verified_tsm))]
use verus_state_machines_macros::tokenized_state_machine;
#[cfg(verus_verified_tsm)]
use verus_state_machines_macros::verified_tokenized_state_machine as tokenized_state_machine;
```

Verify it once as usual and once with `--cfg verus_verified_tsm`. A client that
needs an interface change (for example the `Unit` argument) keeps its trusted
version and gets a separate checked version. The test conventions are described
in `source/rust_verify_test/README.md`.

### API changes at a glance

“Retained” means that the shown signature or call shape does not change.
Contracts and resource proofs can still change.

| Scope | API or use | Before | After and actual difference |
| --- | --- | --- | --- |
| System | Tokenized macro | `tokenized_state_machine!` trusts generated resource operations. | `verified_tokenized_state_machine!` proves them. Token types, `Instance` methods, signatures and specifications are retained. |
| System | Ordinary model macro | `state_machine!` generates mathematical states and relations. | `verified_state_machine_model!` checks the model with unannotated fields. It supplies no token or property API. |
| System | `Instance` and persistent tokens | `Copy`; `clone` promises equality. | Retained. |
| System | `vstd::tokens` traits | Trusted implementations. | Implemented with proofs, except `CountToken` for `count` tokens (inherent methods instead). |
| System | Operations without input tokens, storage machines | Take only `&self`. | Take an extra `Unit` (`Instance::unit_from_<field>`). |
| System | `imap`/`iset` token collections | `IMapToken`/`ISetToken`. | Generated `<field>_map`/`<field>_set` types with the same methods. |
| System | Type parameters | Unconstrained. | Unconstrained; a guard borrowing no token takes a `&Unit` in a machine with storage; persistent tokens (and an instance owning resources) are not `Copy`. |
| System | Raw resources and local readiness | Not available. | `#[verified_raw_tokens]`, optionally with `#[verified_local_ready(..)]`; storage values are maps `IMap<M::__StorageKey, M::__StorageValue>` tagged by storage field. |
| Example | Interner equality | An unrestricted generic helper has a trusted, unimplemented body. | The helper requires `T: VerifiedEq` and calls a checked provider. |
| Example | Disk interpretation | A two-argument spec function returns a described authority token. | A three-argument spec predicate returns `bool` and constrains a supplied authority token. |
| Example | Rc/Arc invariant identity | The invariant uses the original instance value. | An added `Ghost<Loc>` field supplies an identity parameter. |
| Example | Rc/Arc executable clone | Returns `Self` after an assumed increment bound. | Returns `Option<Self>`; `None` at `u64::MAX`. |
