# Tokenized state machine implementation comparison

This chapter compares `tokenized_state_machine!` with
`verified_tokenized_state_machine!`. It describes their generated code and proof
boundaries. For caller changes, see the [migration chapter](migration-tsm.md).

The original macro is not wholly unverified. It checks user induction hooks and
generated transition safety proofs. Its **resource implementation is trusted**:
generated token operations have contracts and `external_body` implementations.
The checked macro replaces that implementation with proofs over the resource
and storage libraries. Those libraries still contain trusted primitives.

| Component | Original macro | Checked macro |
| --- | --- | --- |
| Frontend | Shared machine parser, transition checks, and induction-hook checks | Reuses the frontend; adds interface selection and backend checks |
| State semantics | Generated weak and strong relations, enabling predicates, and invariants | Retains mathematical relations; proves safety, execution, and frame obligations |
| Tokens | Generated proof objects and trusted token-trait implementations | Tracked owners backed by PCM or storage resources |
| Exchange | Trusted method promises the declared token effects | Method proves an update or storage exchange that preserves compatible frames |
| Storage guard | Trusted contract returns a borrowed permission | Checked guard condition is passed to the existing storage primitive |
| Persistent duplication | Trusted clone and `Copy` where the generator permits them | `Copy` tokens holding a shared reference to an idempotent resource |
| Execution | Client supplies the synchronization algorithm | Client still supplies the algorithm; generated protocol operations are proof code |

## Frontend and code generation

Both entrypoints are in [lib.rs](../state_machines_macros/src/lib.rs). The
original entrypoint calls `construct_state_machine(input, true)`, which parses
`ParseResult`, converts it to the machine IR, checks induction hooks, and calls
`output_token_stream`.

The checked entrypoint also parses `ParseResult`. It calls
[verified_readiness.rs](../state_machines_macros/src/verified_readiness.rs),
which consumes the checked interface attributes before the shared conversion.
The common frontend includes [parse_token_stream.rs](../state_machines_macros/src/parse_token_stream.rs),
[parse_transition.rs](../state_machines_macros/src/parse_transition.rs),
[token_transition_checks.rs](../state_machines_macros/src/token_transition_checks.rs),
and [lemmas.rs](../state_machines_macros/src/lemmas.rs).

The checked dispatcher selects one of two interfaces. By default (or with
`#[verified_generic_tokens]`) it generates the raw protocol with the general
emitter and appends the generic field-token interface of
[verified_generic_tokens.rs](../state_machines_macros/src/verified_generic_tokens.rs):
the trusted macro's token types and `Instance` methods, with proofs. With
`#[verified_raw_tokens]` it generates only the raw protocol, using the
straight-line emitter where it applies and the general emitter otherwise, plus
the operations selected by `#[verified_local_ready(..)]` (on the default
interface that attribute is accepted and only its names are checked). Duplicate,
conflicting, or argument-bearing markers produce diagnostics, as does the removed
`#[verified_field_tokens]`. A
declaration that the generic interface does not support is rejected; the macro
does not silently select raw tokens. (Earlier versions selected one of several
field-shape-specific interfaces by default; those were removed.)

`verified_state_machine_model!` is a separate mathematical-model entrypoint.
[verified_model.rs](../state_machines_macros/src/verified_model.rs) generates
states, relations, classifiers, and checked mathematical constructors. It does
not allocate token resources or generate property methods.

## Original resource implementation

[concurrency_tokens.rs](../state_machines_macros/src/concurrency_tokens.rs)
generates `Instance`, per-field token structs, collection aliases, and exchange
methods. It selects arguments from field reads, writes, and special operations.
For example, a written variable becomes a mutable tracked token argument;
a removal consumes a token; an addition returns a token.

The generator gives these methods preconditions and postconditions, then marks
the resource bodies `external_body`. The implementations do not derive the
resource transformation from an underlying owned resource. The generator also
provides trusted implementations of the interfaces in
[tokens.rs](../vstd/tokens.rs), including value agreement, uniqueness, counts,
and element membership.

That trust boundary is separate from the mathematical proofs.
[to_token_stream.rs](../state_machines_macros/src/to_token_stream.rs) emits
relations and induction obligations.
[safety_conditions.rs](../state_machines_macros/src/safety_conditions.rs)
constructs safety proofs from transition syntax. Source assertion proof blocks
can contribute to those proofs; their assumptions remain part of the client's
trust boundary.

## Checked resource model

The principal emitters are
[verified_tokens.rs](../state_machines_macros/src/verified_tokens.rs) and
[verified_general.rs](../state_machines_macros/src/verified_general.rs).
They generate a mathematical `State`, a resource-algebra `Fragment`, and a
`Protocol` with an embedding of complete states into fragments.

`Fragment` combines field components. Its resource-algebra and PCM methods prove
associativity, commutativity, unit laws, and component validity obligations.
`Protocol` implements the existing
[Machine interface](../vstd/resource/tsm.rs). A stored-resource protocol also
implements [StorageMachine](../vstd/resource/tsm_storage.rs), whose storage is
one `IMap<__StorageKey, __StorageValue>` tagged by storage field (see below).

The library defines completion by an invariant-satisfying state:

```text
invariant(state) && op(fragment, frame) == embed(state)
```

A fragment can describe partial ownership. It need not determine one complete
state. The `Inved` construction in the machine library uses completion to define
the validity of the owned machine resource. This is stronger than treating a
public specification descriptor as an ownership certificate.

The generated `Token` alias refers to the library's `Token<Protocol>` or
`StorageToken<Protocol>` for these routes. `StorageToken<M>` is an alias for
`StorageTokenOf<M, M::Key, M::Value, M::Fragment>`, which holds a
`StorageResource<M::Key, M::Value, StorageCarrier<M, M::Fragment>>`; its
declaration (like the carrier `StorageCarrier`) has no trait bounds, and the key
and value types are the concrete generated enums. A storage payload that
contains the machine's own tokens is then an ordinary datatype cycle through
`__StorageValue`, checked by Verus's strict-positivity rule, rather than a cycle
through the `StorageMachine` impl, which Verus rejects outright.

## Relations, safety, induction, and updates

The shared [simplifier](../state_machines_macros/src/simplification.rs) and
[relation generator](../state_machines_macros/src/to_relation.rs) define the
mathematical transition semantics. Weak relations do not include every asserted
safety condition. Strong relations do. A weak relation therefore does not
automatically imply its strong counterpart.

[verified_state_relations.rs](../state_machines_macros/src/verified_state_relations.rs)
retains the original weak relations alongside checked protocol definitions.
Checked emitters also generate safety and execution proofs. User induction
hooks establish invariant preservation under the required transition relation.
The protocol proofs then connect those state facts to actual resource effects.

A resource transition must preserve every compatible frame. For an owned
fragment and an explicitly borrowed fragment, compatibility has the form:

```text
invariant(pre) && op(op(owned, shared), frame) == embed(pre)
```

Generated readiness conditions quantify over these completions. Generated
update proofs establish an invariant-satisfying successor with the same frame.
Storage exchange proofs additionally account for the exact deposit and
withdrawal. Their implementation uses checked frame-update and frame-exchange
theorems in [tsm.rs](../vstd/resource/tsm.rs) and
[tsm_storage.rs](../vstd/resource/tsm_storage.rs).

The checked mathematical `take_step` implementation is in
[verified_take_step.rs](../state_machines_macros/src/verified_take_step.rs).
It requires strong enabling, and the pre-state invariant where its result
promises invariant preservation. It does not generate a weak-to-strong theorem
or use a source assertion proof override to obtain resource authority.

## Field resources and storage custody

[verified_monoids.rs](../state_machines_macros/src/verified_monoids.rs) maps
logical field strategies to resource components. Variables use exclusive
values; constants use agreement. Counts, Boolean fields, collections, and
persistent fields use their corresponding checked algebras and ownership
effects. The supporting implementations include
[count and machine resources](../vstd/resource/tsm.rs),
[collections](../vstd/resource/tsm_collections.rs), and
[persistent resources](../vstd/resource/tsm_persistent.rs).

A generic field token owns exactly the fragment of one field element. Its type
invariant ties its ghost data (key, value, element or count) to the raw token it
holds, or marks it as a placeholder with an instance identifier that no real
instance has. Collection types of the infinite strategies hold one raw token for a
possibly infinite part plus finitely many individual tokens. Operations join the
input tokens' fragments, prove the raw precondition from the trusted-style one,
call the raw operation, and split the output fragment into the promised tokens; no
operation obtains ownership from a map, count or instance identifier in
specification code. The representation and proofs are described in
[Checked tokens: raw and generic interfaces](state_machines/src/checked-token-interfaces.md).

Physical storage belongs to the storage resource rather than an ordinary
logical field token. Deposits consume tracked payloads. Withdrawals return
tracked payloads from the same exchange witness. Guards borrow actual stored
payloads, and their references retain the required owner lifetime.

The stored resources are one map of vstd's storage protocol,
`IMap<__StorageKey, __StorageValue>`, for every machine with storage fields
([verified_storage_tagged.rs](../state_machines_macros/src/verified_storage_tagged.rs)):
a storage field `f`'s entry at `k` is stored under the key `__StorageKey::f(k)`
(`__StorageKey::f` for a `storage_option` field) as `__StorageValue::f(v)`. The
generated per-field helpers convert a field's value to its tagged part and back
(`__tag_f`/`__untag_f`, and the checked tracked conversions `__pack_f`,
`__unpack_f`, `__borrow_f`, `__unwrap_f`). Tags distinguish field namespaces;
they do not replace custody of the payloads. Tracked conversions move entries
one by one, so a general operand of a `storage_imap` field (deposit, withdrawal,
guard, initial value) needs a finite domain, which the machine states with a
`require`.

## Instances, metadata, and duplication

Both generators treat an instance as a copyable handle, and both `clone`
methods promise `out == *self`. The original instance is a trusted token. The
generic interface's `Instance` is not a resource: it holds the protocol location
and, where needed, `&'static` references to leaked shared resources (a unit token,
or a descriptor of the constants), so copying it duplicates no ownership. Its
`id()` is a function of the location. Operations that change resources take the
field tokens that own the affected fragments; an operation without such a token
in a machine with storage takes a `Unit` token of the instance. In a machine with
type parameters, a leaked reference would need the parameters to be `'static`:
there the instance owns duplicable copies of these resources where it needs
them (a descriptor whose type mentions a parameter; a unit token without
storage), is not `Copy`, and its `clone` promises equal identifiers and
constants. A storage token cannot be duplicated, so with storage a guard that
borrows no token borrows a `Unit` instead of an instance-held token.

Persistent tokens hold a leaked `&'static` raw token whose fragment is
idempotent. They are `Copy`, and their `clone` promises equality, as in the
trusted macro. In a machine with type parameters they own their raw token
instead and `clone` duplicates it (with `&mut self` if the machine has storage:
storage-protocol resources only split). Ordinary exclusive owners and physical
permissions are not `Copy` and have no clone method.

## Local readiness and state observations

`#[verified_local_ready(...)]`, with `#[verified_raw_tokens]`, adds raw
operations such as `change_local_ready`, `change_local`, and `change_observed`.
The implementation is in
[verified_readiness.rs](../state_machines_macros/src/verified_readiness.rs).
The generic interface needs no such selection: its preconditions are already
stated over the supplied tokens, and its generated proofs derive the raw
precondition for every completion. There the attribute is accepted, its names
are checked, and it has no further effect.
A local requirement can use facts visible in supplied fragments. Its generated
proof must establish readiness for **every** compatible invariant-satisfying
completion, including the ownership and deposit conditions.

An observed transition returns the resulting owned token, withdrawn storage,
and ghost `before`, `after`, and `frame` values. The proof connects all of these
to the same actual exchange. The states describe a compatible completion.
They do not reveal a unique hidden history. Observations and metadata cannot
construct physical permissions. Borrowed observations also cannot replace an
owner required by a mutating operation.

## Trust boundary and current limits

The checked macro adds no axioms or executable locks. It reuses the existing
[PCM resource primitives](../vstd/resource/pcm.rs) and
[storage protocol primitives](../vstd/resource/storage_protocol.rs), which
include axiomatic allocation, splitting, updating, validation, and borrowing.
Checked machine-library theorems connect generated obligations to these
primitives. This implementation is not an axiom-free proof of the whole system.
Client assumptions, trusted specifications, and verifier trust remain separate.

Backend support is combination-dependent. The general emitter covers more
syntax than the basic straight-line emitter, and the generic interface supports
a subset of the general emitter's forms (its limits are listed in
[Checked tokens: raw and generic interfaces](state_machines/src/checked-token-interfaces.md)).
A supported field kind does not mean that every combination of fields, binders,
storage operands, and selected readiness methods is supported.

The raw interface (`#[verified_raw_tokens]`, and the generic interface built on
it) uses the general emitter for every machine the straight-line emitter does
not support, including labeled machines. Each field's monoid statements on a
path, any number of `remove`, `have` and `add` in the trusted order, form one
update: the composed removal followed by the composed addition. Each path's
storage statements, any number of deposits, withdrawals and guards, form one
storage exchange or guard. That exchange requires its deposit to be disjoint
from the pre-state storage, so a deposit into a location withdrawn earlier on
the same path is not supported: syntactically equal locations are rejected,
other overlaps fail in the generated proof. A stored-value binding cannot
observe a value deposited earlier on its path. Withdrawal keys are evaluated
in the full pre-state, so they may read fields the operation does not own
(including the stored map) or use `pre` as a whole; deposit and guard keys must
be local observations. A guard may guard a value bound by `have` on an exclusive
`map`/`imap` entry or on an `option` or `persistent_option` field
(`have o >= Some(let x)`): the bound value is read from the borrowed fragment. The corpus `examples/verified_tsm/raw_forms_*.rs`
exercises these forms.

Unsupported shapes and generated-name conflicts produce diagnostics. These
limits are implementation constraints, not proofs that the requested protocol
cannot exist. Shared signatures also do not imply that every legacy token trait
is implemented by a checked wrapper. Tests must check the selected full model,
its ownership errors, and its client. Proof histories are erased; executable
coverage requires running the existing synchronization algorithm separately.
