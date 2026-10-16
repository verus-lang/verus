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
| Persistent duplication | Trusted clone and `Copy` where the generator permits them | Proof of idempotent duplication; receiver mode depends on the representation |
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

The checked dispatcher examines field kinds, transition syntax, and selected
readiness methods. It chooses an emitter for the supported combination. Some
emitters generate the complete resource model and field API together. Others
append a nominal field API to the generated protocol module.

Nominal field APIs are the default. `#[verified_raw_tokens]` selects the checked
aggregate resource API. `#[verified_field_tokens]` remains a compatibility
marker. Duplicate, conflicting, or argument-bearing selection markers produce
diagnostics. An unsupported nominal declaration does not silently select raw
tokens. [verified_field_tokens.rs](../state_machines_macros/src/verified_field_tokens.rs)
contains the API append operation and several field API routes.

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
implements [StorageMachine](../vstd/resource/tsm_storage.rs).

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
`StorageTokenOf<M, M::Key, M::Value, M::Fragment>`, whose declaration (like its
carrier `StorageCarrier`) has no trait bounds. A storage payload that contains
the machine's own tokens is then an ordinary datatype cycle, checked by Verus's
strict-positivity rule, rather than a cycle through the `StorageMachine` impl,
which Verus rejects outright. The dedicated owned-storage route
instead constructs its checked exclusive resource model in
[verified_storage_owned_imap.rs](../state_machines_macros/src/verified_storage_owned_imap.rs).
That route supports its full-state key expressions using actual owned storage.

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

Nominal wrappers restrict an actual fragment to a particular field role.
Private constructors and type invariants connect their getters and descriptors
to that resource. Entry wrappers distinguish one entry from a collection owner.
Split, join, removal, and insertion methods transform owned resources; they do
not obtain ownership from a map, count, or instance identifier in specification
code. Representative implementations are
[field roles](../state_machines_macros/src/verified_field_storage_roles.rs),
[IMap roles](../state_machines_macros/src/verified_field_storage_imap_roles.rs),
and [collections](../state_machines_macros/src/verified_field_storage_collections.rs).

Physical storage belongs to the storage resource rather than an ordinary
logical field token. Deposits consume tracked payloads. Withdrawals return
tracked payloads from the same exchange witness. Guards borrow actual stored
payloads, and their references retain the required owner lifetime.

Multiple physical fields can require a field-tagged key/value carrier.
[verified_storage_carrier.rs](../state_machines_macros/src/verified_storage_carrier.rs)
and [verified_storage_homogeneous_carrier.rs](../state_machines_macros/src/verified_storage_homogeneous_carrier.rs)
implement the supported layouts and checked packing and extraction.
Carrier tags distinguish field namespaces. They do not replace custody of the
payloads. Finite-map conversions must also prove the required domain and payload
equalities before tracked extraction.

## Instances, metadata, and duplication

The original generator treats an instance as a cloneable, copyable protocol
handle. Its trusted clone promises complete value equality. Checked instance
representations retain tracked ownership or a checked initialization witness.
Their clone methods generally promise identifier and constant agreement,
without promising equality of the complete representation.

Some routes expose a ghost `InstanceInfo` containing an identifier and constants.
It is a description, not a token owner. Methods that change resources still
require the corresponding tracked owners. The
[mixed-storage field API](../state_machines_macros/src/verified_field_storage_wide.rs)
shows this separation and its initialization facts.

The record lets ghost tickets compare identifiers and constants without
cloning an operational instance. Its equality compares metadata rather than
the opaque instance representation. This is an API convenience, not a logical
necessity: ghost instance snapshots could instead compare the same getters.
`InstanceInfo` is generated only by the routes that provide this interface.

Persistent logical ownership can be duplicated when its component is
idempotent. Some wrappers use a shared tracked receiver. Others split and
restore an actual token slot through a mutable tracked receiver.
The lack of `Copy`, or the need for a mutable receiver, is a representation and
API constraint of these implementations. It is not a claim that persistent
ownership is logically impossible to duplicate. Ordinary exclusive owners and
physical permissions do not acquire persistence from a clone method.

## Local readiness and state observations

`#[verified_local_ready(...)]` adds methods such as `change_local_ready`,
`change_local`, and `change_observed`. The implementation is in
[verified_readiness.rs](../state_machines_macros/src/verified_readiness.rs).
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

Backend support is combination-dependent. Specialized routes cover more
syntax than the basic straight-line emitter. A supported field kind does not
mean that every combination of fields, binders, storage operands, and selected
readiness methods is supported. For example, the general resource emitter
currently rejects labeled machines, although the pure model entrypoint has
checked label classifiers. Selection checks also reject some combinations of
unowned observations and physical readiness.

Unsupported shapes and generated-name conflicts produce diagnostics. These
limits are implementation constraints, not proofs that the requested protocol
cannot exist. Shared signatures also do not imply that every legacy token trait
is implemented by a checked wrapper. Tests must check the selected full model,
its ownership errors, and its client. Proof histories are erased; executable
coverage requires running the existing synchronization algorithm separately.
