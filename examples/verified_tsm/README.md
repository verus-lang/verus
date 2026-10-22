# Tests of the checked state-machine macros

`verified_tokenized_state_machine!` and `verified_state_machine_model!` are also tested by
every test of `source/rust_verify_test/tests/state_machines.rs` and every trusted example
that selects its macro by `cfg(verus_verified_tsm)` (see `source/rust_verify_test/README.md`).
This directory only holds what those dual-run tests cannot cover: soundness negatives that the
trusted macro does not catch, features and limitations that exist only in the checked macros
(the raw interface and its local-ready API, the generic interface's differences from the
trusted one, see `source/docs/state_machines/src/checked-token-interfaces.md`), and regression
tests for bugs of the checked macros (the header names the fixing commit).

All files are registered in `source/rust_verify_test/tests/examples.rs` and run with
`--no-cheating`; `negative/` files state their expected error with `// EXPECTED-ERROR: <text>`.
A file that selects its macro by `cfg(verus_verified_tsm)` also runs with the trusted macro
(without `--no-cheating`, whose generated code it rejects).
Add a file only if it covers something not covered here or by the dual-run tests, and list it
below with the reason.

## Soundness negatives the trusted macro accepts

* `negative/field_tokens_not_send.rs`: a `variable` token of a machine over a `!Send` type is
  `!Send` (trusted tokens are unconditionally `Send`).
* `negative/field_tokens_count_not_send.rs`: the same for a `count` token (its type mentions
  the parameter only through a constant).
* `negative/generic_tokens_multiset_repeated_borrow.rs`: a borrowed multiset part that may
  repeat an element is rejected (shared references do not show distinct resources).
* `negative/negative_take_step_raw_temporary.rs`: raw identifiers `update_tmp_*` are reserved
  in checked models.
* `negative/negative_take_step_weak_to_strong.rs`: checked `take_step` needs the strong
  relation; the weak one does not suffice.
* `negative/test_double_scoped_updates_if_missing_strong.rs`: the same for nested scoped
  updates in `if` (variant of the trusted `double_scoped_updates_if`).
* `negative/test_if_let_assert_with_no_else_missing_strong.rs`: the same for `if let` with an
  `assert` and no `else` (variant of the trusted `if_let_assert_with_no_else`).

## Type cycles through storage (regression 5ee61140d)

* `stored_own_tokens.rs`: storage payloads that contain the machine's own tokens (raw and
  generic interfaces) are accepted.
* `negative/stored_own_tokens_negative_fn.rs`: a token in a `spec_fn` argument (negative
  position) is rejected by strict positivity.
* `negative/stored_own_tokens_negative_ghost.rs`: the same under `Ghost`.
* `negative/stored_own_tokens_negative_trait.rs`: the same hidden behind a trait projection.
* `negative/stored_own_tokens_negative_raw.rs`: the same for the raw protocol token.
* `negative/stored_own_tokens_negative_imap_key.rs`: a raw token as an `IMap` key.

## The raw interface (`#[verified_raw_tokens]`)

* `raw_forms_statements.rs`: remove/have/add sequences on every monoid kind, labels, routing
  to the general emitter, and the same sequences through the generic interface.
* `raw_forms_control.rs`: `let`, `require let`, `assert let`, `match`, `if`, `birds_eye`,
  `readonly!` and `property!` around token and storage operations.
* `raw_forms_storage_option.rs`: deposits, withdrawals and guards of several `storage_option`
  fields, of one and of different payload types (tagged storage).
* `raw_forms_storage_map.rs`: several deposits, withdrawals and guards of one `storage_map`
  on one path, and general-form deposits.
* `raw_forms_storage_many_fields.rs`: nine storage fields in one tagged map (regression
  df5c0980d, storage reasoning that scales with the number of fields).
* `tagged_storage_api.rs`: the tagged-storage helpers raw clients call (`__pack_f`,
  `__tag_f`/`__untag_f`, `__borrow_f`, `__unpack_f`).
* `raw_forms_sub_updates.rs`: field and index sub-updates (regression c2fa710ed).
* `raw_forms_map_mixed_have_guard.rs`: a guard after several haves of one map field
  (regression 4e0ca49ec).
* `raw_forms_persistent_bound_guard.rs`: a guard of a value bound by `have` on a
  `persistent_option` field (regression b00705e0d).
* `negative/shared_consumption.rs`: a borrowed (shared) token cannot be consumed.
* `negative/sequential_unowned_read.rs`: a read needs an owned or borrowed observation.
* `negative/storage_map_wrong_deposit.rs`: the tracked deposit must match the protocol's
  key and value.
* `negative/tagged_storage_wrong_key.rs`: `__borrow_f` of a key that is not in the tagged
  map is rejected (counterpart of `tagged_storage_api.rs`).
* `negative/tagged_storage_non_send.rs`: a tagged storage token is `Send` only if every
  payload type is.
* `negative/storage_birds_guard.rs`: diagnostic: a guard value must be a deterministic
  function of the local inputs.

## Local readiness

Every raw transition, readonly transition and property gets its local-ready API
(`M::local_ready::t`) unless its form is one the macro skips (see
`checked-token-interfaces.md`); the tests of `state_machines.rs` named `*local_ready*` cover the
forms and the skipped ones.

* `raw_forms_local_ready.rs`: local-ready transitions with two deposits, a withdrawal followed
  by a deposit, and an index update.

## Interface selection

* `negative/default_tokens_conflict_raw_then_generic.rs`: the raw and generic attributes
  cannot be combined.
* `negative/default_tokens_removed_field_tokens.rs`: the removed `#[verified_field_tokens]`
  gets a diagnostic.
* `negative/default_tokens_removed_local_ready.rs`: the removed `#[verified_local_ready(..)]`
  gets a diagnostic.

## The generic (default) interface

* `generic_tokens_kinds.rs`: every sharding strategy group with a client of the trusted-style
  API, `arbitrary()` placeholders, constants read through the descriptor, an operation that
  consumes no token, and labeled machines.
* `generic_tokens_counts.rs`: `count` tokens with inherent `CountToken` operations (the trait
  is not implemented), `persistent_count`, `bool` and `persistent_bool`.
* `generic_tokens_imap.rs`: reservation-style collection types of `imap`/`iset` fields
  (`M::field_map`, not `IMapToken`), infinite initial collections, conversions.
* `generic_tokens_constant_infinite_collections.rs`: constants read with only `imap`/`iset`
  collections borrowed (regression de92adf43).
* `generic_tokens_borrowed_collections.rs`: borrowed token collections of the finite
  strategies and of a `multiset` field.
* `generic_tokens_persistent_generic.rs`: persistent tokens and constants of machines with
  type parameters own their resources: not `Copy`, `clone` (`&mut self` with storage), no
  `'static` bound.
* `generic_tokens_storage_only.rs`: `Unit` sources (`<init>_with_unit`, `unit_from_<field>`,
  `Unit::split`) for operations that consume no token.
* `generic_tokens_guard_unit.rs`: token-less guards of generic storage machines take a
  `&Unit` (regression 07152b9dd, they needed `'static` type parameters).
* `generic_tokens_general_guards.rs`: guards of general operands return references into the
  storage (`&V`, `Option<&V>`, `Map<K, &V>`), guards with several outputs.
* `generic_tokens_general_map_guards.rs`: general map guards with other storage fields or
  guards (regression 22cd41783).
* `generic_tokens_not_tokenized.rs`: `not_tokenized` fields read through `birds_eye`, and
  constants, with the trusted semantics.
* `generic_tokens_map_mixed_have_guard.rs`: a guard after several haves of one map field
  (regression 4e0ca49ec).
* `generic_tokens_withdraw_keys.rs`: withdrawal keys over the full pre-state (regression
  bdef221a1).

## Storage layout and finiteness

* `generic_tokens_tagged_many_fields.rs`: ten storage fields in the tagged map (regression
  df5c0980d, storage reasoning that scales with the number of fields).
* `generic_tokens_homogeneous_storage.rs`: storage fields of one payload type use the
  homogeneous carrier (65bf3b660).
* `generic_tokens_tagged_imap_withdraw.rs`: general withdrawals from a tagged `storage_imap`
  with a finite operand (regression fd3d08f2f).
* `negative/generic_tokens_imap_infinite_operands.rs`: diagnostic for a general
  `storage_imap` withdrawal or initial value without a finite domain.
* `negative/generic_tokens_imap_guard_infinite.rs`: diagnostic for a general `storage_imap`
  guard without a finite domain.

## Replacing a stored value

* `storage_replace_in_two_transitions.rs`: the workaround the checked macro's diagnostic for a
  deposit into a location withdrawn earlier in the same transition points to: the replace as
  two transitions with the intermediate state explicit, and clients that replace by calling
  both, for a `storage_option` field and a `storage_map` key (also run with the trusted macro).
* `negative/storage_replace_same_location.rs`: diagnostic for a syntactically identical
  location (the `storage_option` cell), at the deposit.
* `negative/storage_replace_key_written_differently.rs`: the same overlap with keys written
  differently fails in the storage proof, reported at the deposit with the same hint.

## Hygiene

* `hygiene_name_capture.rs`: user identifiers named like generated `__tsm_*` helpers, in the
  model, the generic interface and nondeterministic tokenizing (one representative each).

## The statement calculus (`vstd::resource::tsm_calculus`)

* `tsm_calculus.rs`: the calculus's step lemmas used by hand on two raw machines covering every
  monoid kind, a variable and a constant: the per-machine configuration split and join, and,
  from the generated ownership condition, chains to the frontend's enabling condition, its
  strong relation and the output configuration; each step lemma occurs in one chain. The
  machines' generated local readiness uses the same chains.
