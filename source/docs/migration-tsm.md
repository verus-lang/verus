# Tokenized state machines upgrade

Use `verified_tokenized_state_machine!` to generate resource definitions and
protocol proofs that Verus checks. The proofs use the existing PCM and storage
protocol libraries. The macro adds no axioms and no executable locks.
`tokenized_state_machine!` remains available.

Keep the machine fields, transitions, invariants, and executable algorithm.
Keep field token names such as `X::inc_a`. Change resource ownership and proof
code where this chapter shows a difference.

Each section gives signatures and uses from existing examples. The signatures
omit bodies, visibility, attributes, and contracts unless a contract changes.
They use current Verus mode syntax. Internal parameter names and lifetime names
are normalized. `Self` means the type that contains the method. A signature
block is a comparison, not a complete program.

“Before” means the original VerusSync example. “After” means the current
checked example. This chapter does not describe upgrades between checked
implementation versions. A retained signature is marked explicitly. Technical names, identifiers, and Rust keywords
keep their source spelling.

The first section describes changes to generated TSM APIs and proofs.
The second section describes changes to example and application code.
A machine name in an API example belongs to that example, not to the TSM library.
For implementation details, see the
[implementation comparison](tsm-implementation-comparison.md).

## Changes to the TSM system itself

This section covers macro entrypoints, generated resource APIs, and proof
contracts. Before/after example calls show the effect of each system change.

### Change 1: Generate checked proofs

Replace the macro import and invocation. The machine declaration uses the same
`fields`, `init!`, `transition!`, `property!`, and sharding syntax.

The example is Counting2:
[before](../../examples/state_machines/tutorial/counting_to_2.rs) and
[after](../../examples/verified_tsm/counting_to_2.rs).

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

**Before — generated signatures in `X::Instance`:**

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

**After — generated signatures in `X::Instance` (retained):**

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

**Before — use:**

```rust
globals.instance.borrow().tr_inc_a(&mut c, &mut token);
```

**After — use (retained):**

```rust
globals.instance.borrow().tr_inc_a(&mut c, &mut token);
```

The old macro trusts generated resource operations. The new macro proves them.
The new macro generates field token types by default. An unsupported field
combination gives a diagnostic. It does not select a raw interface silently.

For a mathematical model with no token or property client, use
`verified_state_machine_model!`. The ordinary
[Adder before](../../examples/state_machines/adder.rs) and
[Adder after](../../examples/verified_tsm/adder.rs) use unannotated fields.
Their generated state relation signatures are retained:

```rust
// Before: state_machine! — methods on X::State.
spec fn initialize(post: Self) -> bool;
spec fn add(pre: Self, post: Self, n: int) -> bool;

// After: verified_state_machine_model! — methods on X::State.
spec fn initialize(post: Self) -> bool;
spec fn add(pre: Self, post: Self, n: int) -> bool;
```

The declaration changes from `state_machine!(X { ... })` to
`verified_state_machine_model!(X { ... })`. This entrypoint generates states
and relations. It does not generate token or property methods. A model that
uses those methods needs the checked tokenized macro and sharding annotations.

### Change 2: Keep an owned instance for resource operations

A checked instance contains an owned resource. Its specification value does not give
ownership. A clone proves agreement about identity and constants. It does not
promise equality of the complete instance values.

CountingN shows the difference:
[before](../../examples/state_machines/tutorial/counting_to_n.rs) and
[after](../../examples/verified_tsm/counting_to_n.rs).

**Before — generated signatures and traits for `X::Instance`:**

```rust
// Instance has Copy and Clone implementations.
spec fn id(&self) -> vstd::tokens::InstanceId;
proof fn clone(tracked &self) -> (tracked out: Self)
    ensures out == *self;
```

**After — generated signatures for `X::Instance`:**

```rust
// Instance has no Copy implementation.
spec fn id(&self) -> vstd::resource::Loc;
proof fn clone(tracked &self) -> (tracked out: Self)
    ensures out.id() == self.id(),
            out.num_threads() == self.num_threads();
```

`vstd::tokens::InstanceId` is an alias for `vstd::resource::Loc` in this tree.
The public type spelling changes. The underlying identifier type does not.

**Before — CountingN invariant:**

```rust
(*global_arc).instance@ == instance,
```

**After — CountingN invariant:**

```rust
(*global_arc).instance@.id() == instance.id(),
```

Both examples already store `Tracked<X::Instance>`. Both explicitly call
`instance.clone()` when they create the atomic invariant. Keep that pattern.
A ghost record cannot replace the tracked receiver of a resource operation.

#### Generate a separate metadata type

`SingleThreadedMachine` generates `InstanceInfo<Result, Tix>` for metadata.
It contains the location and all machine constants. It has no resource methods.
This is an external application model, not a TSM library type.
The complete example is
[single_threaded_proofs.rs](../../../AwsArgLlcrtNice/theories/verus/concurrency/src/single_threaded_proofs.rs).
Its original source is in `AwsArgLlcrtNice` commit `acd267f0`.

**Before — generated metadata methods on `Instance<Result, Tix>`:**

```rust
spec fn id(&self) -> vstd::tokens::InstanceId;
spec fn max_threads(&self) -> nat;
```

**After — generated metadata methods:**

```rust
// On Instance<Result, Tix>:
spec fn info(&self) -> InstanceInfo<Result, Tix>;

// On InstanceInfo<Result, Tix>:
spec fn id(&self) -> vstd::resource::Loc;
spec fn max_threads(&self) -> nat;
```

Keep the tracked instance for resource operations. `InstanceInfo` supplies
identity and constants for specifications. Not every machine exports this type.

### Change 3: Clone persistent tokens and supply a basis for empty tokens

The signatures below are generated for the external application model
`SingleThreadedMachine` from Change 2. It is not a TSM library type.
These differences do not apply to all persistent token types.

#### Clone `SingleThreadedMachine::entered`

**Before — generated type interface:**

```rust
// entered<Result, Tix> implements Copy and Clone.
proof fn clone(tracked &self) -> (tracked out: Self)
    ensures out == *self;
```

**After — generated method on `entered<Result, Tix>`:**

```rust
// entered<Result, Tix> does not implement Copy.
proof fn clone(tracked &mut self) -> (tracked out: Self);
```

The checked method moves the owned token out of the receiver and splits it.
It puts one token back and returns the other. These internal changes require
a mutable borrow. The receiver keeps its instance identifier, fragment, and
field value. Other backends can prove duplication through a shared borrow.

**Before — bindings and ticket field in `complete`:**

```rust
Tracked(entered),
// Later, in the leader ticket:
entered: entered,
```

**After — bindings and ticket field in `complete`:**

```rust
Tracked(mut entered),
// Later, in the leader ticket:
entered: entered.clone(),
```

The original example copies `entered` into multiple tickets. The checked
example calls a proof method on the owned token. Some other generated clone
methods use `tracked &self`. Keep the receiver mode that your machine generates.
Ordinary tokens and physical permissions cannot be copied this way.

#### Prove that two `SingleThreadedMachine::stage` owners cannot share an instance

**Before — `vstd::tokens::UniqueValueToken` method used by `stage`:**

```rust
proof fn unique(tracked &mut self, tracked other: &Self)
    ensures final(self).instance_id() != other.instance_id(),
            *final(self) == *old(self);
```

**After — inherent method on `stage<Result, Tix>`:**

```rust
proof fn unique(tracked &mut self, tracked other: &Self)
    requires old(self).instance_id() == other.instance_id(),
    ensures false;
```

The receiver was already mutable. The contract changes. The checked method
requires equal instance ids and proves a contradiction. Its proof returns the
receiver's resource before it proves the contradiction.

**Before — use in `entry_has_unique_leader`:**

```rust
let tracked mut stage1 = tix.m.tracked_remove(i).pre_ticket.stage.tracked_unwrap();
stage1.unique(&tix.m.tracked_borrow(j).pre_ticket.stage.tracked_borrow());
```

**After — use (retained):**

```rust
let tracked mut stage1 = tix.m.tracked_remove(i).pre_ticket.stage.tracked_unwrap();
stage1.unique(&tix.m.tracked_borrow(j).pre_ticket.stage.tracked_borrow());
```

The ticket invariant supplies the equal-id precondition. The checked field
methods do not implement all legacy `vstd::tokens` traits. A generic adapter
must require an interface that the checked type implements.

#### Create empty entering tokens from an owned basis

A basis is an owned token from the same instance. The operation borrows it
mutably and preserves its field value and instance id.

**Before — generated method on `Instance<Result, Tix>`:**

```rust
proof fn generate_empty_entering_token(tracked &self) -> (tracked out: (
    Tracked<may_cancel_entry<Result, Tix>>,
    Tracked<may_cancel_result<Result, Tix>>,
    Tracked<may_cancel_exit<Result, Tix>>,
    Tracked<entering<Result, Tix>>,
));
```

**After — generated method on `Instance<Result, Tix>`:**

```rust
proof fn generate_empty_entering_token(
    tracked &self,
    tracked stage: &mut stage<Result, Tix>,
) -> (tracked out: (
    Tracked<may_cancel_entry<Result, Tix>>,
    Tracked<may_cancel_result<Result, Tix>>,
    Tracked<may_cancel_exit<Result, Tix>>,
    Tracked<entering<Result, Tix>>,
));
```

**Before — use in `complete`:**

```rust
let tracked mut t = self.instance.borrow().generate_empty_entering_token();
```

**After — use in `complete`:**

```rust
let tracked mut t = self.instance.borrow().generate_empty_entering_token(&mut stage);
```

The return tuple keeps its original order. The generated alternative
`generate_empty_entering_token_with_basis_entering` takes
`tracked &mut entering<Result, Tix>` instead of the stage argument.
`entry_has_unique_leader` uses that alternative and restores its basis to the
ticket record. An instance id alone cannot supply the basis.

Count token operations in CountingN retain these signatures:

```rust
// Before and after, on X::unstamped_tickets:
proof fn split(tracked &mut self, count: nat) -> (tracked out: Self);
proof fn join(tracked &mut self, tracked other: Self);
```

Both examples use `unstamped_tokens.split(1 as nat)`. The split requires a
sufficient owned count. A join requires equal instance ids.

### Change 4: Keep actual storage owners and borrow guards

Storage operations use actual tracked permissions. A specification map or
option cannot replace those permissions. The RefCell example keeps its
initializer and deposit arguments:
[before](../../examples/state_machines/tutorial/ref_cell.rs) and
[after](../../examples/verified_tsm/ref_cell.rs).

#### Use the generated collection owner

**Before — generated method on `RefCounter::Instance<S>`:**

```rust
proof fn initialize_empty(
    pcell_loc: CellId,
    tracked storage: Option<Perm<S>>,
) -> (tracked out: (
    Tracked<Self>, Tracked<flag<S>>,
    Tracked<reader_multiset<S>>, Tracked<Option<writer<S>>>,
));
```

**After — generated method on `RefCounter::Instance<S>`:**

```rust
proof fn initialize_empty(
    pcell_loc: CellId,
    tracked storage: Option<Perm<S>>,
) -> (tracked out: (
    Tracked<Self>, Tracked<flag<S>>,
    Tracked<reader_collection<S>>, Tracked<Option<writer<S>>>,
));
```

`reader_multiset<S>` was a legacy `MultisetToken` alias.
`reader_collection<S>` is a generated tracked owner of checked resources.
The tuple position is retained. Collection names depend on the machine.
Do not construct the checked owner from an instance id alone.

**Before — use:**

```rust
let tracked (Tracked(inst), Tracked(flag), _, Tracked(writer)) =
    RefCounter::Instance::<S>::initialize_empty(value_cell.id(), None);
```

**After — use (retained):**

```rust
let tracked (Tracked(inst), Tracked(flag), _, Tracked(writer)) =
    RefCounter::Instance::<S>::initialize_empty(value_cell.id(), None);
```

The example discards the empty collection, so the collection type change needs
no change at this call. A client that names the return type must change it.

#### Deposit the permission and borrow the reader guard

**Before — generated methods on `RefCounter::Instance<S>`:**

```rust
proof fn do_deposit(
    tracked &self, x: Perm<S>, tracked flag: &mut flag<S>,
    tracked storage: Perm<S>, tracked writer: writer<S>,
);
proof fn reader_guard<'a>(
    tracked &self, x: Perm<S>, tracked reader: &'a reader<S>,
) -> (tracked out: &'a Perm<S>);
```

**After — generated signatures (retained):**

```rust
proof fn do_deposit(
    tracked &self, x: Perm<S>, tracked flag: &mut flag<S>,
    tracked storage: Perm<S>, tracked writer: writer<S>,
);
proof fn reader_guard<'a>(
    tracked &self, x: Perm<S>, tracked reader: &'a reader<S>,
) -> (tracked out: &'a Perm<S>);
```

**Before — uses:**

```rust
inst.do_deposit(value_perm, &mut flag, value_perm, writer.tracked_unwrap());
self.ref_cell.inst.borrow().reader_guard(self.reader@.element(), self.reader.borrow())
```

**After — uses (retained):**

```rust
inst.do_deposit(value_perm, &mut flag, value_perm, writer.tracked_unwrap());
self.ref_cell.inst.borrow().reader_guard(self.reader@.element(), self.reader.borrow())
```

The guard now comes from a checked storage proof. Its returned permission
reference is tied to the reader borrow. Keep that owner alive for the borrow.
The executable read uses the permission reference. A state observation cannot
replace it. The negative test
[counting_withdraw_live_reader](../../examples/verified_tsm/negative/counting_withdraw_live_reader.rs)
checks that withdrawal fails while a reader remains owned.

### Change 5: Check resource proof obligations

The generated resource proofs do not justify an `assume`, an admitted proof,
or an `external_body` in the client. Prove induction, domain, arithmetic, and
termination obligations. Use modern `proof fn`, tracked modes, and wrappers
where older examples use earlier Verus syntax.

The generated field getters remain available. The Disk model illustrates their
signatures. Its client interpretation change is described in Change 6:

```rust
// Before, on AuthFrag::auth<nat, Block>:
spec fn instance_id(&self) -> vstd::tokens::InstanceId;
spec fn value(&self) -> Map<nat, Block>;

// After, on AuthFrag::auth<nat, Block>:
spec fn instance_id(&self) -> vstd::resource::Loc;
spec fn value(&self) -> Map<nat, Block>;
```

These getter signatures describe the generated API. The checked proof bodies
must establish the resource operations. Changes to user helper bodies are
listed in the next section.

#### Select checked local readiness for physical transitions

The original RefCell declaration has no local readiness attribute.
The checked declaration selects four physical transitions:

**Before — declaration from the original RefCell example:**

```rust
tokenized_state_machine!(RefCounter<S> {
    // The original fields and transitions.
});
```

**After — declaration from the checked RefCell example:**

```rust
verified_tokenized_state_machine!(
    #[verified_local_ready(do_deposit, do_withdraw, new_reader, drop_reader)]
    RefCounter<S> {
        // The same fields and transitions.
    }
);
```

The generated `Instance::do_deposit` signatures and client calls are shown in
Change 4. Their shapes are retained. The new attribute selects checked proofs
that derive readiness from facts in the supplied resources.
Those proofs establish readiness for every compatible state that satisfies
the invariant, including ownership and deposit conditions.

The checked raw interface can also return state observations from an exchange.
An observation contains the resulting token, withdrawn storage, and
specification values `before`, `after`, and `frame`. These states describe a
compatible completion. They cannot create physical permissions or identify a
unique hidden history. These checked proofs and observations are additions to
the original trusted resource implementation.

## Changes to examples

This section covers user-written helpers, structures, invariants, and
executable methods. These changes are specific to the named clients.
They are not additional methods supplied by the TSM system.

### Change 6: Constrain the supplied Disk authority


The Disk example is
[before](../../examples/state_machines/disk_example.rs) and
[after](../../examples/verified_tsm/disk_example.rs).
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

### Change 7: Prove generic equality in Interner


The Interner example is
[before](../../examples/state_machines/interner.rs) and
[after](../../examples/verified_tsm/interner.rs).

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

**Before — use:**

```rust
let eq = compute_eq(&val, &self.store[idx]);
```

**After — use (retained):**

```rust
let eq = compute_eq(&val, &self.store[idx]);
```

The `T: VerifiedEq` bound requires a checked equality implementation.
The example provides one for `u64`. This requirement replaces the trusted stub.
It is a client change, not a generated token method.

### Change 8: Update Rc and Arc invariants and overflow handling

#### Add an identity field for the invariant

The checked [Rc](../../examples/verified_tsm/rc.rs) and
[Arc](../../examples/verified_tsm/arc.rs) add an identity field for the invariant
predicate. Rc has these fields:

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
a resource. The generated `Instance::id` signatures are shown above.

#### Handle overflow in the executable clone

The Rc example is
[before](../../examples/state_machines/tutorial/rc.rs) and
[after](../../examples/verified_tsm/rc.rs).

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
the example's executable method. It does not change every token clone method.

### Change 9: Update metadata and constant comparisons in the application

The application model is `SingleThreadedMachine`, defined in
[AwsArgLlcrtNice](../../../AwsArgLlcrtNice/theories/verus/concurrency/src/single_threaded_proofs.rs).
Its original source is in that repository's commit `acd267f0`.
It is not part of the TSM library.

#### Store metadata in ghost ticket records

**Before — field in `EnterPreEntryTicket`:**

```rust
pub instance: SingleThreadedMachine::Instance<Result, Tix>,
```

**After — field in `EnterPreEntryTicket`:**

```rust
pub ghost instance: SingleThreadedMachine::InstanceInfo<Result, Tix>,
```

The ticket now stores `instance.info()`. `EnterTicketing` keeps its operational
`Tracked<SingleThreadedMachine::Instance<Result, Tix>>`. Not every machine
exports `InstanceInfo`.

#### Compare observable properties of cloned constants

In the SingleThreadedMachine client, the stored ticketing resource can be a
checked clone. The clone contract gives agreement about its observations.
It need not give equality of opaque Rust values.

**Before — invariant in `single_threaded_barrier.rs`, commit `acd267f0`:**

```rust
m.tix_inst_persist@.value() == m.tix_instance@
```

**After — invariant in the same client:**

```rust
same_ticketing::<A, Tix>(m.tix_inst_persist@.value(), m.tix_instance@)
```

The checked user predicate has this definition:

```rust
pub open spec fn same_ticketing<R, Tix: StbTicketing<R>>(left: Tix, right: Tix) -> bool {
    &&& left.instance() == right.instance()
    &&& left.max_threads() == right.max_threads()
    &&& forall|value: R| left.valid_result(value) == right.valid_result(value)
}
```

Keep each observation required by the protocol. Agreement about an id alone
cannot replace required agreement about constants or result validity.

### Check the complete client

Verify the client. Compile and run its executable example. Use `--no-cheating`
for an example that must contain no assumed proofs. Review existing trusted
specifications separately in a larger application.

The [ergonomics report](../../examples/verified_tsm/ERGONOMICS.md) records the
source comparisons and required adaptations. Counting2, CountingN, RefCell,
Rc, Arc, and Interner include executable uses. An empty `main` or a tracked
history checks proof code but does not run a synchronization algorithm.

### API changes at a glance

The table summarizes both sections. The scope identifies a generated system
change or a change to a specific example or application.
It states the API or use difference. “Retained” means that the shown
signature or call shape does not change. Contracts and resource proofs can
still change.

| Scope | API or use | Before | After and actual difference |
| --- | --- | --- | --- |
| System | Tokenized macro | `tokenized_state_machine!` trusts generated resource operations. | `verified_tokenized_state_machine!` generates checked resource definitions and protocol proofs. Field token names and supported exchange call shapes are retained. |
| System | Ordinary model macro | `state_machine!` generates mathematical states and relations. | `verified_state_machine_model!` checks the model with unannotated fields. It supplies no token or property API. |
| System | Instance duplication | `Instance` implements `Copy`; `clone` promises complete value equality. | `Instance` is an owned tracked resource without `Copy`. Its proof clone promises identity and constant agreement. |
| System | Instance id spelling | Getters return `vstd::tokens::InstanceId`. | Getters return `vstd::resource::Loc`. `InstanceId` is already an alias for `Loc` in this tree. |
| System | Generated metadata type | No separate `InstanceInfo` type is supplied. | Selected profiles add `InstanceInfo` and `instance.info()` for identity and constants. The type supplies no resource ownership. |
| System | Persistent token clone, illustrated by `SingleThreadedMachine::entered` | The persistent field token implements `Copy`; repeated uses copy it. | It has no `Copy`. `clone(tracked &mut self)` splits and replaces the internal resource while preserving its fragment and field value. |
| System | Exclusive token uniqueness, illustrated by `SingleThreadedMachine::stage.unique` | The legacy trait method has no precondition and ensures distinct ids plus receiver restoration. | The inherent method requires equal ids and ensures `false`. Its mutable receiver and shared other-token argument are retained. |
| System | Empty-token basis, illustrated by `generate_empty_entering_token` | Takes only `tracked &self` and returns four count-token wrappers. | Adds a preserved mutable `stage` basis. The `_with_basis_entering` alternative accepts an entering basis. The return tuple is retained. |
| System | Count token `split` and `join` | Mutable receiver; split needs an owned count bound; join needs equal ids. | Retained signatures and premises. The methods have checked resource proofs. |
| System | Generated collection return, illustrated by RefCell | Returns `Tracked<reader_multiset<S>>`, a legacy token collection alias. | Returns `Tracked<reader_collection<S>>`, a generated checked owner. Tuple position, storage argument, and remaining return types are retained. |
| System | Legacy token traits | Generated roles use `vstd::tokens` trait implementations. | Checked roles supply inherent methods. Matching method names do not imply legacy trait implementations; generic trait adapters can need changes. |
| System | Storage deposit and guard, illustrated by RefCell | Deposit takes the specification value and actual permission; guard returns a reader-borrowed permission reference. | Retained arguments and lifetime. Storage and guard operations now have checked proofs over actual permissions. |
| System | Selected physical transition proofs and observations | Generated storage methods have trusted resource contracts. No checked local readiness or exchange-observation API is supplied. | `verified_local_ready` selects proofs of readiness for every compatible completion. The checked raw interface can return actual exchange results with compatible state observations. |
| Example | External application's SingleThreadedMachine ghost metadata | Ticket records store `Instance<Result, Tix>` handles. | Records store `InstanceInfo<Result, Tix>` from `instance.info()`. Metadata has identity and constants; resource operations require the separate tracked instance. |
| Example | Rc/Arc invariant identity | The invariant uses the original instance value. | An added `Ghost<Loc>` field supplies an identity parameter. The invariant relates it to the owned instance. |
| Example | Disk interpretation | A two-argument spec function returns a described authority token. | A three-argument spec predicate returns `bool` and constrains a supplied authority token. |
| Example | Interner equality | An unrestricted generic helper has a trusted, unimplemented body. | The helper requires `T: VerifiedEq` and calls a checked provider. Existing calls retain their shape. |
| Example | Rc/Arc executable clone | Returns `Self` after an assumed increment bound. | Returns `Option<Self>`; `None` at `u64::MAX`. Callers handle the failure result. |
| Example | Cloned ticketing constant agreement | Invariants require complete resource-value equality. | `same_ticketing` requires agreement about instance, thread bound, and result validity. |
