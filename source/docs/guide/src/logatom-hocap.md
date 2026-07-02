# Logical Atomicity in the HOCAP style

In Verus, there is another way to prove linearization, based on the [HOCAP](https://kasv.dk/articles/hocap.pdf).
HOCAP is a proof pattern, rather than a syntactic language feature. This makes it harder
(but still possible) to [open invariants around logical atomic code](https://research.ralfj.de/iris/talk-iris2019.pdf).

To use this, one needs to use the [`logatom` traits](https://verus-lang.github.io/verus/verusdoc/vstd/logatom/index.html).
The main concept is that there are `Linearizer`s and `Operations` (both mutable and read-only versions).
A `Linearizer` is a ghost callback that has pre- and post- conditions.
It must be called to linearize an `Operation` at a valid [linearization point](https://dl.acm.org/doi/pdf/10.1145/78969.78972),
where it is consumed and a `Completion` is obtained.

In our examples, we will focus on [`MutLinearizer`](https://verus-lang.github.io/verus/verusdoc/vstd/logatom/trait.MutLinearizer.html),
but the [`ReadLinearizer`](https://verus-lang.github.io/verus/verusdoc/vstd/logatom/trait.ReadLinearizer.html) is very similar.

## How the logically atomicity proof works

When we have a linearizer , we need to call `MutLinearizer::apply` at a valid linearization point.
When `apply` happens, we present a [`Resource`](https://docs.rs/vstd/latest/vstd/resource/algebra/struct.Resource.html).
This resource captures the concurrent object being talked about.
The linearization proof comes from the fact that we can encode the pre and post conditions of the operations
(which can be thought about as the logically atomic triple)
to express that the ordering that the object is going through (expressed via the resource) makes sense.

## Calling `apply`

Consider the example of a monotonic counter (as seen in the examples dir).
The ghost state is modelled after a [`GhostVarAuth`](https://verus-lang.github.io/verus/verusdoc/vstd/resource/ghost_var/struct.GhostVarAuth.html) held in an [`AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html),
and a [`GhostVar`](https://verus-lang.github.io/verus/verusdoc/vstd/resource/ghost_var/struct.GhostVar.html) which the `MutLinearizer` holds.

```rust
open_atomic_invariant!(inv => v => {
    let tracked CounterInvariant { perm, auth } = v; // destructure

    // curr is the loaded value
    res = self.atomic.compare_exchange_weak(Tracked(&mut perm), curr, next);

    proof {
        if res is Ok {
            let op = IncOp { id: self.auth_id() };
            compl = Some(lin.apply(op, &mut auth, (), &curr));

            v = CounterInvariant { perm, auth };
        } else {
            v = CounterInvariant { perm, auth };
        }
    }
});
```
In the CAS loop to increment the counter, we open the invariant, call `compare_exchange_weak` and,
on success, use the `GhostVarAuth` to update the ghost state within `apply`.

## Constructing the Operations

Logical atomicity and linearizability deal in operations being linearized.
The `ReadOperation` and `MutOperation` model these operations that are linearized.

In the counter example, we can specify an increment operation, `IncOp`:

```rust
/// Operation for incrementing the counter
struct IncOp {
    /// Location of the GhostVarAuth
    id: Loc,
}

impl logatom::MutOperation for IncOp {
    type Resource = GhostVarAuth<u64>;

    type ExecResult = u64;

    type NewState = ();

    closed spec fn requires(
        self,
        pre: Self::Resource,
        new_state: Self::NewState,
        e: Self::ExecResult,
    ) -> bool {
        &&& pre.id() == self.id
        &&& pre@ == e
    }

    closed spec fn ensures(
        self,
        pre: Self::Resource,
        post: Self::Resource,
        new_state: Self::NewState,
    ) -> bool {
        &&& post.id() == self.id
        &&& post@ == pre@.wrapping_add(1)
    }
}
```

Here, we force the resource being passed in to refer to the same ghost location
as the counter's resource (by having the location in the operation itself) and
models the logically atomic pre and post conditions.

## Constructing a Linearizer

The linearizer tipically holds the resource itself. The apply function can either
express agreement (for read only operations) or update the resource (for mutable operations).

We can express additional pre and post conditions on the linearizer. Centrally, in the `apply`
function we must be able to show that from both the operation and the linearizer preconditions
we can derive both post conditions:

```rust
struct IncPerm {
    pub tracked var: GhostVar<u64>,
}

impl logatom::MutLinearizer<IncOp> for IncPerm {
    type Completion = GhostVar<u64>;

    closed spec fn namespaces(self) -> ISet<int> { ISet::empty() }

    closed spec fn pre(self, op: IncOp) -> bool {
        op.id == self.var.id()
    }

    closed spec fn post(self, op: IncOp, exec_res: u64, completion: Self::Completion) -> bool {
        &&& op.id == self.var.id()
        &&& op.id == completion.id()
        &&& exec_res.wrapping_add(1) == completion@
    }

    proof fn apply(
        tracked self,
        op: IncOp,
        tracked resource: &mut GhostVarAuth<u64>,
        new_state: (),
        exec_res: &u64,
    ) -> (tracked result: Self::Completion) {
        let tracked mut var = self.var;
        resource.update(&mut var, exec_res.wrapping_add(1));
        var
    }

    proof fn peek(tracked &self, op: IncOp, tracked resource: &GhostVarAuth<u64>) {}
}

```
