# Logatom: Verus vs Iris

## Basic atomic operations

There are many atomic types in the verus standard library (vstd), we are using the [`vstd::atomic::PAtomicU64`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/struct.PAtomicU64.html) (**P**ermission **Atomic** **U**nsigned **64**-bit integer) for this comparison.

The most notable differences are:
- Iris conflates atomic variables and pointers, whereas in Verus they're separate datatypes.
- Verus treats resources and logical statements separately; Resources are part of the function signature and checked by the Rust borrow checker, and logical statements live in the `requires` and `ensures` clauses and are checked by the Z3 SMT solver.
- Verus uses the "forward reasoning" rules, whereas Iris typically uses "backwards reasoning" rules.
- Verus makes heavy use of borrowing when managing resources, which doesn't exist in Iris.
    - If a resource appears in the input and output unchanged, we can borrow it immutably (see atomic load).
    - If the resource it changed, we can borrow it mutably (see atomic store).
    - Verus has an `old` function to refer to the previous value of a mutable reference.

### New atomic

$$
\text{Iris:}\quad
\rhd(\forall l.\ l \mapsto v \mathop{-\!*} Q(l))\
\vdash\text{wp}\ \text{new}(v)\
\{\ w. Q(w)\ \}
$$

$$
\text{Fwd. reason.:}\quad
\{\,\top\,\}\
l = \text{new}(v)\
\{\,l \mapsto v\,\}
$$

```rs
fn new(v: u32) -> res : (PAtomicU64, Tracked<PermissionU64>)
    ensures
        res.1.patomic == res.0.id(),
        res.1.value == v,
```

### Atomic load

$$
\text{Iris:}\quad
l\mapsto v\ast\rhd(l\mapsto v \mathop{-\!*} Q(v))\
\vdash\text{wp}\ !\,l\
\{\ w. Q(w)\ \}
$$

$$
\text{Fwd. reason.:}\quad
\{\,l\mapsto v\,\}\
v =\ !\,l\
\{\,l\mapsto v\,\}
$$

```rs
fn load(&self, perm: Tracked<&PermissionU64>) -> ret : u32
    requires
        self.id() == perm.patomic,
    ensures
        perm.value == ret,
```

### Atomic store

$$
\text{Iris:}\quad
l\mapsto v\ast\rhd(l \mapsto w \mathop{-\!*} Q())\
\vdash\text{wp}\ l\gets w\
\{\ w. Q(w)\ \}
$$

$$
\text{Fwd. reason.:}\quad
\{\,l\mapsto v\,\}\
l\gets w\
\{\,l\mapsto w\,\}
$$

```rs
fn store(&self, perm: Tracked<&mut PermissionU64>, w: u32)
    requires
        self.id() == old(perm).patomic,
    ensures
        perm.value == w,
        self.id() == perm.patomic,
```

<!--
### Atomic compare and swap

$$
\frac{v_1 = v_3}{
    l\mapsto v_3\ast\rhd(l \mapsto v_2 \mathop{-\!*} Q(\text{true}))\
    \vdash\text{wp}\ \text{CAS}(l, v_1, v_2)\
    \{\ v. Q(v)\ \}
}
$$

$$
\frac{v_1 \neq v_3}{
    l\mapsto v_3\ast\rhd(l \mapsto v_3 \mathop{-\!*} Q(\text{false}))\
    \vdash\text{wp}\ \text{CAS}(l, v_1, v_2)\
    \{\ v. Q(v)\ \}
}
$$

```rs
fn compare_exchange(
    &self,
    perm: Tracked<&mut PermissionU64>,
    curr: u32,
    new: u32,
) -> ret : Result<u32, u32>
    requires
        self.id() == old(perm).patomic,
    ensures
        self.id() == perm.patomic,
        match ret {
            Ok(r) => {
                &&& curr == old(perm).value
                &&& perm.value == new
                &&& r == old(perm).value
            }
            Err(r) => {
                &&& curr != old(perm).value
                &&& perm.value == old(perm).value
                &&& r == old(perm).value
            }
        },
```
-->

## Atomic Invariants

Atomic invariants are represented using the [`vstd::invariant::AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html) type in Verus.

The type `AtomicInvariant<K, V, Pred>` has three type parameters:
- `K` the constant part of the invariant
    - This is set when the invariant is allocated and cannot change afterwards
    - Only accessible through spec function, i.e. cannot meaningfully contain resources
- `V` the value of the invariant
    - You temporarily get full ownership of this value when opening an invariant
    - This is where resources live in the invariant
    - Value can change when invariant is opened if insufficiantly restricted by `inv` predicate
- `Pred` the predicate type implements the trait `InvariantPredicate<K, V>` below

```rs
pub trait InvariantPredicate<K, V> {
    spec fn inv(k: K, v: V) -> bool;
}
```

$$
\boxed{k\ast \exists v.\ v\ast P(k, v)}^{\,N}
$$

### Allocate atomic invariant

$$
\frac{
    P\ast\boxed{R}^{\,N}\vdash\text{wp}^E\,e\ \{\ v.\ Q(v)\ \}
}{
    P\ast R\,\vdash\text{wp}^E\,e\ \{\ v.\ Q(v)\ \}
}
$$

```rs
proof fn new(k: K, tracked v: V, ns: int) -> tracked inv : AtomicInvariant<K, V, Pred>
    requires
        Pred::inv(k, v),
    ensures
        inv.constant() == k,
        inv.namespace() == ns,
```

### Open atomic invariant

$$
\frac{
    P\ast\rhd R\,\vdash\text{wp}^{E/N}\,e\ \{\ v.\ \rhd R\ast Q(v)\}
    \qquad N\subseteq E
    \qquad \text{atomic}(e)
}{
    P\ast\boxed{R}^N \vdash\text{wp}^E\,e\ \{\ v.\ Q(v)\ \}
}
$$

Opening an invariant requires later credits:

```rs
let Tracked(credit) = vstd::invariant::create_open_invariant_credit();

proof {
    open_atomic_invariant_in_proof!(credit => &atom_inv => v => {
        // assume atom_inv.inv(v)
        ...
        // assert atom_inv.inv(v)
    });
}
```

In `exec` mode, creating later credits is trivial, so the user is allowed to omit them:

```rs
open_atomic_invariant!(&atom_inv => v => {
    // assume atom_inv.inv(v)
    ...
    // assert atom_inv.inv(v)
});
```

## Logical Atomicity

```rs
pub struct AtomicUpdate<X, Y, Pred> { ... }

impl<X, Y, Pred> AtomicUpdate<X, Y, Pred> {
    pub uninterp spec fn resolves(self) -> bool;
}

pub trait UpdatePredicate<X, Y> {
    spec fn req(x: X) -> bool;
    spec fn ens(x: X, y: Y) -> bool;

    open spec fn outer_mask(self) -> Set<int>;
    open spec fn inner_mask(self) -> Set<int>;
}
```

### Atomic specification

$$
\langle P \rangle \{ P' \}
\;e\;
\langle Q \rangle \{ Q' \}
^{Eo}_{Ei}
$$

```rs
fn function(px: Px) -> (py: Py)
    atomically (atomic_update) {
        type PredType,

        (ax: Ax) -> (ay: Ay),

        requires atomic_pre_condition(px, ax),      // P
        ensures atomic_post_condition(px, ax, ay),  // Q

        outer_mask [...],  // Eo
        inner_mask [...],  // Ei
    },

    requires private_pre_condition(px),              // P'
    ensures private_post_condition(px, ax, ay, py),  // Q'
{
    ..;
}
```

**Reminder:** Pre- and postconditions in Verus are pure/logical statements, if we want to associate resources with them, we place them in the following locations (in execution order):
- `private_pre_condition`: function arguments (`px: Px`)
- `atomic_pre_condition`: atomic update input (`ax: Ax`)
- `atomic_post_condition`: atomic update output (`ay: Ay`)
- `private_post_condition`: return value (`py: Py`)
- each predicate can "see" all previous values/resources

The masks `outer_mask` and `inner_mask` are 1:1 copies of $Eo$ and $Ei$ in Iris
- `outer_mask` ($Eo$) restricts where the AU can be **constructed**
- `inner_mask` ($Ei$) restricts where the AU can be **opened**
- An atomic update with $Ei ⊈ Eo$ can not be constructed

The type of `atomic_update` is `AtomicUpdate<Ax, Ay, PredType>`
- `PredType` and its trait implementation are generated automatically
- the `type PredType` declaration is optional, if no name is specified, the default name of the predicate type is `pascal_case(function_name) + "AtomicUpdatePredicate"`

We think of the atomic update as a function `Ax -> Ay`
- **Caller:** in the atomic function call, the atomic update is represented as an `update` function (user chooses the name) with the same signature
- **Callee:** opening the atomic update corresponds to defining the `update` function
    - In the abort case (`Err(ax)`), we defer the definition
    - In the commit case (`Ok(ay)`), we give the value of the function
- In Iris, $AU$ is (approximately) defined as follows:
    $$
        \nu U.\ ^{Eo}{|\mskip-8mu\Rrightarrow}^{Ei}\exists x.\ P(x)\ast\Big(
            \big(P(x)\mathop{-\!*}~^{Ei}{|\mskip-8mu\Rrightarrow}^{Eo}U\big)\land
            \big(\forall y.\ Q(x, y)\mathop{-\!*}~^{Ei}{|\mskip-8mu\Rrightarrow}^{Eo}\phi(y)\big)
        \Big)
    $$
    - the $\land$ is an "additive conjunction" or "internal choice"
    - when constructing the $AU$, you are given $P(x)$ and you produce either $P(x)$ or $Q(x, y)$
    - the abort case $(P(x)\mathop{-\!*}~^{Ei}{|\mskip-8mu\Rrightarrow}^{Eo}U)$ may defer the commit indefinitely due to greatest fixpoint ($\nu$)
    - the commit case $(\forall y.\ Q(x, y)\mathop{-\!*}~^{Ei}{|\mskip-8mu\Rrightarrow}^{Eo}\phi(y))$ resolves the atomic update

In Iris, we are forced to resolve the atomic update eventually since we need the $\phi(y)$ to finish the proof of the weakest precondition.
In Verus, we artificially force the user to resolve the AU using the `resolves` predicate.
- `AtomicUpdate::resolves` is an uninterpreted spec function, from atomic updates to `bool`
- It behaves like a prophesy variable, initially the value of the function is unknown, and we learn that the function evaluates to `true` when the atomic update is opened and resolved.
- The user must prove that `au.resolves()` at the end of the logically atomic function.

### Atomic function call

```rs
let tracked phi;

// assert private pre `function`
function(args) atomically |update| {
    // ...
    // assert atomic pre `function`
    let new_perm = update(old_perm);
    // assume atomic post `function`
    // ...
    phi = ...;
}
// assume private post `function`

stuff(phi);
```

### Open atomic update

Commit:

```rs
let res = try_open_atomic_update!(atomic_update, old_perm => {
    // assume atomic pre `atomic_update`
    // ...
    // assert atomic post `atomic_update`
    Tracked(Ok(new_perm))
});

assert(res == Tracked(Ok(())));
assert(atomic_update.resolves());
```

Abort:

```rs
let res = try_open_atomic_update!(atomic_update, old_perm => {
    // assume atomic pre `atomic_update`
    // ...
    // assert `old_perm == new_perm`
    Tracked(Err(new_perm))
});

assert(res == Tracked(Err(atomic_update)));
```

### Example: Atomic Increment

Iris/Heaplang:

$$
\large
\begin{align*}
    \text{rec}\ inc(x) =\ &\text{let}\ v=\ !x \\
    &\text{if}\ \text{CAS}(x, v, v+1)\ \text{then}\ v \\
    &\text{else}\ inc(x)
\end{align*}
$$

Rust:

```rs
fn increment(var: &AtomicU64) -> u64 {
    let mut curr = var.load(SeqCst);

    loop {
        let res = var.compare_exchange_weak(curr, curr + 1, SeqCst, SeqCst);

        match res {
            Ok(_) => return curr,
            Err(new) => curr = new,
        }
    }
}
```

Verus:

```rs
pub fn increment(var: &PAtomicU64) -> (out: u64)
    atomically (atomic_update) {
        (old_perm: PermissionU64) -> (new_perm: PermissionU64),
        requires
            old_perm@.patomic == var.id(),
        ensures
            new_perm@.patomic == old_perm@.patomic,
            new_perm@.value == old_perm@.value.wrapping_add(1),
        outer_mask any,
    },
    ensures
        out == old_perm@.value,
{
    let tracked mut au = atomic_update;

    let mut curr;
    let err_au = try_open_atomic_update!(au, perm => {
        curr = var.load(Tracked(&perm));
        Tracked(Err(perm))
    });

    proof { au = err_au.get().tracked_unwrap_err() };

    loop invariant au == atomic_update {
        let next = curr.wrapping_add(1);

        let res;
        let maybe_au: Tracked<Result<(), AtomicUpdate<_, _, _>>> = try_open_atomic_update!(au, mut perm => {
            let ghost prev = perm;

            res = var.compare_exchange_weak(Tracked(&mut perm), curr, next);

            Tracked(match res {
                Ok(_) => Ok(perm),
                Err(_) => Err(perm),
            })
        });

        match res {
            Ok(_) => {
                assert(atomic_update.resolves());
                return curr;
            }

            Err(new) => {
                proof { au = maybe_au.get().tracked_unwrap_err() };
                curr = new;
            },
        }
    }
}
```
