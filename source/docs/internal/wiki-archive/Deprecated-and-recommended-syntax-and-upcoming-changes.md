NOTE: These changes have been applied a while ago, this page is now just an archive.

---

The Verus syntax is in flux, and breaking changes are coming with the https://github.com/verus-lang/verus/tree/main_new branch.

This document collects snippets of syntax that we plan to support long term, details breaking changes, and what deprecated syntax it replaces.

## Standard library

### Old syntax

```
mod pervasive;
#[allow(unused_imports)]
use pervasive::prelude::*;
use pervasive::set_lib::lemma_len_union;
```

### New syntax

```
#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::set_lib::lemma_len_union;
```

## Functions

### Old syntax

```
fn f() {
}

#[proof]
fn g() {
}

#[spec]
fn h() {
}
```

### New syntax

```
fn f() {
}

proof fn g() {
}

spec fn h() {
}
```

## Spec functions, ghost variables

Note: all variables are ghost in spec functions

### Old syntax

```
#[spec]
fn f(i: int, j: int) -> int {
    recommends([
        i != 0,
        i <= j
    ]);
    decreases((i, j));
    decreases_when(0 <= i);

    i + j
}
```

### New syntax

```
spec fn f(i: int, j: int) -> int
    recommends
        i != 0,
        i <= j,
    decreases i, j when 0 <= i
{
    i + j
}
```

## Proof functions, tracked variables, ghost variables

Note: variables are ghost by default in proof functions

### Old syntax

```
#[proof]
fn f(i: int, j: int, #[proof] t: S) -> (k: int) {
    requires([i != 0]);
    ensures(|k: int| [
        k != 1,
        k == i + 1
    ]);
    decreases((i, j));

    let t_ghost_copy = t;
    #[proof] let t_moved = t;
    assert(t_moved == t_ghost_copy);
    i + 1
}
```

### New syntax

```
proof fn f(i: int, j: int, tracked t: S) -> (k: int)
    requires
        i != 0,
    ensures
        k != 1,
        k == i + 1,
    decreases i, j
{
    let t_ghost_copy = t;
    let tracked t_moved = t;
    assert(t_moved == t_ghost_copy);
    i + 1
}
```

## Exec functions, exec variables, tracked variables, ghost variables

Note: variables are exec by default in exec functions

### Old syntax

```
#[proof]
fn lemma1(i: int, #[proof] t: S) {
}

fn f(i: u32, #[spec] j: int, #[proof] t: S) -> u32 {
    requires([i != j, j < 10]);
    ensures(|k: u32| [
        k == i + 1
    ]);

    #[spec] let i_plus_j = i + j;
    #[spec] let t_ghost_copy = t;
    #[proof] let t_moved = t;
    lemma1(i, t_moved);
    assert(t_moved == t_ghost_copy);
    assert(i_plus_j == i + j);
    i + 1
}

fn g(#[proof] t: S) -> u32 {
    f(5, 6, t)
}
```

### Recent, but now old syntax

Note: ghost/tracked parameters in exec functions must be wrapped in `Ghost<T>` and `Tracked<T>` types.
The `ghost(expr)` and `tracked(expr)` expressions can be used to construct values of type
`Ghost<T>` and `Tracked<T>`.

```
proof fn lemma1(i: int, tracked t: S) {
}

fn f(i: u32, j: Ghost<int>, t: Tracked<S>) -> (k: u32)
    requires
        i != j@,
        i < 10,
    ensures
        k == i + 1,
{
    let i_plus_j: Ghost<int> = ghost(i + j@);
    let t_ghost_copy: Ghost<S> = ghost(t@);
    let t_moved: Tracked<S> = tracked(t.get());
    proof {
        lemma1(i as int, t_moved.get());
    }
    assert(t_moved@ == t_ghost_copy@);
    assert(i_plus_j@ == i + j@);
    i + 1
}

fn g(t: Tracked<S>) -> u32 {
    f(5, ghost(6), t)
}
```

### New syntax

Note: ghost/tracked parameters in exec functions must be wrapped in `Ghost<T>` and `Tracked<T>` types.
The `Ghost(expr)` and `Tracked(expr)` expressions can be used to construct values of type
`Ghost<T>` and `Tracked<T>`.
The `Ghost(x)` and `Tracked(x)` patterns can be used to unwrap `Ghost<T>` and `Tracked<T>` types.

```
proof fn lemma1(i: int, tracked t: S) {
}

fn f(i: u32, Ghost(j): Ghost<int>, Tracked(t): Tracked<S>) -> (k: u32)
    // Note: Ghost(j) unwraps the Ghost<int> value so that j has type int
    // Note: Tracked(t) unwraps the Tracked<S> value so that t has type S
    requires
        i != j,
        i < 10,
    ensures
        k == i + 1,
{
    let ghost i_plus_j = i + j;
    let ghost t_ghost_copy = t;
    let tracked t_moved = t;
    proof {
        lemma1(i as int, t_moved);
    }
    assert(t_moved == t_ghost_copy);
    assert(i_plus_j == i + j);
    i + 1
}

fn g(Tracked(t): Tracked<S>) -> u32 {
    f(5, Ghost(6), Tracked(t))
}
```

## Structs

### Old syntax

```
struct X {
    x: u32,
    #[spec] g: int,
    #[proof] t: int,
}

#[proof]
struct Y {
    #[spec] g: int,
    #[proof] t: int,
}

#[spec]
struct Z {
    i: int,
}

fn f(#[proof] t: int) -> (Spec<Z>, Proof<Y>) {
    let x = X {
        x: 7,
        g: 9,
        t,
    };
    #[spec] let g = x.g;
    #[proof] let t = x.t;
    #[proof] let y = Y { g, t };
    (Spec(Z { i: g + 1 }), Proof(y))
}
```

### New syntax

Note: ghost/tracked fields in exec structs must be wrapped in Ghost<T> and Tracked<T> types.
All fields in ghost structs are ghost.

```
struct X {
    x: u32,
    g: Ghost<int>,
    t: Tracked<int>,
}

tracked struct Y {
    ghost g: int,
    tracked t: int,
}

ghost struct Z {
    i: int,
}

fn f(Tracked(t): Tracked<int>) -> (Ghost<Z>, Tracked<Y>) {
    let x = X {
        x: 7,
        g: Ghost(9),
        t: Tracked(t),
    };
    let Ghost(g) = x.g;
    let Tracked(t) = x.t;
    let tracked y = Y { g, t };
    (Ghost(Z { i: g + 1 }), Tracked(y))
}
```

## Forall, exists, implies, equals

### Old syntax

```
forall(|i: int, j: int| imply(f(i, j), g(j, i)))
exists(|i: int, j: int| equal(f(i, j), g(j, i)))
```

or

```
forall(|i: int, j: int| f(i, j) >>= g(j, i))
exists(|i: int, j: int| f(i, j) === g(j, i))
```

### New syntax

```
forall|i: int, j: int| f(i, j) ==> g(j, i)
exists|i: int, j: int| f(i, j) == g(j, i)
```
