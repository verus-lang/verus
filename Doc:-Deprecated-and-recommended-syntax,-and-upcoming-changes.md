The Verus syntax is in flux, and breaking changes are coming with the https://github.com/verus-lang/verus/tree/main_new branch.

This document collects snippets of syntax that we plan to support long term, details breaking changes, and what deprecated syntax it replaces.

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

## Spec functions

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

## Proof functions

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

## Exec functions

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

fn g(Tracked(t): Tracked<S>) -> k {
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
