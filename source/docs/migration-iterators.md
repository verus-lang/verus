# Iterator upgrade

Verus has a new, unified interface for iterators, including those used in `for` loops. The previous
interface relied on ad-hoc ghost traits (`ForLoopGhostIterator`, `ForLoopGhostIteratorNew`)
and iterator-specific ghost fields (`iter.cur`, `iter.keys`, `iter.pos`, `iter@`, ...). The
new interface is built on the standard `Iterator` trait extended with a uniform set of Verus specifications.

Below are some examples of how you can update your code to adapt to the new specifications.

---

## Change 1: `iter.cur` → `x` or `iter.index()`

*Relevant to anyone using `for … in iter: 0..n`.*

The old `iter.cur` field gave the value of the **current** loop element for range iterators.
In the new interface, this is just `x` (the loop variable) or `iter.index()` (the number of
items produced so far). For a zero-based range these are equal (`x == iter.index()`).

**Before:**
```rust
for x in iter: 0..10
    invariant n == iter.cur * 3,
{
    assert(x == iter.cur);
    n += 3;
}
```

**After:**
```rust
for x in iter: 0..10
    invariant n == x * 3,
{
    assert(x == iter.index());
    n += 3;
}
```

**Before:**
```rust
for x in iter: 5..10
    invariant 
        n == 2 * iter.cur,
{
    assert(x == iter.cur + 5);
    n += 2;
}
```

**After:**
```rust
for x in iter: 5..10
    invariant 
        n == 2 * iter.index(),
{
    assert(x == iter.index() + 5);
    n += 2;
}
```


The same applies to `decreases` clauses that referenced `iter.cur`.

---

## Change 2: `iter@` → `iter.history()` or `iter.seq().take(iter.index())`

*Relevant to anyone whose invariants referred to `iter@`.*

In the old system, `iter@` yielded a `Seq` of the items produced so far. The new system has two ways to express this:

- **`iter.history()`** — a `Seq<Item>` of items produced so far. This is a direct replacement for
  `iter@` when the iterator yields owned values.  Automation may be slightly weaker, since
  this is defined in terms of `iter.seq()`
- **`iter.seq().take(iter.index())`** — equivalent, but written in terms of the full prophetic
  sequence.  However, the most reliable automation will typically come from writing an explicit quantifier,
e.g., `forall |i| 0 <= i < iter.index() ==> iter.seq()[i] == ...`

In addition, in the new system, both `iter.seq()` and `iter.history()` return a
`Seq<Item>` where `Item` is exactly the iterator's `Item` type. For iterators
that yield references (`&T`), `iter.seq()` is a `Seq<&T>`; call `.unref()` to
get `Seq<T>`.  You can also call `.as_ref()` on a `Seq<T>` to get a `Seq<&T>`.

For example, when iterating over an owned collection whose items are `Copy` values:

**Before:**
```rust
// Iterating over a range — iter@ gave elements seen so far
for i in iter: 0..n
    invariant
        items@ == iter@,
{
    items.push(i);
}
```

**After:**
```rust
for i in iter: 0..n
    invariant
        items@ == iter.history(),
{
    items.push(i);
}
```
or preferably:
```
for i in iter: 0..n
    invariant
        items.len() == iter.index(),
        forall 0 <= i < items.len() ==> items[i] == iter.seq()[i],
{
    items.push(i);
}
```


---

## Change 3: Slice and array iterator invariants

*Relevant to anyone iterating over slices, arrays, or `Vec` with `iter:` bindings.*

The old slice iterator exposed `.pos` (position) and `.elements` (the full sequence) as
named fields on the ghost iterator. The new interface uses `iter.index()` and `iter.seq()`:

**Before:**
```rust
for x in it: sl.iter()
    invariant
        i == it.pos,
        it.elements == seq![0u32, 2u32, 4u32],
{
    ...
}
```

**After:**
```rust
for x in it: sl.iter()
    invariant
        i == it.index(),
        it.seq().unref() == seq![0u32, 2u32, 4u32],
{
    ...
}
```

Note the `.unref()` call: `sl.iter()` yields references (`&T`), so `it.seq()` has type
`Seq<&T>`. 

---

## Change 4: Hash map and set iterator invariants

*Relevant to anyone iterating over `HashMap`, `HashSet`, or `BTreeMap`.*

The old hash/set iterators exposed iterator-specific ghost fields (`iter.keys`, `iter.values`,
`iter.elements`, `iter.kv_pairs`, `iter.pos`). The new interface is uniform: `iter.seq()`
holds all items as references, and `iter.index()` is the position.

Additionally, a common idiom with the old iterators would store the iterator
into a variable before the loop so as to snapshot its ghost state in advance.
That is no longer necessary; the iterator expression can appear inline.

### Example: HashMap keys

**Before:**
```rust
let m_keys = m.keys();
assert(m_keys@.1.to_set() =~= set![3u32, 6u32]);
let ghost g_keys = m_keys@.1;

let mut items = Vec::<u32>::new();
assert(items@ =~= g_keys.take(0));

for k in iter: m_keys
    invariant
        iter.keys == g_keys,
        g_keys.to_set() =~= set![3u32, 6u32],
        items@ == iter@,
{
    assert(iter.keys.take(iter.pos).push(*k) =~= iter.keys.take(iter.pos + 1));
    items.push(*k);
}
```

**After:**
```rust
let mut items = Vec::<u32>::new();

for k in iter: m.keys()      // iterator created inline
    invariant
        items@ == iter.seq().take(iter.index()).unref(),
{
    items.push(*k);
}
```

---

## Change 5: Removing the `ForLoopGhostIterator` implementation

*Relevant to anyone who implemented a custom iterator for use in verified `for` loops.*

The old system required two types (one exec, one ghost) and multiple trait implementations
to construct your own iterator type.

The new system only requires defining one type, and having that type implement
the `IteratorSpecImpl` trait.  See the [new docs for details](guide/src/iterator-specs.md).
