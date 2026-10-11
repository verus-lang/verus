# MIR building for a complex place expression with interleaved bounds checks

Notes on how `rustc_mir_build/src/builder/` lowers

```rust
fn test(a: *mut [*mut [*mut u64]; 20], b: *mut u8, c: *mut u8) {
    unsafe {
        let x = *(*(*a)[{ let y = 13; 0 }])[11];
    }
}
```

The `mir_dump/` directory checked into this package was stale (it was for `*b = *c`),
so it was regenerated from `test_ptr.rs` with the stable compiler into `/tmp/mirgen/dump`.
All code references below are to the local tree.

## Reference: the built MIR

```
fn test(_1: *mut [*mut [*mut u64]; 20], _2: *mut u8, _3: *mut u8) -> () {
    debug a => _1;
    debug b => _2;
    debug c => _3;
    let mut _0: ();
    let _4: u64;
    let _5: usize;
    let _6: i32;
    let mut _7: bool;
    let _8: usize;
    let mut _9: *const [*mut u64];
    let mut _10: usize;
    let mut _11: bool;
    scope 1 {
        debug x => _4;
    }
    scope 2 {
        debug y => _6;
    }

    bb0: {
        StorageLive(_4);
        StorageLive(_5);
        StorageLive(_6);
        _6 = const 13_i32;
        FakeRead(ForLet(None), _6);
        _5 = const 0_usize;
        StorageDead(_6);
        FakeRead(ForIndex, (*_1));
        _7 = Lt(copy _5, const 20_usize);
        assert(move _7, "index out of bounds: the length is {} but the index is {}", const 20_usize, copy _5) -> [success: bb1, unwind: bb3];
    }

    bb1: {
        StorageLive(_8);
        _8 = const 11_usize;
        _9 = &raw const (fake) (*(*_1)[_5]);
        _10 = PtrMetadata(move _9);
        _11 = Lt(copy _8, copy _10);
        assert(move _11, "index out of bounds: the length is {} but the index is {}", move _10, copy _8) -> [success: bb2, unwind: bb3];
    }

    bb2: {
        _4 = copy (*(*(*_1)[_5])[_8]);
        FakeRead(ForLet(None), _4);
        StorageDead(_8);
        StorageDead(_5);
        _0 = const ();
        StorageDead(_4);
        return;
    }

    bb3 (cleanup): {
        resume;
    }
}
```

## The THIR you start from

```
Deref                          *(...)[11]  — outermost
└ Index                        (...)[11]
  ├ lhs: Deref                 *( (*a)[blk] )
  │      └ Index               (*a)[blk]
  │        ├ lhs: Deref        *a
  │        │      └ VarRef a
  │        └ index: Block      { let y = 13; 0 }
  └ index: Literal 11
```

(Verified via `-Zunpretty=thir-tree`; every node is additionally wrapped in `ExprKind::Scope`.)

## Entry: `let x = <place expr>`

`block.rs:232` handles `StmtKind::Let` and calls `expr_into_pattern` (`matches/mod.rs:571`),
which for a plain binding:

1. `storage_live_binding` → `StorageLive(_4)`
2. `expr_into_dest(_4, …)` — `into.rs:849` is the arm for `ExprKind::Index | Deref | Field`.
   It asserts `Category::of == Some(Category::Place)` and calls `as_place`, then
   `Rvalue::Use(consume_by_copy_or_move(place))`. This is the key structural fact:
   **the whole nested place expression is lowered by one `as_place` call, and all the
   bounds-check code is emitted as a side effect of building that place.**
3. `push_fake_read(ForLet)` → `FakeRead(ForLet(None), _4)` (`matches/mod.rs:593`)

## Building the place

`as_place` (`as_place.rs:369`) → `as_place_builder` → `expr_as_place`. The central idea is
`PlaceBuilder` (`as_place.rs:71`): a `PlaceBase` plus a growing `Vec<PlaceElem>`.
Projections are only *accumulated*; nothing is materialized into a local until someone
calls `.to_place()`.

The recursion in `expr_as_place` for this expression:

| THIR node | `expr_as_place` arm | effect |
|---|---|---|
| `ExprKind::Scope` | `:430` | `in_scope`, recurse |
| outer `Deref` | `:446` | recurse, then `.deref()` → push `Deref` |
| outer `Index` | `:451` | → `lower_index_expression` |
| inner `Deref` | `:446` | recurse, then `.deref()` |
| inner `Index` | `:451` | → `lower_index_expression` |
| `Deref` of `a` | `:446` | recurse, then `.deref()` |
| `VarRef a` | `:464` | `PlaceBuilder::from(_1)` |

`.deref()`/`.index()`/`.field()` are thin wrappers over `project()` at `as_place.rs:308-335`.

## `lower_index_expression` — `as_place.rs:620`

This is where everything interesting happens. For each index, in this exact order:

```rust
let base_place = unpack!(block = self.expr_as_place(block, base, mutability, Some(fake_borrow_temps)));   // :634
let idx        = unpack!(block = self.as_temp(block, index_lifetime, index, Mutability::Not));            // :644
block = self.bounds_check(block, &base_place, idx, expr_span, source_info);                               // :646
if is_outermost_index { self.read_fake_borrows(...) } else { self.add_fake_borrows_of_base(...) }          // :648
block.and(base_place.index(idx))                                                                          // :660
```

Two things to note:

- `fake_borrow_temps: Option<_>` doubles as the "am I the outermost index?" flag (`:631`).
  The outer index calls with `None` → `is_outermost_index == true`; it then threads
  `Some(&mut vec)` down through `expr_as_place`, so the inner index sees `Some` and knows
  it is nested.
- The index is forced into a **fresh** temp via `as_temp` with `Mutability::Not` (`:644`),
  with the comment at `:637-642` explaining why: nothing can ever mutate it afterwards, so
  the bounds check stays valid, and Stacked Borrows retagging relies on it.

### Where `y = 13` gets interleaved

`as_temp` (`as_temp.rs:17`) pushes `StorageLive(temp)` (`as_temp.rs:105`) and *then* calls
`expr_into_dest` on the index expression. The index expression is a block, so `into.rs` →
`ast_block` → `ast_block_stmts` lowers `let y = 13;` and then the tail expr `0` into the
temp. That's precisely this sequence in `bb0`:

```
StorageLive(_5);        // as_temp.rs:105 — the index temp for the inner index
StorageLive(_6);        // let y, via expr_into_pattern
_6 = const 13_i32;
FakeRead(ForLet(None), _6);
_5 = const 0_usize;     // tail expr of the block → expr_into_dest(_5, ...)
StorageDead(_6);        // y's scope ends
```

`StorageDead(_5)` / `StorageDead(_8)` in `bb2` come from
`schedule_drop(..., DropKind::Storage)` at `as_temp.rs:114`, using
`index_lifetime = temporary_scope(thir[index].temp_scope_id)` (`as_place.rs:643`) — the
*enclosing* temporary scope, deliberately wider than necessary so the index local is still
live when the final place is read.

## `bounds_check` — `as_place.rs:726`

```rust
let slice = slice.to_place(self);                                        // :734  ← materializes the base place
let len   = self.len_of_slice_or_array(block, slice, ...);               // :737
let lt    = self.temp(bool_ty, expr_span);                               // :741
self.cfg.push_assign(block, source_info, lt,
    Rvalue::BinaryOp(BinOp::Lt, (Operand::Copy(index), len.to_copy()))); // :742
let msg = BoundsCheck { len, index: Operand::Copy(index) };              // :751
self.assert(block, Operand::Move(lt), true, msg, expr_span)              // :754
```

`len.to_copy()` is why the `Lt` reads `copy _10` while the assert message keeps `move _10`.

`self.assert` lives in `scope.rs:1756`: it starts a fresh block, emits
`TerminatorKind::Assert { unwind: UnwindAction::Continue, target: success_block }`, calls
`diverge_from` (`scope.rs:1646`) to register the block as an unwind entry point, and
returns the success block. `diverge_from` → `unwind_drops.add_entry_point` is what later
rewrites `unwind: Continue` into `unwind: bb3` and creates the shared
`bb3 (cleanup) { resume; }`.

This is also why each index lands in its own basic block: the `Assert` terminator cuts the
CFG. The chain `bb0 → bb1 → bb2` is exactly one block per bounds check plus the final block.

### Array vs. slice length — `len_of_slice_or_array`, `as_place.rs:668`

**Inner index.** Base is `(*a)`, type `[*mut [*mut u64]; 20]` — `ty::Array` (`:677`). The
length is statically known, so no locals are needed. It still pushes a `FakeRead(ForIndex)`
purely so borrowck/initialization-checking counts the array as used (`:683`, with a FIXME
questioning whether that's needed). Result:

```
FakeRead(ForIndex, (*_1));
_7 = Lt(copy _5, const 20_usize);
assert(move _7, "...", const 20_usize, copy _5) -> [success: bb1, unwind: bb3];
```

**Outer index.** Base is `*(*a)[_5]`, type `[*mut u64]` — `ty::Slice` (`:687`). Length must
be read from the pointer metadata at runtime. The fast path at `:688-697` (pass
`place.local` straight to `PtrMetadata`) requires `place.projection == [Deref]`; here the
projection is `[Deref, Index(_5), Deref]`, so it falls to the general path at `:698-708`:
take a `RawPtrKind::FakeForPtrMetadata` raw pointer to the slice place, then
`UnaryOp(PtrMetadata, …)`:

```
_9  = &raw const (fake) (*(*_1)[_5]);   // Rvalue::RawPtr, as_place.rs:705
_10 = PtrMetadata(move _9);             // as_place.rs:715
_11 = Lt(copy _8, copy _10);
assert(move _11, "...", move _10, copy _8) -> [success: bb2, unwind: bb3];
```

## The duplicated dereferences

This is the cost of `PlaceBuilder` being pure accumulation. `bounds_check` calls
`slice.to_place(self)` (`:734`), which materializes `(*(*_1)[_5])` — walking `_1`, indexing,
derefing — just to feed `PtrMetadata`. Then `lower_index_expression:660` returns
`base_place.index(idx)`, and `into.rs:859` materializes the *full* place
`(*(*(*_1)[_5])[_8])` from scratch. The intermediate pointer loads are never shared, because
at MIR-build time they aren't loads at all — they're just projection elements in a `Vec`.

The duplication becomes literal after the `Derefer` pass, which spills each
`Deref`-of-a-pointer-in-the-middle into its own local:

```
bb1: _12 = deref_copy (*_1)[_5];        // for the bounds check
     _9  = &raw const (fake) (*_12);
bb2: _13 = deref_copy (*_1)[_5];        // same value, recomputed
     _14 = deref_copy (*_13)[_8];
     _4  = copy (*_14);
```

`_12` and `_13` are identical; later optimization passes (GVN) are expected to clean that up.

## Fake borrows (why none appear here)

`lower_index_expression:648-658` exists to stop `x[1][{x = y; 2}]` from invalidating a
bounds check already performed — the doc comment at `:616-619`. The mechanism:

- Nested indices call `add_fake_borrows_of_base` (`:757`), which walks
  `base_place.iter_projections().rev()` and emits
  `Rvalue::Ref(_, BorrowKind::Fake(Shallow), …)` for every `Deref` it finds, collecting the
  temps.
- The outermost index calls `read_fake_borrows` (`:815`), pushing `FakeRead(ForIndex)` on
  each temp so they stay live across all the index expressions, making borrowck reject
  writes through those pointers.

In this example `add_fake_borrows_of_base` is reached (inner index,
`is_outermost_index == false`) but bails immediately at `:768`: it only does work
`if let ty::Slice(_) = place_ty.ty.kind()`, and the inner base `(*a)` is an *array*. The
comment at `:769-772` explains the asymmetry — for slices you can't assign to the unsized
value itself, so only the pointers leading to it need protecting; arrays are
captured/checked wholesale. So `fake_borrow_temps` is empty and `read_fake_borrows` emits
nothing. The `FakeRead(ForIndex, (*_1))` in the dump is unrelated — it comes from the array
branch of `len_of_slice_or_array`.

Also worth noting: `as_place.rs:357-368`'s warning on `as_place` is the contract that makes
all of this necessary — any user code running between place construction and use can
invalidate the bounds check or move the memory, which is exactly the `match`/index situation.

## Reproducing

```sh
mkdir -p /tmp/mirgen && cd /tmp/mirgen
cp /Users/trhance/rust/compiler/rustc_mir_build/test_ptr.rs .
RUSTC_BOOTSTRAP=1 rustc --crate-type=lib --emit=mir \
    -Zdump-mir=test -Zdump-mir-dir=/tmp/mirgen/dump test_ptr.rs
RUSTC_BOOTSTRAP=1 rustc --crate-type=lib -Zunpretty=thir-tree test_ptr.rs
```

Relevant dumps: `test_ptr.test.1-1-000.built.after.mir`,
`test_ptr.test.2-1-005.Derefer.after.mir`.
