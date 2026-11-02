# Approved: no trusted specs over `PointsTo` / `PointsToUnaligned`

Approved specs from [TRUSTED_POINTS_TO_PLAN.md](TRUSTED_POINTS_TO_PLAN.md).

## `is_disjoint` (approved 2026-11-02)

`PTPhys` gets a new method:

```rust
/// Borrows the byte permission at address `addr`, which is in this permission's memory range.
proof fn borrow_byte(tracked &self, addr: int) -> (tracked b: &PointsToByte)
    requires
        self.wf_basic(),
        self.ptr()@.addr <= addr < self.ptr()@.addr + Self::size(self.ptr()@.metadata),
    ensures
        b.ptr()@.addr == addr,
;
```

- `PointsToByte::is_disjoint_byte` becomes the axiom, with its current spec.
- `PointsToByte`'s generic `is_disjoint` is verified from `other.borrow_byte` and `is_disjoint_byte`, with its spec unchanged.
- `PTPhys` stays sealed.

## Structural axioms (approved 2026-11-02)

These stay trusted, with their specs unchanged:
`PointsToUnaligned::from_raw_parts_ref`, `PointsToUnaligned::from_raw_parts_mut`, `PointsTo::from_unaligned_mut`.
