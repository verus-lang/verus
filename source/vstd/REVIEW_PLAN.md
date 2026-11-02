# Review plan: trusted-`PointsTo` refactor and `Tracked<&T>`

Uncommitted changes in both repos, trusted code first.
What to look for in each: the "For review" sections of [TRUSTED_POINTS_TO_PLAN.md](TRUSTED_POINTS_TO_PLAN.md#for-review)
and [TRACKED_REF_PLAN.md](TRACKED_REF_PLAN.md#for-review); the trusted items are in [TRACKED_REF_TRUSTED_REVIEW.md](TRACKED_REF_TRUSTED_REVIEW.md).

## vstd

1. **Trusted reference and pointer specs**
   - [raw_ptr/ptr_specs.rs](raw_ptr/ptr_specs.rs)
   - [raw_ptr/shared_reference.rs](raw_ptr/shared_reference.rs)
2. **Trusted permission model**
   - [raw_ptr/points_to_model.rs](raw_ptr/points_to_model.rs)
   - [raw_ptr/points_to_structs.rs](raw_ptr/points_to_structs.rs) (new)
3. **Verified wrappers and operations**
   - [raw_ptr/ptr_verified_specs.rs](raw_ptr/ptr_verified_specs.rs) (new)
   - [raw_ptr/points_to_ops.rs](raw_ptr/points_to_ops.rs)
   - [raw_ptr/points_to_collections.rs](raw_ptr/points_to_collections.rs)
4. **Module wiring**
   - [raw_ptr/mod.rs](raw_ptr/mod.rs)
5. **Docs**
   - [TRACKED_REF_PLAN.md](TRACKED_REF_PLAN.md)
   - [TRUSTED_POINTS_TO_PLAN.md](TRUSTED_POINTS_TO_PLAN.md)

## rustlib (`/Users/estang/Documents/Verus/rustlib`)

1. **`str` trusted specs and wrappers (approved file)**
   - `proofs/str.rs`
2. **Reference-to-pointer casts and their callers in `[T]` / `str` methods**
   - `verified-1.95.0/core/src/slice/mod.rs`
   - `verified-1.95.0/core/src/str/mod.rs`
3. **`SliceIndex` / `SliceIndexVerus`**
   - `verified-1.95.0/core/src/slice/index.rs`
   - `verified-1.95.0/core/src/str/traits.rs`
4. **`str` algorithms**
   - `verified-1.95.0/core/src/str/pattern.rs`
   - `verified-1.95.0/core/src/str/validations.rs`
5. **`Box`**
   - `verified-1.95.0/alloc/src/boxed.rs`
