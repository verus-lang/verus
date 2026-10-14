// Reference snapshot of the `wrap_mut` work, removed from `points_to_permissions.rs`.
//
// This file is NOT part of the build (it is not listed as a module in `vstd.rs`). It is kept so the
// work can be restored later, once the soundness of `wrap_mut` has been reviewed. It verified (as
// part of `points_to_permissions.rs`) with the build at 1967 verified, 0 errors.
//
// What it contains:
//
// * `wrap_mut`: a private axiom on the generic `impl<T: ?Sized, PointsToPerm> SeqPointsTo<T,
//   PointsToPerm>` block. It wraps a `&'a mut Seq<PointsToPerm>` into a `&'a mut SeqPointsTo` with
//   pointer `ptr` -- the `&mut` analogue of the `shr_ref_struct_wrap` builtin, which Verus doesn't
//   have. `SeqPointsTo`'s only other field, `ptr`, is ghost, so any change to it through the result
//   is discarded; the final sequence flows back into `s`.
// * The proof body of `SeqPointsTo<T, PointsTo<T>>::subrange_mut`, which uses `wrap_mut` together
//   with the existing `Seq::tracked_borrow_subrange_mut`. The spec of `subrange_mut` was not
//   changed, so restoring only means swapping `axiom fn` back to `proof fn` and adding the body.
// * `PointsToUntyped::split_mut` also uses `wrap_mut` (with `Seq::tracked_split_borrow_mut`). It is
//   still in `points_to_permissions.rs`, commented out in place right after `split_ref`; uncomment
//   it to restore.
//
// To restore:
//
// 1. Paste `wrap_mut` (below) at the end of the generic
//    `impl<T, PointsToPerm> SeqPointsTo<T, PointsToPerm> where T: ?Sized, PointsToPerm:
//    PointsToProperties + FixedSize` block (after `spec_index`).
// 2. In `impl<T> SeqPointsTo<T, PointsTo<T>>`, change `pub axiom fn subrange_mut` to
//    `pub proof fn subrange_mut`, replace the trailing `;` after its `ensures` with the body below.
// 3. Uncomment `PointsToUntyped::split_mut`.
// 4. Update `POINTS_TO_AXIOMS.md` (replace the `subrange_mut` axiom entry with `wrap_mut`),
//    `POINTS_TO_COMPARISON.md`, `POINTS_TO_MIGRATION.md` and `PORTING_STATUS.md`.
//
// Soundness considerations to review:
//
// * `wrap_mut` is generic, so it applies to every `SeqPointsTo<T, PointsToPerm>`, including
//   `PointsToUntyped`. Its requires are exactly `wf_basic`'s conditions on the wrapped value, and it
//   ensures nothing about the type-specific `wf` (alignment, metadata), which callers prove.
// * It is private (no `pub`), so only code in `points_to_permissions.rs` can use it.
// * The `final(r)` clause is conditioned on `final(r).ptr() == ptr`, since the ghost pointer could
//   be changed through `r`.

verus! {

// ---- 1. In the generic `impl<T, PointsToPerm> SeqPointsTo<T, PointsToPerm>` block ----

    /// Wraps a mutable borrow of a sequence of permissions into a mutable borrow of a
    /// `SeqPointsTo` with pointer `ptr`, provided that the permissions and `ptr` satisfy the
    /// conditions of `wf_basic`. The final sequence of permissions flows back into `s`;
    /// any change to the (ghost) pointer through the result is discarded.
    ///
    /// This is the `&mut` analogue of `shr_ref_struct_wrap` for `SeqPointsTo`, whose only other
    /// field is ghost. It's an axiom because Verus has no `&mut` version of that builtin.
    axiom fn wrap_mut<'a>(tracked s: &'a mut Seq<PointsToPerm>, ptr: *mut T) -> (tracked r:
        &'a mut Self)
        requires
            forall|i: int|
                #![trigger s[i].ptr()@.provenance]
                #![trigger s[i].ptr()@.addr]
                #![trigger s[i].wf_basic()]
                0 <= i < s.len() ==> {
                    &&& s[i].ptr()@.provenance == ptr@.provenance
                    &&& s[i].ptr()@.addr == ptr@.addr + i * PointsToPerm::const_size()
                    &&& s[i].wf_basic()
                },
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
        ensures
            r.seq_pt() == *old(s),
            r.ptr() == ptr,
            r.wf_basic(),
            *final(s) == final(r).seq_pt(),
            final(r).wf_basic() && final(r).ptr() == ptr ==> forall|i: int|
                #![trigger (*final(s))[i]]
                0 <= i < (*final(s)).len() ==> {
                    &&& (*final(s))[i].ptr()@.provenance == ptr@.provenance
                    &&& (*final(s))[i].ptr()@.addr == ptr@.addr + i * PointsToPerm::const_size()
                    &&& (*final(s))[i].wf_basic()
                },
    ;

// ---- 2. Body of `SeqPointsTo<T, PointsTo<T>>::subrange_mut` (spec unchanged) ----

    // pub proof fn subrange_mut(tracked &mut self, i: nat, j: nat) -> (tracked r: &mut Self)
    //     requires ... ensures ...   (unchanged from the axiom)
    {
        let ghost old_self = *self;
        let ghost self_ref = self;
        let ghost sub_ptr = ptr_mut_from_data::<T>(
            PtrData {
                addr: ((old_self.ptr()@.addr + i * size_of::<T>()) as usize),
                provenance: old_self.ptr()@.provenance,
                metadata: (),
            },
        );
        // `sub_ptr` is non-null, in bounds and aligned (same reasoning as in `subrange`)
        if old_self.len() != 0 && size_of::<T>() != 0 {
            assert(old_self.len() * size_of::<T>() != 0) by (nonlinear_arith)
                requires
                    old_self.len() != 0,
                    size_of::<T>() != 0,
            ;
            self.provenance_not_none();
            self.ptr_bounds();
            assert(i * size_of::<T>() <= old_self.len() * size_of::<T>()) by (nonlinear_arith)
                requires
                    i <= old_self.len(),
            ;
            assert((old_self.ptr()@.addr + i * size_of::<T>()) as nat % align_of::<T>() == 0) by {
                broadcast use
                    crate::vstd::arithmetic::div_mod::lemma_mul_mod_noop_right,
                    crate::vstd::arithmetic::div_mod::lemma_add_mod_noop,
                ;

            }
        }

        let tracked s = self.seq_pt.tracked_borrow_subrange_mut(i as int, j as int);

        // Each element of `s` sits at the expected offset from `sub_ptr`
        assert forall|k: int| 0 <= k < s.len() implies {
            &&& #[trigger] s[k].ptr()@.provenance == sub_ptr@.provenance
            &&& s[k].ptr()@.addr == sub_ptr@.addr + k * size_of::<T>()
            &&& s[k].wf_basic()
        } by {
            assert(old_self.ptr()@.addr + (k + i) * size_of::<T>() == old_self.ptr()@.addr + i
                * size_of::<T>() + k * size_of::<T>()) by (nonlinear_arith);
        }
        let tracked r = Self::wrap_mut(s, sub_ptr);
        let ghost r_ref = r;

        // If `r` stays well-formed with the same pointer and length, so does `self`
        if final(r_ref).wf() && final(r_ref).ptr() == r_ref.ptr() && final(r_ref).len()
            == r_ref.len() {
            let ghost new_self = *final(self_ref);
            assert forall|k: int| 0 <= k < new_self.len() implies {
                &&& #[trigger] new_self[k].wf_basic()
                &&& new_self[k].ptr()@.addr == new_self.ptr()@.addr + k * size_of::<T>()
                &&& new_self[k].ptr()@.provenance == new_self.ptr()@.provenance
            } by {
                if i <= k < j {
                    assert(old_self.ptr()@.addr + i * size_of::<T>() + (k - i) * size_of::<T>()
                        == old_self.ptr()@.addr + k * size_of::<T>()) by (nonlinear_arith);
                }
            }
        }
        r
    }

} // verus!
