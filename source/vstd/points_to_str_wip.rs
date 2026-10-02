// Reference snapshot of the `str` permission port, removed from `points_to_permissions.rs`.
//
// This file is NOT part of the build (it is not listed as a module in `vstd.rs`). It is kept so the
// `str` work can be restored later. It verified (as part of `points_to_permissions.rs`) with the
// build at 2009 verified, 0 errors.
//
// To restore: paste the `verus!` contents back at the end of `points_to_permissions.rs`
// (inside its `verus!` block) and add these imports there:
//
//     use super::string::StringSliceAdditionalSpecFns;
//     use super::transmute::{group_transmute_axioms, transmute_pre_points_to};
//
// (`use super::endian::*;`, already in `points_to_permissions.rs` for the integer casts, is not needed
// here.) Note that `StringSliceAdditionalSpecFns::spec_bytes` is `cfg(not(verus_verify_core))` in
// `string.rs`, so this code needs a cfg guard if the file is built under `verus_verify_core`.
//
// Design notes:
//
// * A `str` permission is `SeqPointsTo<str, PointsTo<u8>>`: one `PointsTo<u8>` per byte, plus a
//   `*mut str` pointer whose metadata is the length. No `str` is stored; the value is derived from
//   the `u8` values via `str::spec_bytes()`.
// * `is_valid()` = every byte valid AND some `&str` has exactly those bytes AND the abstract bytes
//   decode into it. `value()` is the `choose`n such `&str`.
// * Decodability is in `is_valid()` rather than `wf()` because there is no `str` extensionality
//   axiom (two `&str`s with the same `spec_bytes()` are not known to be equal), so a `choose`-based
//   `value()` could not otherwise be shown to decode. For the same reason `cast_to_str` ensures
//   `out.value().spec_bytes() == value@`, not `out.value() == target`.
// * `wf()` = `wf_basic()` and `ptr()@.metadata == len()`.
// * Proved: `is_aligned`, `bytes_decode`, `cast_to_u8_seq_pt`, `cast_to_str`.
//   Axioms: `as_untyped`, `as_u8_seq_pt` (nothing is stored to borrow).
// * Pruning results for `cast_to_str`: the `provenance_not_none`/`ptr_bounds` block (needed for the
//   `len as usize` metadata cast), `bytes_decode()`, `bytes_len()`, `typed_value_equiv`, the subrange
//   assert, and the `EncodingU8Slice::decode` / `abs_decode::<[u8]>` / `abs_decode::<str>` asserts
//   are all needed. The `value@.len() == bytes().len()` assert was not.

verus! {

/// Permission to access (possibly valid) memory containing a `str`.
/// Internally represented as a sequence of `PointsTo<u8>` permissions, one for each byte,
/// along with a `*mut str` pointer whose metadata is the length of the `str`.
///
/// There is no stored `str`: a `str` has no ghost state of its own, so its value is determined by the
/// `u8` values of the individual bytes.
impl SeqPointsTo<str, PointsTo<u8>> {
    /// The contiguous sequence of abstract bytes that this permission tracks.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        SeqPointsTo::<u8, PointsTo<u8>>::bytes_inner(self.seq_pt())
    }

    /// The `u8` value of each byte of memory.
    /// Only meaningful if every byte is valid.
    #[verifier::inline]
    pub open spec fn value_bytes(&self) -> Seq<u8> {
        Seq::new(self.len(), |i: int| self[i].value())
    }

    /// Returns `true` if the permission's associated memory is a valid `str`:
    /// every byte is valid for `u8`, and those bytes are the bytes of some `str` that
    /// the abstract bytes decode into.
    pub open spec fn is_valid(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.len() ==> #[trigger] self[i].is_valid()
        &&& exists|s: &str|
            #![auto]
            s.spec_bytes() == self.value_bytes() && abs_decode::<str>(self.bytes(), s)
    }

    /// Returns `true` if the permission's associated memory is not a valid `str`.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        !self.is_valid()
    }

    /// If the permission's associated memory is a valid `str`, returns that `str`.
    /// Otherwise, the result is meaningless.
    pub open spec fn value(&self) -> &str
        recommends
            self.is_valid(),
    {
        choose|s: &str|
            #![auto]
            s.spec_bytes() == self.value_bytes() && abs_decode::<str>(self.bytes(), s)
    }

    /// In addition to the well-formed-ness properties which must hold of every `SeqPointsTo`,
    /// the `*mut str` pointer's metadata must match the number of `PointsTo<u8>` permissions.
    /// (Validity already requires that the bytes decode into the value.)
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& self.ptr()@.metadata == self.len()
    }

    /// A `str` is always aligned (it has the same alignment as `u8`).
    pub proof fn is_aligned(tracked &self)
        ensures
            self.ptr()@.addr as int % spec_align_of_val::<str>(self.value()) as int == 0,
    {
        broadcast use layout_of_str, align_of_u8;

    }

    /// If the memory is valid, then the bytes must decode into the `str` value in memory.
    /// The number of abstract bytes is the length of the `str`.
    pub proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            self.is_valid() ==> abs_decode::<str>(self.bytes(), self.value()),
            self.bytes().len() == self.len(),
    {
        SeqPointsTo::<u8, PointsTo<u8>>::bytes_len_helper(self.seq_pt());
    }

    /// Creates a reference to a `PointsToUntyped` from a reference to a `SeqPointsTo<str, PointsTo<u8>>`,
    /// with the same address and provenance, a length of the `str` length,
    /// and the same abstract bytes.
    ///
    /// This is an axiom because the `SeqPointsTo` does not store a `PointsToUntyped` that can be borrowed.
    pub axiom fn as_untyped(tracked &self) -> (tracked raw: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            raw.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: self.ptr()@.metadata,
                },
            ),
            raw.bytes() == self.bytes(),
            raw.wf(),
    ;

    /// Casts a `SeqPointsTo<str, PointsTo<u8>>` to the `SeqPointsTo<u8, PointsTo<u8>>` for the same bytes.
    /// The sequence of permissions is unchanged; only the pointer is cast.
    pub proof fn cast_to_u8_seq_pt(tracked self) -> (tracked out: SeqPointsTo<u8, PointsTo<u8>>)
        requires
            self.wf(),
        ensures
            out.seq_pt() == self.seq_pt(),
            out.ptr() == self.ptr() as *mut u8,
            out.bytes() == self.bytes(),
            out.wf(),
    {
        broadcast use align_of_u8;

        SeqPointsTo { seq_pt: self.seq_pt, ptr: Ghost(self.ptr() as *mut u8) }
    }

    /// Like `cast_to_u8_seq_pt`, but borrows.
    ///
    /// This is an axiom because the `SeqPointsTo<str, PointsTo<u8>>` does not store a
    /// `SeqPointsTo<u8, PointsTo<u8>>` that can be borrowed.
    pub axiom fn as_u8_seq_pt(tracked &self) -> (tracked out: &SeqPointsTo<u8, PointsTo<u8>>)
        requires
            self.wf(),
        ensures
            out.seq_pt() == self.seq_pt(),
            out.ptr() == self.ptr() as *mut u8,
            out.bytes() == self.bytes(),
            out.wf(),
    ;
}

impl SeqPointsTo<u8, PointsTo<u8>> {
    /// A valid `SeqPointsTo<u8, PointsTo<u8>>` can be cast to a valid `SeqPointsTo<str, PointsTo<u8>>`
    /// when it is possible to transmute between the `[u8]` value in memory (`value`) and the
    /// given `str` value `target`, and `target` has the same bytes as `value`.
    ///
    /// The sequence of permissions and the abstract bytes remain the same;
    /// only the pointer is cast (its metadata is the length of the `str`).
    pub proof fn cast_to_str(tracked self, value: &[u8], target: &str) -> (tracked out:
        SeqPointsTo<str, PointsTo<u8>>)
        requires
            self.wf(),
            self.is_valid(),
            self.value() == value@,
            transmute_pre_points_to::<[u8], str>(value, target),
            target.spec_bytes() == value@,
        ensures
            out.seq_pt() == self.seq_pt(),
            out.ptr() == ptr_mut_from_data::<str>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: self.len() as usize,
                },
            ),
            out.bytes() == self.bytes(),
            out.is_valid(),
            out.value().spec_bytes() == value@,
            out.wf(),
    {
        broadcast use group_transmute_axioms, layout_of_slices, layout_of_str;

        if self.len() != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        self.bytes_decode();
        self.bytes_len();
        assert forall|i: int| 0 <= i < value@.len() implies #[trigger] u8::decode(
            seq![self.bytes()[i]],
            value[i],
        ) by {
            self.typed_value_equiv(i);
            assert(self.bytes().subrange(i * size_of::<u8>(), (i + 1) * size_of::<u8>())
                == seq![self.bytes()[i]]);
        }
        assert(EncodingU8Slice::decode(self.bytes(), value));
        assert(abs_decode::<[u8]>(self.bytes(), value));
        assert(abs_decode::<str>(self.bytes(), target));

        SeqPointsTo {
            seq_pt: self.seq_pt,
            ptr: Ghost(
                ptr_mut_from_data::<str>(
                    PtrData {
                        addr: self.ptr()@.addr,
                        provenance: self.ptr()@.provenance,
                        metadata: self.len() as usize,
                    },
                ),
            ),
        }
    }
}

} // verus!
