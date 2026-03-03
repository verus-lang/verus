use super::super::modes::*;
use super::super::prelude::*;
use super::map::*;

verus! {

broadcast use super::super::group_vstd_default;

pub open spec fn seq_to_map<V>(s: Seq<V>, off: int) -> Map<int, V> {
    Map::new(|i: int| off <= i < off + s.len(), |i: int| s[i - off])
}

/** An implementation of a resource for owning a subrange of a sequence.

`GhostSeqAuth<T>` represents authoritative ownership of the entire
sequence, and `GhostSubseq<T>` represents client ownership of some
subrange of that sequence.  Updating the authoritative `GhostSeqAuth<T>`
requires a `GhostSubseq<T>` covering the relevant positions.
`GhostSubseq<K, T>`s can be combined or split.

### Example

```
fn example_use() {
    let tracked (mut auth, mut sub) = GhostSeqAuth::new(seq![0u64, 1u64, 2u64, 3u64, 4u64, 5u64], 0);

    // Split the subsequence into a multiple subseqs.
    let tracked sub2 = sub.split(3);

    // In general, we might need to call agree() to establish the fact that
    // a subseq has the same values as the auth seq.  Here, Verus doesn't need
    // agree because it can track where both the auth and subseq came from.
    proof { sub.agree(&auth); }
    proof { sub2.agree(&auth); }

    assert(sub[0] == auth[0]);
    assert(sub2[0] == auth[3]);

    // Update the sequence using ownership of subseqs.
    // The update() method on GhostSubseq updates the entire subrange.
    proof { sub.update(&mut auth, seq![10u64, 11u64, 12u64]); }
    assert(auth[0] == 10u64);
    assert(sub[0] == 10u64);

    // The update_subrange_with() method on GhostSeqAuth allows updating
    // arbitrary parts of a subseq's subrange.
    proof { auth.update_subrange_with(&mut sub2, 4, seq![24u64, 25u64]); }
    assert(auth[3] == 3u64);
    assert(auth[4] == 24u64);
    assert(sub2[1] == 24u64);

    // Not shown in this simple example is the main use case of this resource:
    // maintaining an invariant between GhostSeqAuth<V> and some exec-mode
    // shared state with a seq view (e.g., the contents of a file or a disk),
    // which states that the Seq<V> view of GhostSeqAuth<V> is the same as the
    // view of the state (e.g., file or disk contents), and then handing out a
    // GhostSubseq<V> to different clients that might need to operate on
    // different subranges of the shared state (e.g., different concurrent
    // transactions that operate on different parts of the file/disk).
}
```
*/

pub tracked struct GhostSeqAuth<V> {
    ghost off: nat,
    ghost len: nat,
    auth: GhostMapAuth<int, V>,
}

pub tracked struct GhostSubseq<V> {
    ghost off: nat,
    ghost len: nat,
    frac: GhostSubmap<int, V>,
}

impl<V> GhostSeqAuth<V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.auth@.dom() =~= Set::new(|i: int| self.off <= i < self.off + self.len)
    }

    pub closed spec fn id(self) -> int {
        self.auth.id()
    }

    pub closed spec fn view(self) -> Seq<V> {
        Seq::new(self.len, |i: int| self.auth@[self.off + i])
    }

    pub open spec fn len(self) -> nat {
        self@.len()
    }

    pub open spec fn spec_index(self, idx: int) -> V
        recommends
            0 <= idx < self.len(),
    {
        self@[idx]
    }

    pub closed spec fn off(self) -> nat {
        self.off
    }

    pub open spec fn subrange_abs(self, start_inclusive: int, end_exclusive: int) -> Seq<V>
        recommends
            self.off() <= start_inclusive <= end_exclusive <= self.off() + self@.len(),
    {
        self@.subrange(start_inclusive - self.off(), end_exclusive - self.off())
    }

    pub proof fn new(s: Seq<V>, off: nat) -> (tracked result: (GhostSeqAuth<V>, GhostSubseq<V>))
        ensures
            result.0.off() == off,
            result.0@ =~= s,
            result.1.id() == result.0.id(),
            result.1.off() == off,
            result.1@ =~= s,
    {
        let tracked (mauth, mfrac) = GhostMapAuth::<int, V>::new(seq_to_map(s, off as int));
        let tracked auth = GhostSeqAuth { off: off, len: s.len(), auth: mauth };
        let tracked frac = GhostSubseq { off: off, len: s.len(), frac: mfrac };
        (auth, frac)
    }

    pub proof fn dummy() -> (tracked result: Self) {
        let tracked (auth, subseq) = Self::new(Seq::empty(), 0);
        auth
    }

    pub proof fn agree(tracked self: &GhostSeqAuth<V>, tracked frac: &GhostSubseq<V>)
        requires
            self.id() == frac.id(),
        ensures
            frac@.len() > 0 ==> {
                &&& frac@ =~= self@.subrange(
                    frac.off() as int - self.off(),
                    frac.off() - self.off() + frac@.len() as int,
                )
                &&& frac.off() >= self.off()
                &&& frac.off() + frac@.len() <= self.off() + self@.len()
            },
    {
        frac.agree(self)
    }

    pub proof fn update_subrange_with(
        tracked self: &mut GhostSeqAuth<V>,
        tracked frac: &mut GhostSubseq<V>,
        off: int,
        v: Seq<V>,
    )
        requires
            old(self).id() == old(frac).id(),
            old(frac).off() <= off,
            off + v.len() <= old(frac).off() + old(frac)@.len(),
        ensures
            self.id() == old(self).id(),
            frac.id() == old(frac).id(),
            frac.off() == old(frac).off(),
            self@ =~= old(self)@.update_subrange_with(off - self.off(), v),
            frac@ =~= old(frac)@.update_subrange_with(off - frac.off(), v),
            self.off() == old(self).off(),
            frac.off() == old(frac).off(),
    {
        let tracked mut mid = frac.split(off - frac.off());
        let tracked mut end = mid.split(v.len() as int);
        mid.update(self, v);
        frac.combine(mid);
        frac.combine(end);
    }
}

impl<V> GhostSubseq<V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.frac@.dom() =~= Set::new(|i: int| self.off <= i < self.off + self.len)
    }

    pub closed spec fn view(self) -> Seq<V> {
        Seq::new(self.len, |i: int| self.frac@[self.off + i])
    }

    pub open spec fn len(self) -> nat {
        self@.len()
    }

    pub open spec fn spec_index(self, idx: int) -> V
        recommends
            0 <= idx < self.len(),
    {
        self@[idx]
    }

    pub open spec fn subrange_abs(self, start_inclusive: int, end_exclusive: int) -> Seq<V>
        recommends
            self.off() <= start_inclusive <= end_exclusive <= self.off() + self@.len(),
    {
        self@.subrange(start_inclusive - self.off(), end_exclusive - self.off())
    }

    pub closed spec fn off(self) -> nat {
        self.off
    }

    pub closed spec fn id(self) -> int {
        self.frac.id()
    }

    pub proof fn agree(tracked self: &GhostSubseq<V>, tracked auth: &GhostSeqAuth<V>)
        requires
            self.id() == auth.id(),
        ensures
            self@.len() > 0 ==> {
                &&& self@ =~= auth@.subrange(
                    self.off() as int - auth.off(),
                    self.off() - auth.off() + self@.len() as int,
                )
                &&& self.off() >= auth.off()
                &&& self.off() + self@.len() <= auth.off() + auth@.len()
            },
    {
        use_type_invariant(self);
        use_type_invariant(auth);

        self.frac.agree(&auth.auth);

        if self@.len() > 0 {
            assert(self.frac@.contains_key(self.off as int));
            assert(auth.auth@.contains_key(self.off as int));

            assert(self.frac@.contains_key(self.off + self.len - 1));
            assert(auth.auth@.contains_key(self.off + self.len - 1));
            assert(self.off - auth.off + self.len - 1 < auth@.len());

            assert forall|i: int| 0 <= i < self.len implies #[trigger] self.frac@[self.off + i]
                == auth@[self.off - auth.off + i] by {
                assert(self.frac@.contains_key(self.off + i));
                assert(auth.auth@.contains_key(self.off + i));
            };
        }
    }

    pub proof fn agree_map(tracked self: &GhostSubseq<V>, tracked auth: &GhostMapAuth<int, V>)
        requires
            self.id() == auth.id(),
        ensures
            forall|i|
                0 <= i < self@.len() ==> #[trigger] auth@.contains_key(self.off() + i)
                    && auth@[self.off() + i] == self@[i],
    {
        use_type_invariant(self);

        self.frac.agree(&auth);

        assert forall|i: int| 0 <= i < self.len implies #[trigger] auth@.contains_key(self.off + i)
            && self.frac@[self.off + i] == auth@[self.off + i] by {
            assert(self.frac@.contains_key(self.off + i));
        };
    }

    pub proof fn update(
        tracked self: &mut GhostSubseq<V>,
        tracked auth: &mut GhostSeqAuth<V>,
        v: Seq<V>,
    )
        requires
            old(self).id() == old(auth).id(),
            v.len() == old(self)@.len(),
        ensures
            self.id() == auth.id(),
            self.off() == old(self).off(),
            auth.id() == old(auth).id(),
            self@ =~= v,
            auth@ =~= old(auth)@.update_subrange_with(self.off() - auth.off(), v),
            self.off() == old(self).off(),
            auth.off() == old(auth).off(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&*auth);

        self.update_map(&mut auth.auth, v);
    }

    pub proof fn update_map(
        tracked self: &mut GhostSubseq<V>,
        tracked auth: &mut GhostMapAuth<int, V>,
        v: Seq<V>,
    )
        requires
            old(self).id() == old(auth).id(),
            v.len() == old(self)@.len(),
        ensures
            self.id() == auth.id(),
            self.off() == old(self).off(),
            auth.id() == old(auth).id(),
            self@ =~= v,
            auth@ =~= Map::new(
                |i: int| old(auth)@.contains_key(i),
                |i: int|
                    if self.off() <= i < self.off() + v.len() {
                        v[i - self.off()]
                    } else {
                        old(auth)@[i]
                    },
            ),
    {
        use_type_invariant(&*self);

        let vmap = seq_to_map(v, self.off as int);
        assert(self.frac@.dom() == vmap.dom());
        self.frac.agree(auth);
        self.frac.update(auth, vmap);
    }

    pub proof fn split(tracked self: &mut GhostSubseq<V>, n: int) -> (tracked result: GhostSubseq<
        V,
    >)
        requires
            0 <= n <= old(self)@.len(),
        ensures
            self.id() == old(self).id(),
            self.off() == old(self).off(),
            result.id() == self.id(),
            result.off() == old(self).off() + n,
            self@ =~= old(self)@.subrange(0, n),
            result@ =~= old(self)@.subrange(n, old(self)@.len() as int),
    {
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);

        use_type_invariant(&mself);
        let tracked mut mselffrac = mself.frac;

        let tracked mfrac = mselffrac.split(
            Set::new(|i: int| mself.off + n <= i < mself.off + mself.len),
        );
        let tracked result = GhostSubseq {
            off: (mself.off + n) as nat,
            len: (mself.len - n) as nat,
            frac: mfrac,
        };

        *self = Self { off: mself.off, len: n as nat, frac: mselffrac };
        result
    }

    pub proof fn combine(tracked self: &mut GhostSubseq<V>, tracked r: GhostSubseq<V>)
        requires
            r.id() == old(self).id(),
            r.off() == old(self).off() + old(self)@.len(),
        ensures
            self.id() == old(self).id(),
            self@ =~= old(self)@ + r@,
            self.off() == old(self).off(),
    {
        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);

        use_type_invariant(&mself);
        use_type_invariant(&r);
        let tracked mut mselffrac = mself.frac;

        mselffrac.combine(r.frac);
        *self = Self { frac: mselffrac, off: mself.off, len: mself.len + r.len };
    }

    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSubseq<V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self.off() == old(self).off(),
            self@ == old(self)@,
            self@.len() == 0 || other@.len() == 0 || self.off() + self@.len() <= other.off()
                || other.off() + other@.len() <= self.off(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);

        self.frac.disjoint(&other.frac);
        assert(self@.len() == 0 || self.frac@.contains_key(self.off() as int));
        assert(other@.len() == 0 || other.frac@.contains_key(other.off() as int));
    }

    pub proof fn dummy() -> (tracked result: Self) {
        let tracked (auth, subseq) = GhostSeqAuth::<V>::new(Seq::empty(), 0);
        subseq
    }

    // Helper to lift GhostSubmap into GhostSubseq.
    pub proof fn new(off: nat, len: nat, tracked f: GhostSubmap<int, V>) -> (tracked result:
        GhostSubseq<V>)
        requires
            f@.dom() == Set::new(|i: int| off <= i < off + len),
        ensures
            result.id() == f.id(),
            result.off() == off,
            result@ == Seq::new(len, |i| f@[off + i]),
    {
        GhostSubseq { off: off, len: len, frac: f }
    }
}

} // verus!
