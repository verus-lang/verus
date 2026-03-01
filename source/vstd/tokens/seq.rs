use super::super::modes::*;
use super::super::prelude::*;
use super::super::gset::lemma_gset_ext_equal;
use super::super::iset::{lemma_iset_difference, lemma_iset_ext_equal};
use super::map::*;
use super::super::set::lemma_set_generic_difference;

verus! {

broadcast use super::super::group_vstd_default;

pub open spec fn seq_to_map<V>(s: Seq<V>, off: int) -> IMap<int, V> {
    IMap::new(|i: int| off <= i < off + s.len(), |i: int| s[i - off])
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

pub struct GhostSeqAuth<V> {
    ghost off: nat,
    ghost len: nat,
    auth: GhostMapAuth<int, V>,
}

pub struct GhostSubseq<V> {
    ghost off: nat,
    ghost len: nat,
    frac: GhostSubmap<int, V>,
}

impl<V> GhostSeqAuth<V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.auth@.dom() =~= ISet::new(|i: int| self.off <= i < self.off + self.len)
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
        &&& self.frac@.dom() =~= ISet::new(|i: int| self.off <= i < self.off + self.len)
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
            let self_dom = ISet::new(|i: int| self.off <= i < self.off + self.len);
            let auth_dom = ISet::new(|i: int| auth.off <= i < auth.off + auth.len);
            assert(self.frac@.dom() =~= self_dom);
            assert(auth.auth@.dom() =~= auth_dom);
            lemma_iset_ext_equal(self.frac@.dom(), self_dom);
            lemma_iset_ext_equal(auth.auth@.dom(), auth_dom);
            super::super::iset::lemma_iset_new(|i: int| self.off <= i < self.off + self.len, self.off as int);
            assert(self_dom.contains(self.off as int));
            assert(self.frac@.dom().contains(self.off as int));
            assert(self.frac@.contains_key(self.off as int));
            assert(auth.auth@.contains_key(self.off as int));
            assert(auth_dom.contains(self.off as int));
            super::super::iset::lemma_iset_new(
                |i: int| auth.off <= i < auth.off + auth.len,
                self.off as int,
            );
            assert(auth.off <= self.off as int);
            assert(self.off >= auth.off);

            super::super::iset::lemma_iset_new(
                |i: int| self.off <= i < self.off + self.len,
                self.off + self.len - 1,
            );
            assert(self_dom.contains(self.off + self.len - 1));
            assert(self.frac@.dom().contains(self.off + self.len - 1));
            assert(self.frac@.contains_key(self.off + self.len - 1));
            assert(auth.auth@.contains_key(self.off + self.len - 1));
            assert(auth_dom.contains(self.off + self.len - 1));
            assert(self.off - auth.off + self.len - 1 < auth@.len());
            assert(self.off + self.len <= auth.off + auth@.len());

            assert forall|i: int| 0 <= i < self.len implies #[trigger] self.frac@[self.off + i]
                == auth@[self.off - auth.off + i] by {
                super::super::iset::lemma_iset_new(
                    |ii: int| self.off <= ii < self.off + self.len,
                    self.off + i,
                );
                assert(self_dom.contains(self.off + i));
                assert(self.frac@.dom().contains(self.off + i));
                assert(self.frac@.contains_key(self.off + i));
                assert(auth.auth@.contains_key(self.off + i));
                assert(auth_dom.contains(self.off + i));
                super::super::iset::lemma_iset_new(
                    |ii: int| auth.off <= ii < auth.off + auth.len,
                    self.off + i,
                );
                assert(0 <= self.off - auth.off + i);
                assert(self.off - auth.off + i < auth@.len());
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
        let self_dom = ISet::new(|i: int| self.off <= i < self.off + self.len);
        assert(self.frac@.dom() =~= self_dom);
        lemma_iset_ext_equal(self.frac@.dom(), self_dom);

        assert forall|i: int| 0 <= i < self.len implies #[trigger] auth@.contains_key(self.off + i)
            && self.frac@[self.off + i] == auth@[self.off + i] by {
            super::super::iset::lemma_iset_new(
                |ii: int| self.off <= ii < self.off + self.len,
                self.off + i,
            );
            assert(self_dom.contains(self.off + i));
            assert(self.frac@.dom().contains(self.off + i));
            assert(self.frac@.contains_key(self.off + i));
        };
        assert forall|i: int|
            0 <= i < self@.len() implies #[trigger] auth@.contains_key(self.off() + i) by {
        }
        assert forall|i: int| 0 <= i < self@.len() implies auth@[self.off() + i] == self@[i] by {
            assert(0 <= i < self.len);
            assert(auth@.contains_key(self.off + i) && self.frac@[self.off + i] == auth@[self.off + i]);
            assert(self@[i] == self.frac@[self.off + i]);
        }
        assert forall|i: int| 0 <= i < self@.len() implies #[trigger] auth@.contains_key(
            self.off() + i,
        ) && auth@[self.off() + i] == self@[i] by {
        }
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
        self.agree(auth);

        let tracked mut mself = GhostSubseq::<V>::dummy();
        tracked_swap(self, &mut mself);
        let tracked mut mauth = GhostSeqAuth::<V>::dummy();
        tracked_swap(auth, &mut mauth);
        use_type_invariant(&mauth);

        let off = mauth.off;
        let len = mauth.len;
        let tracked mut map_auth = mauth.auth;
        let old_map = map_auth@;
        mself.update_map(&mut map_auth, v);

        let full = ISet::new(|i: int| off <= i < off + len);
        assert(old_map.dom() =~= full);
        super::super::map::lemma_infinite_new_ensures(
            |i: int| old_map.contains_key(i),
            |i: int|
                if mself.off() <= i < mself.off() + v.len() {
                    v[i - mself.off()]
                } else {
                    old_map[i]
                },
        );
        let rhs_map = IMap::new(
            |i: int| old_map.contains_key(i),
            |i: int|
                if mself.off() <= i < mself.off() + v.len() {
                    v[i - mself.off()]
                } else {
                    old_map[i]
                },
        );
        assert(map_auth@ =~= rhs_map);
        super::super::map::lemma_imap_ext_equal(map_auth@, rhs_map);
        assert(rhs_map.dom() =~= old_map.dom()) by {
            assert forall|i: int| rhs_map.dom().contains(i) == old_map.dom().contains(i) by {
                assert(rhs_map.dom().contains(i) == old_map.contains_key(i));
                assert(old_map.contains_key(i) == old_map.dom().contains(i));
            }
            super::super::iset::lemma_iset_ext_equal(rhs_map.dom(), old_map.dom());
        }
        assert(map_auth@.dom() =~= rhs_map.dom());
        super::super::iset::lemma_iset_ext_equal(map_auth@.dom(), rhs_map.dom());
        assert(map_auth@.dom() =~= old_map.dom());
        super::super::iset::lemma_iset_ext_equal(map_auth@.dom(), old_map.dom());
        assert(map_auth@.dom() =~= full);

        let tracked nauth = GhostSeqAuth { off: off, len: len, auth: map_auth };
        *auth = nauth;
        *self = mself;

        assert(self@ =~= v);
        let rel = self.off() - auth.off();
        assert(auth@.len() == old(auth)@.update_subrange_with(rel, v).len());
        assert forall|i: int| 0 <= i < auth@.len() implies auth@[i] == old(auth)@.update_subrange_with(rel, v)[i] by {
            let abs = auth.off() + i;
            assert(auth@[i] == auth.auth@[abs]);
            assert(old(auth)@[i] == old_map[abs]);
            super::super::iset::lemma_iset_new(|ii: int| off <= ii < off + len, abs);
            assert(0 <= abs - off < len);
            assert(abs == off + (abs - off));
            assert(auth.auth@.dom() =~= full);
            super::super::iset::lemma_iset_ext_equal(auth.auth@.dom(), full);
            assert(auth.auth@.dom().contains(abs));
            assert(auth.auth@.contains_key(abs));
            super::super::map::lemma_imap_ext_equal(auth.auth@, rhs_map);
            assert(auth.auth@[abs] == rhs_map[abs]);
            if self.off() <= abs < self.off() + v.len() {
                assert(rel <= i < rel + v.len());
                assert(i - rel == abs - self.off());
                assert(rhs_map[abs] == v[abs - self.off()]);
                assert(old(auth)@.update_subrange_with(rel, v)[i] == v[i - rel]);
            } else {
                assert(!(rel <= i < rel + v.len()));
                assert(rhs_map[abs] == old_map[abs]);
                assert(old(auth)@.update_subrange_with(rel, v)[i] == old(auth)@[i]);
            }
        }
        assert(auth@ =~= old(auth)@.update_subrange_with(rel, v));
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
            auth@ =~= IMap::new(
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
        assert(self.frac@.dom() =~= vmap.dom());
        self.frac.agree(auth);
        assert(self.frac@ <= auth@);
        self.frac.update(auth, vmap);
        old(self).frac@.lemma_union_prefer_right(vmap);
        old(auth)@.lemma_union_prefer_right(vmap);
        assert(self.frac@ == old(self).frac@.union_prefer_right(vmap));
        assert(auth@ == old(auth)@.union_prefer_right(vmap));

        assert(self@.len() == v.len());
        assert forall|i: int| 0 <= i < v.len() implies self@[i] == v[i] by {
            let k = self.off + i;
            super::super::iset::lemma_iset_new(|ii: int| self.off <= ii < self.off + v.len(), k);
            assert(vmap.dom().contains(k));
            assert((old(self).frac@.dom().union(vmap.dom())).contains(k));
            assert((old(self).frac@.union_prefer_right(vmap)).dom().contains(k));
            assert((old(self).frac@.union_prefer_right(vmap))[k] == vmap[k]);
            assert(self.frac@[k] == (old(self).frac@.union_prefer_right(vmap))[k]);
            assert(self.frac@[k] == vmap[k]);
            assert(self@[i] == self.frac@[k]);
            assert(vmap[k] == v[i]);
        }
        assert(self@ =~= v);

        let rhs = IMap::new(
            |i: int| old(auth)@.contains_key(i),
            |i: int|
                if self.off() <= i < self.off() + v.len() {
                    v[i - self.off()]
                } else {
                    old(auth)@[i]
                },
        );
        super::super::map::lemma_imap_ext_equal(auth@, rhs);
        assert(auth@.dom() =~= rhs.dom()) by {
            assert forall|i: int| auth@.dom().contains(i) == rhs.dom().contains(i) by {
                super::super::map::lemma_infinite_new_ensures(
                    |ii: int| old(auth)@.contains_key(ii),
                    |ii: int|
                        if self.off() <= ii < self.off() + v.len() {
                            v[ii - self.off()]
                        } else {
                            old(auth)@[ii]
                        },
                );
                assert(vmap.dom().contains(i) ==> old(auth)@.dom().contains(i));
                assert((old(auth)@.union_prefer_right(vmap)).dom().contains(i) == old(auth)@.dom().contains(i));
                assert(auth@.dom().contains(i) == (old(auth)@.union_prefer_right(vmap)).dom().contains(i));
                assert(old(auth)@.contains_key(i) == old(auth)@.dom().contains(i));
                assert(rhs.dom().contains(i) == old(auth)@.contains_key(i));
            }
            super::super::iset::lemma_iset_ext_equal(auth@.dom(), rhs.dom());
        }
        assert forall|i: int| auth@.dom().contains(i) implies auth@[i] == rhs[i] by {
            super::super::iset::lemma_iset_new(|ii: int| self.off <= ii < self.off + v.len(), i);
            super::super::map::lemma_infinite_new_ensures(
                |ii: int| old(auth)@.contains_key(ii),
                |ii: int|
                    if self.off() <= ii < self.off() + v.len() {
                        v[ii - self.off()]
                    } else {
                        old(auth)@[ii]
                    },
            );
            assert(auth@.contains_key(i));
            if self.off() <= i < self.off() + v.len() {
                assert(vmap.dom().contains(i));
                assert((old(auth)@.union_prefer_right(vmap))[i] == vmap[i]);
                assert(vmap[i] == v[i - self.off()]);
                assert(auth@[i] == v[i - self.off()]);
                assert(rhs[i] == v[i - self.off()]);
            } else {
                assert(!vmap.dom().contains(i));
                assert((old(auth)@.union_prefer_right(vmap))[i] == old(auth)@[i]);
                assert(auth@[i] == old(auth)@[i]);
                assert(rhs[i] == old(auth)@[i]);
            }
        }
        assert(auth@ =~= rhs);
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
        assert(mselffrac@ == mself.frac@);
        let olddom = mselffrac@.dom();
        let s_raw = ISet::new(|i: int| mself.off + n <= i < mself.off + mself.len);
        let s = olddom.intersect(s_raw);
        assert(s <= olddom) by {
            assert forall|i: int| s.contains(i) implies olddom.contains(i) by {
                super::super::iset::lemma_iset_intersect(olddom, s_raw, i);
                assert(s.contains(i));
            }
        }
        let tracked mfrac = mselffrac.split_with_olddom(s, olddom);
        super::super::iset::lemma_iset_ext_equal_eq(mfrac@.dom(), s);
        assert(mfrac@.dom() =~= s);
        let full = ISet::new(|i: int| mself.off <= i < mself.off + mself.len);
        assert(olddom =~= full);
        super::super::iset::lemma_iset_ext_equal(olddom, full);
        assert forall|i: int| s.contains(i) == s_raw.contains(i) by {
            super::super::iset::lemma_iset_intersect(olddom, s_raw, i);
            super::super::iset::lemma_iset_new(|ii: int| mself.off + n <= ii < mself.off + mself.len, i);
            super::super::iset::lemma_iset_new(|ii: int| mself.off <= ii < mself.off + mself.len, i);
            if s_raw.contains(i) {
                assert(full.contains(i));
                assert(olddom.contains(i));
                assert(s.contains(i));
            }
        }
        super::super::iset::lemma_iset_ext_equal(s, s_raw);
        assert(s =~= s_raw);
        super::super::iset::lemma_iset_ext_equal_eq(s, s_raw);
        assert(s == s_raw);
        assert(mfrac@.dom() =~= s_raw);
        let left = ISet::new(|i: int| mself.off <= i < mself.off + n);
        assert forall|i: int| (olddom - s).contains(i) == left.contains(i) by {
            super::super::iset::lemma_iset_difference(olddom, s, i);
            super::super::iset::lemma_iset_new(|ii: int| mself.off + n <= ii < mself.off + mself.len, i);
            super::super::iset::lemma_iset_new(|ii: int| mself.off <= ii < mself.off + mself.len, i);
            super::super::iset::lemma_iset_new(|ii: int| mself.off <= ii < mself.off + n, i);
            if (olddom - s).contains(i) {
                assert(olddom.contains(i));
                assert(full.contains(i));
                assert(mself.off <= i < mself.off + mself.len);
                assert(!s.contains(i));
                assert(i < mself.off + n);
            }
            if left.contains(i) {
                assert(mself.off <= i < mself.off + n);
                assert(full.contains(i));
                assert(olddom.contains(i));
                assert(!s.contains(i));
            }
        }
        super::super::iset::lemma_iset_ext_equal(olddom - s, left);
        assert(olddom - s =~= left);
        super::super::iset::lemma_iset_ext_equal_eq(olddom - s, left);
        assert(mself.frac@.dom() == olddom);
        assert(olddom - s == left);
        assert(mselffrac@.dom() == olddom - s);
        super::super::iset::lemma_iset_ext_equal(mselffrac@.dom(), olddom - s);
        assert(mselffrac@.dom() =~= olddom - s);
        assert(mselffrac@.dom() =~= left);
        super::super::iset::lemma_iset_ext_equal_eq(mselffrac@.dom(), left);
        assert(mselffrac@.dom() == left);
        assert(mself.frac@ == mselffrac@.union_prefer_right(mfrac@));
        mselffrac@.lemma_union_prefer_right(mfrac@);
        let tracked result = GhostSubseq::new((mself.off + n) as nat, (mself.len - n) as nat, mfrac);
        let tracked nself = GhostSubseq::new(mself.off, n as nat, mselffrac);
        *self = nself;
        assert(self.off() == mself.off);
        assert(self@.len() == n);
        assert(mself@.subrange(0, n).len() == n);
        assert forall|i: int| 0 <= i < n implies self@[i] == mself@.subrange(0, n)[i] by {
            let k = mself.off + i;
            super::super::iset::lemma_iset_new(|ii: int| mself.off <= ii < mself.off + n, k);
            super::super::iset::lemma_iset_new(|ii: int| mself.off <= ii < mself.off + mself.len, k);
            super::super::iset::lemma_iset_new(|ii: int| mself.off + n <= ii < mself.off + mself.len, k);
            assert(left.contains(k));
            assert(mselffrac@.dom().contains(k) == (olddom - s).contains(k));
            assert((olddom - s).contains(k));
            assert(mselffrac@.dom().contains(k));
            assert(!s.contains(k));
            assert(!mfrac@.dom().contains(k));
            assert(mself.frac@.dom().contains(k));
            assert((mselffrac@.union_prefer_right(mfrac@)).dom().contains(k));
            mselffrac@.lemma_union_prefer_right(mfrac@);
            assert((mselffrac@.union_prefer_right(mfrac@))[k] == if mfrac@.dom().contains(k) {
                mfrac@[k]
            } else {
                mselffrac@[k]
            });
            assert((mselffrac@.union_prefer_right(mfrac@))[k] == mselffrac@[k]);
            assert(mself.frac@[k] == mselffrac@[k]);
            assert(self@[i] == mselffrac@[k]);
            assert(mself@.subrange(0, n)[i] == mself@[i]);
            assert(mself@[i] == mself.frac@[k]);
        };
        assert(self@ =~= mself@.subrange(0, n));
        assert(result.off() == mself.off + n);
        assert(result@.len() == mself.len - n);
        assert(mself@.subrange(n, mself@.len() as int).len() == mself.len - n);
        assert forall|i: int|
            0 <= i < mself.len - n implies result@[i] == mself@.subrange(n, mself@.len() as int)[i] by {
            let k = mself.off + n + i;
            super::super::iset::lemma_iset_new(|ii: int| mself.off + n <= ii < mself.off + mself.len, k);
            super::super::iset::lemma_iset_new(|ii: int| mself.off <= ii < mself.off + mself.len, k);
            assert(s.contains(k));
            assert(mfrac@.dom().contains(k));
            assert((mselffrac@.union_prefer_right(mfrac@)).dom().contains(k));
            mselffrac@.lemma_union_prefer_right(mfrac@);
            assert((mselffrac@.union_prefer_right(mfrac@))[k] == if mfrac@.dom().contains(k) {
                mfrac@[k]
            } else {
                mselffrac@[k]
            });
            assert((mselffrac@.union_prefer_right(mfrac@))[k] == mfrac@[k]);
            assert(mself.frac@[k] == mfrac@[k]);
            assert(result@[i] == mfrac@[k]);
            assert(mself@.subrange(n, mself@.len() as int)[i] == mself@[n + i]);
            assert(mself@[n + i] == mself.frac@[k]);
        };
        assert(result@ =~= mself@.subrange(n, mself@.len() as int));
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
        let combined_dom = ISet::new(|i: int| mself.off <= i < mself.off + mself.len + r.len);
        assert(mselffrac@ == mself.frac@.union_prefer_right(r.frac@));
        mself.frac@.lemma_union_prefer_right(r.frac@);
        assert forall|i: int| mselffrac@.dom().contains(i) == combined_dom.contains(i) by {
            super::super::iset::lemma_iset_new(|ii: int| mself.off <= ii < mself.off + mself.len, i);
            super::super::iset::lemma_iset_new(|ii: int| r.off <= ii < r.off + r.len, i);
            super::super::iset::lemma_iset_new(
                |ii: int| mself.off <= ii < mself.off + mself.len + r.len,
                i,
            );
            assert(mself.frac@.dom().contains(i) <==> mself.off <= i < mself.off + mself.len);
            assert(r.frac@.dom().contains(i) <==> r.off <= i < r.off + r.len);
            assert(r.off == mself.off + mself.len);
            super::super::iset::lemma_iset_union(mself.frac@.dom(), r.frac@.dom(), i);
            assert((mself.frac@.union_prefer_right(r.frac@)).dom().contains(i) == (mself.frac@.dom().union(r.frac@.dom())).contains(i));
            assert(mselffrac@.dom().contains(i) <==> mself.frac@.dom().contains(i) || r.frac@.dom().contains(i));
        }
        super::super::iset::lemma_iset_ext_equal(mselffrac@.dom(), combined_dom);
        assert(mselffrac@.dom() =~= combined_dom);
        super::super::iset::lemma_iset_ext_equal_eq(mselffrac@.dom(), combined_dom);
        assert(mselffrac@.dom() == combined_dom);
        let tracked nself = GhostSubseq::new(mself.off, mself.len + r.len, mselffrac);
        *self = nself;
        assert(self@.len() == mself.len + r.len);
        assert((mself@ + r@).len() == mself.len + r.len);
        assert forall|i: int| 0 <= i < mself.len + r.len implies self@[i] == (mself@ + r@)[i] by {
            let k = mself.off + i;
            if i < mself.len {
                super::super::iset::lemma_iset_new(|ii: int| r.off <= ii < r.off + r.len, k);
                super::super::iset::lemma_iset_new(
                    |ii: int| mself.off <= ii < mself.off + mself.len + r.len,
                    k,
                );
                assert(!r.frac@.dom().contains(k));
                assert((mself.frac@.union_prefer_right(r.frac@)).dom().contains(k));
                assert((mself.frac@.union_prefer_right(r.frac@))[k] == mself.frac@[k]);
                assert(mselffrac@[k] == mself.frac@[k]);
                assert(self@[i] == mself@[i]);
                assert((mself@ + r@)[i] == mself@[i]);
            } else {
                let j = i - mself.len;
                assert(0 <= j < r.len);
                assert(k == r.off + j);
                super::super::iset::lemma_iset_new(|ii: int| r.off <= ii < r.off + r.len, k);
                assert(r.frac@.dom().contains(k));
                assert((mself.frac@.union_prefer_right(r.frac@)).dom().contains(k));
                assert((mself.frac@.union_prefer_right(r.frac@))[k] == if r.frac@.dom().contains(k) {
                    r.frac@[k]
                } else {
                    mself.frac@[k]
                });
                assert((mself.frac@.union_prefer_right(r.frac@))[k] == r.frac@[k]);
                assert(mselffrac@[k] == r.frac@[k]);
                assert(self@[i] == r@[j]);
                assert((mself@ + r@)[i] == r@[j]);
            }
        }
        assert(self@ =~= mself@ + r@);
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
        let self_dom = ISet::new(|i: int| self.off <= i < self.off + self.len);
        let other_dom = ISet::new(|i: int| other.off <= i < other.off + other.len);
        assert(self.frac@.dom() =~= self_dom);
        assert(other.frac@.dom() =~= other_dom);
        lemma_iset_ext_equal(self.frac@.dom(), self_dom);
        lemma_iset_ext_equal(other.frac@.dom(), other_dom);
        if self@.len() > 0 {
            super::super::iset::lemma_iset_new(
                |i: int| self.off <= i < self.off + self.len,
                self.off() as int,
            );
            assert(self_dom.contains(self.off() as int));
            assert(self.frac@.dom().contains(self.off() as int));
            assert(self.frac@.contains_key(self.off() as int));
        }
        if other@.len() > 0 {
            super::super::iset::lemma_iset_new(
                |i: int| other.off <= i < other.off + other.len,
                other.off() as int,
            );
            assert(other_dom.contains(other.off() as int));
            assert(other.frac@.dom().contains(other.off() as int));
            assert(other.frac@.contains_key(other.off() as int));
        }
        assert(self@.len() == 0 || self.frac@.contains_key(self.off() as int));
        assert(other@.len() == 0 || other.frac@.contains_key(other.off() as int));
        if self@.len() > 0 && other@.len() > 0 {
            if self.off() <= other.off() {
                if !(self.off() + self@.len() <= other.off()) {
                    super::super::iset::lemma_iset_new(
                        |i: int| self.off <= i < self.off + self.len,
                        other.off() as int,
                    );
                    assert(self_dom.contains(other.off() as int));
                    assert(self.frac@.dom().contains(other.off() as int));
                    assert(self.frac@.contains_key(other.off() as int));
                    assert(other.frac@.contains_key(other.off() as int));
                    assert(false);
                }
            } else {
                assert(other.off() < self.off());
                if !(other.off() + other@.len() <= self.off()) {
                    super::super::iset::lemma_iset_new(
                        |i: int| other.off <= i < other.off + other.len,
                        self.off() as int,
                    );
                    assert(other_dom.contains(self.off() as int));
                    assert(other.frac@.dom().contains(self.off() as int));
                    assert(other.frac@.contains_key(self.off() as int));
                    assert(self.frac@.contains_key(self.off() as int));
                    assert(false);
                }
            }
        }
    }

    pub proof fn dummy() -> (tracked result: Self) {
        let tracked (auth, subseq) = GhostSeqAuth::<V>::new(Seq::empty(), 0);
        subseq
    }

    // Helper to lift GhostSubmap into GhostSubseq.
    pub proof fn new(off: nat, len: nat, tracked f: GhostSubmap<int, V>) -> (tracked result:
        GhostSubseq<V>)
        requires
            f@.dom() == ISet::new(|i: int| off <= i < off + len),
        ensures
            result.id() == f.id(),
            result.off() == off,
            result@ == Seq::new(len, |i| f@[off + i]),
    {
        GhostSubseq { off: off, len: len, frac: f }
    }
}

} // verus!
