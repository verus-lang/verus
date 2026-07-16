use core::marker;

#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
tracked enum SeqInner<A> {
    Nil,
    Cons { head: Tracked<A>, tail: Tracked<SeqInner<A>> },
}

// This indirection is required to show the termination of `Seq::len`
//
// If we translated this to `Seq` we the decrease clauses wouldn't work,
// because we would have had to re-internalize the tail into a `Seq`
impl<A> SeqInner<A> {
    spec fn len(self) -> nat
        decreases self,
    {
        match self {
            SeqInner::Nil => 0,
            SeqInner::Cons { tail, .. } => { 1 + tail.len() },
        }
    }

    spec fn index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
        decreases self.len(),
    {
        match self {
            SeqInner::Nil => arbitrary(),
            SeqInner::Cons { head, tail } => if i == 0 {
                head@
            } else {
                tail.index(i - 1)
            },
        }
    }

    #[verifier::inline]
    spec fn spec_index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    {
        self.index(i)
    }

    spec fn first(self) -> A
        recommends
            0 < self.len(),
    {
        self[0]
    }

    spec fn last(self) -> A
        recommends
            0 < self.len(),
    {
        self[self.len() as int - 1]
    }

    spec fn push(self, a: A) -> SeqInner<A>
        decreases self.len(),
    {
        match self {
            SeqInner::Nil => SeqInner::Cons { head: Tracked(a), tail: Tracked(SeqInner::Nil) },
            SeqInner::Cons { head, tail } => {
                let new_tail = tail.push(a);
                SeqInner::Cons { head, tail: Tracked(new_tail) }
            },
        }
    }

    spec fn update(self, i: int, a: A) -> SeqInner<A>
        recommends
            0 <= i < self.len(),
        decreases self.len(),
    {
        if !(0 <= i < self.len()) {  // this supports weakening some preconditions
            self
        } else {
            match self {
                SeqInner::Nil => arbitrary(),
                SeqInner::Cons { head, tail } => if i == 0 {
                    SeqInner::Cons { head: Tracked(a), tail }
                } else {
                    let new_tail = tail.update(i - 1, a);
                    SeqInner::Cons { head, tail: Tracked(new_tail) }
                },
            }
        }
    }

    spec fn subrange(self, start_inclusive: int, end_exclusive: int) -> SeqInner<A>
        recommends
            0 <= start_inclusive <= end_exclusive <= self.len(),
        decreases start_inclusive, end_exclusive - start_inclusive,
    {
        match self {
            SeqInner::Nil => SeqInner::Nil,
            SeqInner::Cons {
                head,
                tail,
            } =>
            // skip elements until start_inclusive becomes 0
            if start_inclusive > 0 {
                tail.subrange(start_inclusive - 1, end_exclusive - 1)
            } else {
                if end_exclusive <= 0 {
                    SeqInner::Nil
                } else {
                    let new_tail = tail.subrange(start_inclusive, end_exclusive - 1);
                    SeqInner::Cons { head, tail: Tracked(new_tail) }
                }
            },
        }
    }

    spec fn add(self, rhs: SeqInner<A>) -> SeqInner<A>
        decreases self.len(),
    {
        match self {
            SeqInner::Nil => rhs,
            SeqInner::Cons { head, tail } => {
                let new_tail = tail.add(rhs);
                SeqInner::Cons { head, tail: Tracked(new_tail) }
            },
        }
    }

    spec fn insert(self, i: int, a: A) -> SeqInner<A>
        recommends
            0 <= i <= self.len(),
    {
        self.subrange(0, i).push(a).add(self.subrange(i, self.len() as int))
    }

    spec fn remove(self, i: int) -> SeqInner<A>
        recommends
            0 <= i < self.len(),
    {
        self.subrange(0, i).add(self.subrange(i + 1, self.len() as int))
    }

    // return the suffix
    proof fn tracked_split_at(tracked &mut self, i: int) -> (tracked ret: Self)
        requires
            0 <= i <= old(self).len(),
        ensures
            *final(self) == old(self).subrange(0, i),
            ret == old(self).subrange(i, old(self).len() as int),
            final(self).len() == i,
            ret.len() == old(self).len() - i,
        decreases self.len(),
    {
        let tracked mut s = SeqInner::Nil;
        super::modes::tracked_swap(&mut s, self);
        let tracked ret = if i == 0 {
            seq_inner::lemma_subrange_len(*old(self), 0, i);
            seq_inner::lemma_empty(old(self).subrange(0, i));
            seq_inner::lemma_full_subrange_idempotent(*old(self));

            s
        } else {
            let ghost old_self = s;
            match s {
                SeqInner::Nil => {
                    assert(false);
                    proof_from_false()
                },
                SeqInner::Cons { head, tail } => {
                    let tracked Tracked(mut tail) = tail;
                    let ghost old_tail = tail;
                    let tracked suff = tail.tracked_split_at(i - 1);

                    let tracked mut new = SeqInner::Cons { head, tail: Tracked(tail) };

                    super::modes::tracked_swap(&mut new, self);

                    suff
                },
            }
        };

        assert(*final(self) == old(self).subrange(0, i));
        assert(ret == old(self).subrange(i, old(self).len() as int));
        seq_inner::lemma_subrange_len(*old(self), 0, i);
        seq_inner::lemma_subrange_len(*old(self), i, old(self).len() as int);

        ret
    }

    proof fn tracked_add(tracked &mut self, tracked mut b: Self)
        ensures
            *final(self) == old(self).add(b),
            final(self).len() == old(self).len() + b.len(),
        decreases self.len(),
    {
        let tracked mut s = SeqInner::Nil;
        super::modes::tracked_swap(&mut s, self);
        match s {
            SeqInner::Nil => {
                seq_inner::lemma_empty(*old(self));
                super::modes::tracked_swap(&mut b, self);
            },
            SeqInner::Cons { head, tail } => {
                let tracked Tracked(mut tail) = tail;
                tail.tracked_add(b);
                let tracked mut new = SeqInner::Cons { head, tail: Tracked(tail) };
                super::modes::tracked_swap(&mut new, self);
                seq_inner::lemma_add_len(s, b);
            },
        }
    }

    proof fn tracked_insert(tracked &mut self, i: int, tracked v: A)
        requires
            0 <= i <= old(self).len(),
        ensures
            final(self).len() == old(self).len() + 1,
            *final(self) == old(self).insert(i, v),
        decreases self.len(),
    {
        if i == self.len() {
            seq_inner::lemma_subrange_len(*old(self), i, self.len() as int);
            seq_inner::lemma_empty(old(self).subrange(i, self.len() as int));
            seq_inner::lemma_full_subrange_idempotent(*old(self));
            seq_inner::lemma_add_empty(self.push(v));
            self.tracked_push(v);
        } else {
            let tracked suff = self.tracked_split_at(i);
            self.tracked_push(v);
            self.tracked_add(suff);
        }
    }

    proof fn tracked_remove(tracked &mut self, i: int) -> (tracked ret: A)
        requires
            0 <= i < old(self).len(),
        ensures
            ret == old(self)[i],
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).remove(i),
        decreases self.len(),
    {
        if i == 0 {
            self.tracked_pop_front()
        } else {
            let tracked suff = self.tracked_split_at(i + 1);
            assert(suff == old(self).subrange(i + 1, old(self).len() as int));

            let tracked ret = self.tracked_pop();
            seq_inner::lemma_subrange_index(*old(self), 0, i + 1, i);
            assert(ret == old(self)[i]);
            assert(*self == old(self).subrange(0, i + 1).subrange(0, i));
            seq_inner::lemma_subrange_composition(*old(self), 0, i + 1, 0, i);

            self.tracked_add(suff);
            ret
        }
    }

    proof fn tracked_borrow(tracked &self, i: int) -> (tracked ret: &A)
        requires
            0 <= i < self.len(),
        ensures
            *ret == self[i],
        decreases self.len(),
    {
        if i == 0 {
            match self {
                SeqInner::Nil => {
                    assert(false);
                    proof_from_false()
                },
                SeqInner::Cons { head, .. } => { head.borrow() },
            }
        } else {
            match self {
                SeqInner::Nil => {
                    assert(false);
                    proof_from_false()
                },
                SeqInner::Cons { tail, .. } => { tail.tracked_borrow(i - 1) },
            }
        }
    }

    proof fn tracked_push(tracked &mut self, tracked v: A)
        ensures
            *final(self) == old(self).push(v),
            final(self).len() == old(self).len() + 1,
        decreases self.len(),
    {
        let tracked mut s = SeqInner::Nil;
        super::modes::tracked_swap(&mut s, self);
        match s {
            SeqInner::Nil => {
                let tracked mut new = SeqInner::Cons {
                    head: Tracked(v),
                    tail: Tracked(SeqInner::Nil),
                };
                super::modes::tracked_swap(&mut new, self);
            },
            SeqInner::Cons { head, tail } => {
                let tracked Tracked(mut tail) = tail;
                tail.tracked_push(v);
                let tracked mut new = SeqInner::Cons { head, tail: Tracked(tail) };
                super::modes::tracked_swap(&mut new, self);
            },
        }
        assert(*final(self) == old(self).push(v));
        seq_inner::lemma_push_len(*old(self), v);
    }

    proof fn tracked_push_front(tracked &mut self, tracked v: A)
        ensures
            *final(self) == old(self).insert(0, v),
            final(self).len() == old(self).len() + 1,
        decreases self.len(),
    {
        self.tracked_insert(0, v);
    }

    proof fn tracked_pop(tracked &mut self) -> (tracked ret: A)
        requires
            old(self).len() > 0,
        ensures
            ret == old(self).last(),
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).subrange(0, old(self).len() - 1),
        decreases self.len(),
    {
        let tracked mut s = SeqInner::Nil;
        super::modes::tracked_swap(&mut s, self);

        let tracked ret = match s {
            SeqInner::Nil => {
                assert(false);
                proof_from_false()
            },
            SeqInner::Cons { head, tail } => {
                let tracked Tracked(mut tail) = tail;
                let tracked Tracked(head) = head;

                let tracked v = match tail {
                    SeqInner::Nil => {
                        let tracked mut new = SeqInner::Nil;
                        super::modes::tracked_swap(&mut new, self);

                        seq_inner::lemma_empty(tail);
                        seq_inner::lemma_subrange_len(*old(self), 0, old(self).len() - 1);
                        seq_inner::lemma_empty(old(self).subrange(0, old(self).len() - 1));

                        head
                    },
                    SeqInner::Cons { head: thead, tail: ttail } => {
                        let tracked mut tail = SeqInner::Cons { head: thead, tail: ttail };
                        let tracked v = tail.tracked_pop();

                        let tracked mut new = SeqInner::Cons {
                            head: Tracked(head),
                            tail: Tracked(tail),
                        };
                        super::modes::tracked_swap(&mut new, self);

                        v
                    },
                };

                v
            },
        };

        assert(*final(self) == old(self).subrange(0, old(self).len() - 1));
        seq_inner::lemma_subrange_len(*old(self), 0, old(self).len() - 1);

        ret
    }

    proof fn tracked_pop_front(tracked &mut self) -> (tracked ret: A)
        requires
            old(self).len() > 0,
        ensures
            ret == old(self).first(),
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).subrange(1, old(self).len() as int),
    {
        let tracked mut s = SeqInner::Nil;
        super::modes::tracked_swap(&mut s, self);
        let tracked ret = match s {
            SeqInner::Nil => {
                assert(false);
                proof_from_false()
            },
            SeqInner::Cons { head, tail } => {
                let tracked Tracked(mut tail) = tail;
                let tracked Tracked(head) = head;
                seq_inner::lemma_tail_subrange(head, tail);
                assert(tail == old(self).subrange(1, old(self).len() as int));
                super::modes::tracked_swap(&mut tail, self);
                head
            },
        };

        assert(*final(self) == old(self).subrange(1, old(self).len() as int));
        seq_inner::lemma_subrange_len(*old(self), 1, old(self).len() as int);

        ret
    }
}

mod seq_inner {
    use super::*;

    // empty
    pub(super) proof fn lemma_empty<A>(s: SeqInner<A>)
        ensures
            s.len() == 0 <==> s == SeqInner::Nil,
    {
        if s.len() == 0 {
            assert(s == SeqInner::Nil)
        }
        if s == SeqInner::Nil {
            assert(s.len() == 0);
        }
    }

    // push lemmas
    pub(super) proof fn lemma_push_len<A>(s: SeqInner<A>, a: A)
        ensures
            s.push(a).len() == s.len() + 1,
        decreases s.len(),
    {
        match s {
            SeqInner::Nil => {},
            SeqInner::Cons { tail, .. } => {
                lemma_push_len(tail@, a);
            },
        }
    }

    pub(super) proof fn lemma_push_index_different<A>(s: SeqInner<A>, a: A, i: int)
        requires
            i < s.len(),
        ensures
            #[trigger] s.push(a)[i] == s[i],
        decreases s,
    {
        match s {
            SeqInner::Nil => {
                lemma_index_out_of_bounds(s.push(a), i);
            },
            SeqInner::Cons { tail, .. } => {
                if i == 0 {
                } else {
                    lemma_push_index_different(tail@, a, i - 1);
                }
            },
        }
    }

    pub(super) proof fn lemma_push_index_same<A>(s: SeqInner<A>, a: A, i: int)
        requires
            i == s.len(),
        ensures
            #[trigger] s.push(a)[i] == a,
        decreases s,
    {
        match s {
            SeqInner::Nil => {
                assert(s.push(a) == SeqInner::Cons {
                    head: Tracked(a),
                    tail: Tracked(SeqInner::Nil),
                });
                assert(s.push(a)[0] == a);
            },
            SeqInner::Cons { tail, .. } => {
                lemma_push_index_same(tail@, a, i - 1);
            },
        }
    }

    // update lemmas
    pub(super) proof fn lemma_update_len<A>(s: SeqInner<A>, i: int, a: A)
        ensures
            s.update(i, a).len() == s.len(),
        decreases i,
    {
        if !(0 <= i < s.len()) {
            assert(s.update(i, a) == s);
        } else {
            let s_upd = s.update(i, a);
            match s {
                SeqInner::Nil => {},
                SeqInner::Cons { head, tail } => {
                    match s_upd {
                        SeqInner::Nil => {},
                        SeqInner::Cons { head: head_upd, tail: tail_upd } => {
                            if i == 0 {
                                assert(head_upd == a);
                            } else {
                                lemma_update_len(tail@, (i - 1), a);
                            }
                        },
                    }
                },
            }
        }
    }

    pub(super) proof fn lemma_update_index_same<A>(s: SeqInner<A>, i: int, a: A)
        requires
            0 <= i < s.len(),
        ensures
            #[trigger] s.update(i, a)[i] == a,
        decreases s,
    {
        match s {
            SeqInner::Nil => {},
            SeqInner::Cons { tail, .. } => {
                if i == 0 {
                    assert(s.update(i, a)[i] == a)
                } else {
                    lemma_update_index_same(tail@, i - 1, a);
                }
            },
        }
    }

    pub(super) proof fn lemma_update_index_different<A>(s: SeqInner<A>, i1: int, i2: int, a: A)
        requires
            i1 != i2,
        ensures
            #[trigger] s.update(i2, a)[i1] == s[i1],
        decreases s,
    {
        if !(0 <= i2 < s.len()) {
            assert(s.update(i2, a) == s);
        } else {
            match s {
                SeqInner::Nil => {},
                SeqInner::Cons { tail, .. } => {
                    if i2 == 0 {
                        assert(s.update(i2, a)[i1] == s[i1]);
                    } else if i1 == 0 {
                        assert(s.update(i2, a)[i1] == s[i1]);
                    } else {
                        lemma_update_index_different(tail@, i1 - 1, i2 - 1, a);
                    }
                },
            }
        }
    }

    // subrange lemmas
    pub(super) proof fn lemma_subrange_len<A>(s: SeqInner<A>, j: int, k: int)
        requires
            0 <= j <= k <= s.len(),
        ensures
            s.subrange(j, k).len() == k - j,
        decreases j, k,
    {
        match s {
            SeqInner::Nil => {},
            SeqInner::Cons { head, tail } => {
                if j > 0 {
                    assert(s.subrange(j, k) == tail.subrange(j - 1, k - 1));
                    lemma_subrange_len(tail@, j - 1, k - 1);
                } else if k > 0 {
                    let new_tail = tail@.subrange(j, k - 1);
                    lemma_subrange_len(tail@, j, k - 1);
                    assert(new_tail.len() == k - j - 1);
                    let sub = SeqInner::Cons { head, tail: Tracked(new_tail) };
                    assert(sub.len() == 1 + new_tail.len());
                } else {
                    assert(j == k == 0);
                    assert(s.subrange(j, k).len() == 0);
                }
            },
        }
    }

    pub(super) proof fn lemma_subrange_composition_aux2<A>(s: SeqInner<A>, j1: int, j2: int)
        requires
            0 <= j2 <= j1 <= s.len(),
        ensures
            s.subrange(0, j1).subrange(0, j2) == s.subrange(0, j2),
        decreases s.len(),
    {
        if j1 == j2 {
            lemma_subrange_len(s, 0, j1);
            lemma_full_subrange_idempotent(s.subrange(0, j1));
        } else if j1 == 0 {
            assert(false);
        } else if j2 == 0 {
            lemma_subrange_len(s.subrange(0, j1), 0, j2);
            lemma_empty(s.subrange(0, j1).subrange(0, j2));
        } else {
            match s {
                SeqInner::Nil => {},
                SeqInner::Cons { head, tail } => {
                    lemma_subrange_composition_aux2(tail@, j1 - 1, j2 - 1);
                },
            }
        }
    }

    pub(super) proof fn lemma_subrange_index_aux<A>(s: SeqInner<A>, k: int, i: int)
        requires
            0 <= k <= s.len(),
            0 <= i < k,
        ensures
            s.subrange(0, k)[i] == s[i],
        decreases s,
    {
        lemma_subrange_len(s, 0, k);
        // assert(s.subrange(0, k).len() == k);
        // assert(0 <= i < s.subrange(0, k).len());
        match s {
            SeqInner::Nil => {
                // assert(false);
            },
            SeqInner::Cons { head, tail } => {
                if i == 0 {
                    // assert(s[0] == head);
                    assert(s.subrange(0, k)[0] == head);
                } else {
                    lemma_subrange_index_aux(tail@, k - 1, i - 1);
                }
            },
        }
    }

    pub(super) proof fn lemma_subrange_index<A>(s: SeqInner<A>, j: int, k: int, i: int)
        requires
            0 <= j <= k <= s.len(),
            0 <= i < k - j,
        ensures
            s.subrange(j, k)[i] == s[i + j],
        decreases s,
    {
        lemma_subrange_len(s, j, k);
        if j == 0 {
            lemma_subrange_index_aux(s, k, i);
        } else {
            match s {
                SeqInner::Nil => {
                    assert(false);
                },
                SeqInner::Cons { head, tail } => {
                    lemma_subrange_index(tail@, j - 1, k - 1, i);
                },
            }
        }
    }

    pub(super) proof fn lemma_subrange_composition_aux1<A>(
        s: SeqInner<A>,
        j1: int,
        i2: int,
        j2: int,
    )
        requires
            0 <= j1 <= s.len(),
            0 <= i2 <= j2 <= j1,
        ensures
            s.subrange(0, j1).subrange(i2, j2) == s.subrange(i2, j2),
        decreases s.len(),
    {
        if i2 == 0 {
            lemma_subrange_composition_aux2(s, j1, j2);
        } else {
            match s {
                SeqInner::Nil => {},
                SeqInner::Cons { head, tail } => {
                    lemma_subrange_composition_aux1(tail@, j1 - 1, i2 - 1, j2 - 1);
                },
            }
        }
    }

    pub(super) proof fn lemma_subrange_composition<A>(
        s: SeqInner<A>,
        i1: int,
        j1: int,
        i2: int,
        j2: int,
    )
        requires
            0 <= i1 <= j1 <= s.len(),
            0 <= i2 <= j2 <= j1 - i1,
        ensures
            s.subrange(i1, j1).subrange(i2, j2) == s.subrange(i1 + i2, i1 + j2),
        decreases s.len(),
    {
        if i1 == 0 {
            lemma_subrange_composition_aux1(s, j1, i2, j2);
        } else {
            match s {
                SeqInner::Nil => {},
                SeqInner::Cons { head, tail } => {
                    lemma_subrange_composition(tail@, i1 - 1, j1 - 1, i2, j2);
                },
            }
        }
    }

    pub(super) open spec fn cons_list<A>(head: A, tail: SeqInner<A>) -> SeqInner<A> {
        SeqInner::Cons { head: Tracked(head), tail: Tracked(tail) }
    }

    pub(super) proof fn lemma_tail_subrange<A>(head: A, tail: SeqInner<A>)
        ensures
            cons_list(head, tail).subrange(1, cons_list(head, tail).len() as int) == tail,
    {
        let s = SeqInner::Cons { head: Tracked(head), tail: Tracked(tail) };
        match s {
            SeqInner::Nil => {
                assert(false);
            },
            SeqInner::Cons { head: h, tail: t } => { lemma_full_subrange_idempotent(tail) },
        }
    }

    pub(super) proof fn lemma_full_subrange_idempotent<A>(s: SeqInner<A>)
        ensures
            s.subrange(0, s.len() as int) == s,
        decreases s.len(),
    {
        match s {
            SeqInner::Nil => {
                assert(s.subrange(0, s.len() as int) == s);
            },
            SeqInner::Cons { head, tail } => {
                lemma_subrange_index(s, 0, s.len() as int, 0);
                lemma_full_subrange_idempotent(tail@);
            },
        }
    }

    // decrease to index
    pub(super) proof fn lemma_index_decreases<A>(s: SeqInner<A>, i: int)
        requires
            0 <= i < s.len(),
        ensures
            (decreases_to!(s => s[i])),
        decreases i,
    {
        match s {
            SeqInner::Nil => {
                assert(s.len() == 0);
                assert(false);
            },
            SeqInner::Cons { head, tail } => {
                if i == 0 {
                    assert(decreases_to!(s => s[i]));
                } else {
                    assert(tail[i - 1] == s[i]);
                    lemma_index_decreases(tail@, i - 1);
                    assert(decreases_to!(s => tail@));
                    assert(decreases_to!(tail@ => tail[i-1]));
                }
            },
        }
    }

    // add lemmas
    pub(super) proof fn lemma_add_empty<A>(s: SeqInner<A>)
        ensures
            s.add(SeqInner::Nil) == s,
            SeqInner::Nil.add(s) == s,
        decreases s.len(),
    {
        assert(SeqInner::Nil.add(s) == s);

        let sum = s.add(SeqInner::Nil);
        match s {
            SeqInner::Nil => {
                assert(sum == SeqInner::Nil);
                assert(s == SeqInner::Nil);
            },
            SeqInner::Cons { head, tail } => {
                assert(sum == SeqInner::Cons { head, tail: Tracked(tail@.add(SeqInner::Nil)) });
                lemma_add_empty(tail@);
            },
        }
    }

    pub(super) proof fn lemma_add_len<A>(s1: SeqInner<A>, s2: SeqInner<A>)
        ensures
            s1.add(s2).len() == s1.len() + s2.len(),
        decreases s1.add(s2).len(),
    {
        let sum = s1.add(s2);
        match s1 {
            SeqInner::Nil => {
                assert(sum == s2);
            },
            SeqInner::Cons { head, tail } => {
                let new_tail = tail@.add(s2);
                lemma_add_len(tail@, s2);
                assert(new_tail.len() == (s1.len() - 1) + s2.len());
                assert(sum.len() == 1 + new_tail.len());
            },
        }
    }

    pub(super) proof fn lemma_add_index1<A>(s1: SeqInner<A>, s2: SeqInner<A>, i: int)
        requires
            i < s1.len(),
        ensures
            s1.add(s2)[i] == s1[i],
        decreases s1,
    {
        if i < 0 {
            lemma_index_out_of_bounds(s1, i);
            lemma_index_out_of_bounds(s1.add(s2), i);
        } else {
            match s1 {
                SeqInner::Nil => {},
                SeqInner::Cons { head, tail } => {
                    if i == 0 {
                        assert(s1[i] == s1.add(s2)[i]);
                    } else {
                        lemma_add_index1(tail@, s2, i - 1);
                    }
                },
            }
        }
    }

    pub(super) proof fn lemma_add_index2<A>(s1: SeqInner<A>, s2: SeqInner<A>, i: int)
        requires
            s1.len() <= i < s1.len() + s2.len(),
        ensures
            s1.add(s2)[i] == s2[i - s1.len()],
        decreases s1,
    {
        match s1 {
            SeqInner::Nil => {
                assert(s1.add(s2) == s2);
                assert(s1.add(s2)[i] == s2[i - s1.len()]);
            },
            SeqInner::Cons { head, tail } => {
                if i == 0 {
                    assert(s1.add(s2)[i] == s2[i - s1.len()]);
                } else {
                    lemma_add_index2(tail@, s2, i - 1);
                    assert(s1.add(s2)[i] == s2[i - s1.len()]);
                }
            },
        }
    }

    // index lemma
    pub(super) proof fn lemma_index_out_of_bounds<A>(s: SeqInner<A>, i: int)
        requires
            !(0 <= i < s.len()),
        ensures
            s[i] == arbitrary::<A>(),
        decreases s,
    {
        match s {
            SeqInner::Nil => {},
            SeqInner::Cons { tail, .. } => {
                lemma_index_out_of_bounds(tail@, i - 1);
            },
        }
    }

}

/// `Seq<A>` is a sequence type for specifications.
/// To use a "sequence" in compiled code, use an `exec` type like `vec::Vec`
/// that has `Seq<A>` as its specification type.
///
/// An object `seq: Seq<A>` has a length, given by [`seq.len()`](Seq::len),
/// and a value at each `i` for `0 <= i < seq.len()`, given by [`seq[i]`](Seq::index).
///
/// Sequences can be constructed in a few different ways:
///  * [`Seq::empty`] construct an empty sequence (`len() == 0`)
///  * [`Seq::new`] construct a sequence of a given length, initialized according
///     to a given function mapping indices `i` to values `A`.
///  * The [`seq!`] macro, to construct small sequences of a fixed size (analagous to the
///     [`std::vec!`] macro).
///  * By manipulating an existing sequence with [`Seq::push`], [`Seq::update`],
///    or [`Seq::add`].
///
/// To prove that two sequences are equal, it is usually easiest to use the
/// extensional equality operator `=~=`.
#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
pub tracked struct Seq<A> {
    inner: SeqInner<A>,
}

impl<A> Seq<A> {
    /// An empty sequence (i.e., a sequence of length 0).
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::empty"]
    pub closed spec fn empty() -> Seq<A> {
        Seq { inner: SeqInner::Nil }
    }

    /// Construct a sequence `s` of length `len` where entry `s[i]` is given by `f(i)`.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::new"]
    pub closed spec fn new(len: nat, f: spec_fn(int) -> A) -> Seq<A>
        decreases len,
    {
        if len == 0 {
            Seq { inner: SeqInner::Nil }
        } else {
            Self::new((len - 1) as nat, f).push(f(len - 1))
        }
    }

    /// The length of a sequence.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::len"]
    pub closed spec fn len(self) -> nat {
        self.inner.len()
    }

    /// Gets the value at the given index `i`.
    ///
    /// If `i` is not in the range `[0, self.len())`, then the resulting value
    /// is meaningless and arbitrary.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::index"]
    pub closed spec fn index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    {
        self.inner.index(i)
    }

    /// `[]` operator, synonymous with `index`
    #[verifier::inline]
    pub open spec fn spec_index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    {
        self.index(i)
    }

    /// Appends the value `a` to the end of the sequence.
    /// This always increases the length of the sequence by 1.
    /// This often requires annotating the type of the element literal in the sequence,
    /// e.g., `10int`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn push_test() {
    ///     assert(seq![10int, 11, 12].push(13) =~= seq![10, 11, 12, 13]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::push"]
    pub closed spec fn push(self, a: A) -> Seq<A> {
        Seq { inner: self.inner.push(a) }
    }

    /// Updates the sequence at the given index, replacing the element with the given
    /// value, and leaves all other entries unchanged.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn update_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     let t = s.update(2, -5);
    ///     assert(t =~= seq![10, 11, -5, 13, 14]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::update"]
    pub closed spec fn update(self, i: int, a: A) -> Seq<A>
        recommends
            0 <= i < self.len(),
    {
        Seq { inner: self.inner.update(i, a) }
    }

    /// Returns a sequence for the given subrange.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn subrange_test() {
    ///     let s = seq![10int, 11, 12, 13, 14];
    ///     //                      ^-------^
    ///     //           0      1   2   3   4   5
    ///     let sub = s.subrange(2, 4);
    ///     assert(sub =~= seq![12, 13]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::subrange"]
    pub closed spec fn subrange(self, start_inclusive: int, end_exclusive: int) -> Seq<A>
        recommends
            0 <= start_inclusive <= end_exclusive <= self.len(),
    {
        Seq { inner: self.inner.subrange(start_inclusive, end_exclusive) }
    }

    /// Returns a sequence containing only the first n elements of the original sequence
    #[verifier::inline]
    pub open spec fn take(self, n: int) -> Seq<A> {
        self.subrange(0, n)
    }

    /// Returns a sequence without the first n elements of the original sequence
    #[verifier::inline]
    pub open spec fn skip(self, n: int) -> Seq<A> {
        self.subrange(n, self.len() as int)
    }

    /// Concatenates the sequences.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn add_test() {
    ///     assert(seq![10int, 11].add(seq![12, 13, 14])
    ///             =~= seq![10, 11, 12, 13, 14]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::add"]
    pub closed spec fn add(self, rhs: Seq<A>) -> Seq<A> {
        Seq { inner: self.inner.add(rhs.inner) }
    }

    /// `+` operator, synonymous with `add`
    #[verifier::inline]
    pub open spec fn spec_add(self, rhs: Seq<A>) -> Seq<A> {
        self.add(rhs)
    }

    /// Returns the last element of the sequence.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::last"]
    pub open spec fn last(self) -> A
        recommends
            0 < self.len(),
    {
        self[self.len() as int - 1]
    }

    /// Returns the first element of the sequence.
    #[rustc_diagnostic_item = "vstd::seq::Seq::first"]
    pub open spec fn first(self) -> A
        recommends
            0 < self.len(),
    {
        self[0]
    }

    /// Create an empty sequence
    pub proof fn tracked_empty() -> (tracked ret: Self)
        ensures
            ret == Seq::empty(),
    {
        Seq { inner: SeqInner::Nil }
    }

    /// Insert a tracked element into a sequence
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn insert_test(tracked &mut s: Seq<int>, tracked v: int)
    ///     requires
    ///         old(s)@ == seq![0, 1, 2]
    ///     ensures
    ///         final(s)@ == seq![0, 1, v, 2]
    /// {
    ///     s.tracked_insert(2, v)
    /// }
    /// ```
    pub proof fn tracked_insert(tracked &mut self, i: int, tracked v: A)
        requires
            0 <= i <= old(self).len(),
        ensures
            final(self).len() == old(self).len() + 1,
            *final(self) == old(self).insert(i, v),
    {
        self.inner.tracked_insert(i, v)
    }

    /// Remove a tracked element from a sequence
    pub proof fn tracked_remove(tracked &mut self, i: int) -> (tracked ret: A)
        requires
            0 <= i < old(self).len(),
        ensures
            ret == old(self)[i],
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).remove(i),
    {
        self.inner.tracked_remove(i)
    }

    /// Obtain a tracked borrow into an element of a sequence
    pub proof fn tracked_borrow(tracked &self, i: int) -> (tracked ret: &A)
        requires
            0 <= i < self.len(),
        ensures
            *ret == self[i],
    {
        self.inner.tracked_borrow(i)
    }

    /// Push a tracked value into the end of a sequence
    pub proof fn tracked_push(tracked &mut self, tracked v: A)
        ensures
            *final(self) == old(self).push(v),
            final(self).len() == old(self).len() + 1,
    {
        self.inner.tracked_push(v)
    }

    /// Push a tracked value into the beginning of a sequence
    pub proof fn tracked_push_front(tracked &mut self, tracked v: A)
        ensures
            *final(self) == old(self).insert(0, v),
            final(self).len() == old(self).len() + 1,
    {
        self.inner.tracked_push_front(v)
    }

    /// Pop a tracked value from the end of a sequence
    pub proof fn tracked_pop(tracked &mut self) -> (tracked ret: A)
        requires
            old(self).len() > 0,
        ensures
            ret == old(self).last(),
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).take(old(self).len() - 1),
    {
        self.inner.tracked_pop()
    }

    /// Pop a tracked value from the beginning of a sequence
    pub proof fn tracked_pop_front(tracked &mut self) -> (tracked ret: A)
        requires
            old(self).len() > 0,
        ensures
            ret == old(self).first(),
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).drop_first(),
    {
        self.inner.tracked_pop_front()
    }

    /// Split a tracked sequence around an index
    pub proof fn tracked_split_at(tracked &mut self, i: int) -> (tracked ret: Self)
        requires
            0 <= i <= old(self).len(),
        ensures
            *final(self) == old(self).subrange(0, i),
            ret == old(self).subrange(i, old(self).len() as int),
            final(self).len() == i,
            ret.len() == old(self).len() - i,
    {
        Seq { inner: self.inner.tracked_split_at(i) }
    }

    proof fn tracked_add(tracked &mut self, tracked b: Self)
        ensures
            *final(self) == old(self).add(b),
            final(self).len() == old(self).len() + b.len(),
    {
        self.inner.tracked_add(b.inner)
    }
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s[i])),
{
    lemma_seq_index_decreases(s, i)
}

pub broadcast proof fn lemma_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s[i])),
{
    seq_inner::lemma_index_decreases(s.inner, i)
}

// TODO: this should be provable
pub axiom fn axiom_seq_len_decreases<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s2.len() < s1.len(),
        forall|i2: int|
            0 <= i2 < s2.len() && #[trigger] trigger(s2[i2]) ==> exists|i1: int|
                0 <= i1 < s1.len() && s1[i1] == s2[i2],
    ensures
        decreases_to!(s1 => s2),
;

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_subrange_decreases<A>(s: Seq<A>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        s.subrange(i, j).len() < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s.subrange(i, j))),
{
    lemma_seq_subrange_decreases(s, i, j)
}

pub broadcast proof fn lemma_seq_subrange_decreases<A>(s: Seq<A>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        s.subrange(i, j).len() < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s.subrange(i, j))),
{
    broadcast use {lemma_seq_subrange_len, lemma_seq_subrange_index};

    let s2 = s.subrange(i, j);
    assert forall|i2: int| 0 <= i2 < s2.len() && #[trigger] trigger(s2[i2]) implies exists|i1: int|
        0 <= i1 < s.len() && s[i1] == s2[i2] by {
        assert(s[i + i2] == s2[i2]);
    }
    axiom_seq_len_decreases(s, s2);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
{
    broadcast use lemma_seq_empty;

}

pub broadcast proof fn lemma_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
{
    let s = Seq::<A>::empty();
    match s.inner {
        SeqInner::Nil => {
            assert(s == Seq { inner: SeqInner::Nil });
        },
        SeqInner::Cons { tail, .. } => {
            let seq_tail = Seq { inner: tail@ };
            assert(s.len() == 1 + seq_tail.len());
            assert(s.len() > 0);
        },
    }
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_new_len<A>(len: nat, f: spec_fn(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
{
    lemma_seq_new_len(len, f)
}

pub broadcast proof fn lemma_seq_new_len<A>(len: nat, f: spec_fn(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
    decreases len,
{
    let s = Seq::new(len, f);
    if len == 0 {
        assert(s.len() == 0);
    } else {
        broadcast use lemma_seq_push_len;

        let pref = Seq::new((len - 1) as nat, f);
        lemma_seq_new_len((len - 1) as nat, f);
        assert(pref.len() == (len - 1) as nat);

        let s2 = pref.push(f(len - 1));
        assert(s2.len() == pref.len() + 1);

        assert(s == s2);
        assert(s.len() == len);
    }
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_new_index<A>(len: nat, f: spec_fn(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        #[trigger] Seq::new(len, f)[i] == f(i),
{
    lemma_seq_new_index(len, f, i)
}

pub broadcast proof fn lemma_seq_new_index<A>(len: nat, f: spec_fn(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        #[trigger] Seq::new(len, f)[i] == f(i),
    decreases len,
{
    broadcast use lemma_seq_new_len;

    let s = Seq::new(len, f);
    assert(s.len() == len);

    let pref = Seq::new((len - 1) as nat, f);
    assert(pref.len() == len - 1);

    let a = f(len - 1);
    assert(s == pref.push(a));

    if i == len - 1 {
        lemma_seq_push_index_same(pref, a, i);
        assert(s[i] == a);
    } else {
        assert(0 <= i < (len - 1));
        lemma_seq_new_index((len - 1) as nat, f, i);
        lemma_seq_push_index_different(pref, a, i);
    }
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
{
    lemma_seq_push_len(s, a)
}

pub broadcast proof fn lemma_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
{
    seq_inner::lemma_push_len(s.inner, a)
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
{
    lemma_seq_push_index_same(s, a, i)
}

pub broadcast proof fn lemma_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
{
    seq_inner::lemma_push_index_same(s.inner, a, i);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    requires
        i < s.len(),
    ensures
        #[trigger] s.push(a)[i] == s[i],
{
    lemma_seq_push_index_different(s, a, i)
}

pub broadcast proof fn lemma_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    requires
        i < s.len(),
    ensures
        #[trigger] s.push(a)[i] == s[i],
{
    seq_inner::lemma_push_index_different(s.inner, a, i);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_push_index_different_alt<A>(s: Seq<A>, a: A, i: int)
    requires
        i < s.len(),
    ensures
        (#[trigger] s.push(a))[i] == #[trigger] s[i],
{
    lemma_seq_push_index_different_alt(s, a, i)
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_push_index_different_alt<A>(s: Seq<A>, a: A, i: int)
    requires
        i < s.len(),
    ensures
        (#[trigger] s.push(a))[i] == #[trigger] s[i],
{
    broadcast use lemma_seq_push_index_different;

}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
{
    lemma_seq_update_len(s, i, a)
}

pub broadcast proof fn lemma_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
    decreases i,
{
    seq_inner::lemma_update_len(s.inner, i, a)
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
{
    lemma_seq_update_same(s, i, a)
}

pub broadcast proof fn lemma_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
{
    seq_inner::lemma_update_index_same(s.inner, i, a);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_update_same_alt<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #![trigger s.update(i, a), s[i]]
        s.update(i, a)[i] == a,
{
    lemma_seq_update_same_alt(s, i, a)
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_update_same_alt<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #![trigger s.update(i, a), s[i]]
        s.update(i, a)[i] == a,
{
    broadcast use lemma_seq_update_same;

}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        i1 != i2,
    ensures
        #[trigger] s.update(i2, a)[i1] == s[i1],
{
    lemma_seq_update_different(s, i1, i2, a)
}

pub broadcast proof fn lemma_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        i1 != i2,
    ensures
        #[trigger] s.update(i2, a)[i1] == s[i1],
{
    seq_inner::lemma_update_index_different(s.inner, i1, i2, a);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_update_different_alt<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        i1 != i2,
    ensures
        (#[trigger] s.update(i2, a))[i1] == #[trigger] s[i1],
{
    lemma_seq_update_different_alt(s, i1, i2, a)
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_update_different_alt<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        i1 != i2,
    ensures
        (#[trigger] s.update(i2, a))[i1] == #[trigger] s[i1],
{
    broadcast use lemma_seq_update_different;

}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
{
    lemma_seq_ext_equal(s1, s2)
}

pub broadcast proof fn lemma_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
    decreases s1.len(),
{
    match s1.inner {
        SeqInner::Nil => {
            assert(s1.len() == s2.len() <==> s1 =~= s2);
        },
        SeqInner::Cons { head: head1, tail: tail1 } => {
            let seq_tail1 = Seq { inner: tail1@ };

            match s2.inner {
                SeqInner::Nil => {
                    assert(s1.len() != s2.len());
                },
                SeqInner::Cons { head: head2, tail: tail2 } => {
                    if head1 != head2 {
                        assert(s1[0] != s2[0]);
                    } else {
                        let seq_tail2 = Seq { inner: tail2@ };
                        lemma_seq_ext_equal(seq_tail1, seq_tail2);
                        if seq_tail1 =~= seq_tail2 {
                            assert(s1.len() == seq_tail1.len() + 1 == seq_tail2.len() + 1
                                == s2.len());
                            assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
                                if i == 0 {
                                    assert(s1[0] == s2[0]);
                                } else {
                                    assert(s1[i] == s2[i]);
                                }
                            }
                        } else if seq_tail1.len() == seq_tail2.len() {
                            assert(exists|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i]);
                            let i = choose|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i];
                            assert(s1[i + 1] != s2[i + 1]);
                        } else {
                            assert(s1.len() != s2.len());
                        }
                    }
                },
            }
        },
    }
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
{
    lemma_seq_ext_equal_deep(s1, s2)
}

pub broadcast proof fn lemma_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
{
    match s1.inner {
        SeqInner::Nil => {
            assert(s1.len() == s2.len() <==> s1 =~~= s2);
        },
        SeqInner::Cons { head: head1, tail: tail1 } => {
            let seq_tail1 = Seq { inner: tail1@ };

            match s2.inner {
                SeqInner::Nil => {
                    assert(s1.len() != s2.len());
                },
                SeqInner::Cons { head: head2, tail: tail2 } => {
                    if head1 != head2 {
                        assert(s1[0] != s2[0]);
                    } else {
                        let seq_tail2 = Seq { inner: tail2@ };
                        lemma_seq_ext_equal(seq_tail1, seq_tail2);
                        if seq_tail1 =~~= seq_tail2 {
                            assert(s1.len() == seq_tail1.len() + 1 == seq_tail2.len() + 1
                                == s2.len());
                            assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
                                if i == 0 {
                                    assert(s1[0] == s2[0]);
                                } else {
                                    assert(s1[i] == s2[i]);
                                }
                            }
                        } else if seq_tail1.len() == seq_tail2.len() {
                            assert(exists|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i]);
                            let i = choose|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i];
                            assert(s1[i + 1] != s2[i + 1]);
                        } else {
                            assert(s1.len() != s2.len());
                        }
                    }
                },
            }
        },
    }
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
{
    lemma_seq_subrange_len(s, j, k)
}

pub broadcast proof fn lemma_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
{
    seq_inner::lemma_subrange_len(s.inner, j, k)
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        #[trigger] s.subrange(j, k)[i] == s[i + j],
{
    lemma_seq_subrange_index(s, j, k, i)
}

pub broadcast proof fn lemma_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        #[trigger] s.subrange(j, k)[i] == s[i + j],
{
    seq_inner::lemma_subrange_index(s.inner, j, k, i);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_subrange_index_alt<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i - j < k - j,
    ensures
        (#[trigger] s.subrange(j, k))[i - j] == #[trigger] s[i],
{
    lemma_seq_subrange_index_alt(s, j, k, i)
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_subrange_index_alt<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i - j < k - j,
    ensures
        (#[trigger] s.subrange(j, k))[i - j] == #[trigger] s[i],
{
    broadcast use lemma_seq_subrange_index;

}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_two_subranges_index<A>(s: Seq<A>, j: int, k1: int, k2: int, i: int)
    requires
        0 <= j <= k1 <= s.len(),
        0 <= j <= k2 <= s.len(),
        0 <= i < k1 - j,
        0 <= i < k2 - j,
    ensures
        #[trigger] s.subrange(j, k1)[i] == (#[trigger] s.subrange(j, k2))[i],
{
    lemma_seq_two_subranges_index(s, j, k1, k2, i)
}

// Less expensive, more limited alternative to lemma_seq_subrange_index_alt
pub broadcast proof fn lemma_seq_two_subranges_index<A>(s: Seq<A>, j: int, k1: int, k2: int, i: int)
    requires
        0 <= j <= k1 <= s.len(),
        0 <= j <= k2 <= s.len(),
        0 <= i < k1 - j,
        0 <= i < k2 - j,
    ensures
        #[trigger] s.subrange(j, k1)[i] == (#[trigger] s.subrange(j, k2))[i],
{
    broadcast use lemma_seq_subrange_index;

}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] s1.add(s2).len() == s1.len() + s2.len(),
{
    lemma_seq_add_len(s1, s2)
}

pub broadcast proof fn lemma_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] s1.add(s2).len() == s1.len() + s2.len(),
{
    seq_inner::lemma_add_len(s1.inner, s2.inner);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        i < s1.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s1[i],
{
    lemma_seq_add_index1(s1, s2, i)
}

pub broadcast proof fn lemma_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        i < s1.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s1[i],
{
    seq_inner::lemma_add_index1(s1.inner, s2.inner, i)
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        s1.len() <= i < s1.len() + s2.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s2[i - s1.len()],
{
    lemma_seq_add_index2(s1, s2, i)
}

pub broadcast proof fn lemma_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        s1.len() <= i < s1.len() + s2.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s2[i - s1.len()],
{
    seq_inner::lemma_add_index2(s1.inner, s2.inner, i);
}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_add_index1_alt<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        (#[trigger] s1.add(s2))[i] == #[trigger] s1[i],
{
    lemma_seq_add_index1_alt(s1, s2, i)
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_add_index1_alt<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        (#[trigger] s1.add(s2))[i] == #[trigger] s1[i],
{
    broadcast use lemma_seq_add_index1;

}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast proof fn axiom_seq_add_index2_alt<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s2.len(),
    ensures
        (#[trigger] s1.add(s2))[i + s1.len()] == #[trigger] s2[i],
{
    lemma_seq_add_index2_alt(s1, s2, i);
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_add_index2_alt<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s2.len(),
    ensures
        (#[trigger] s1.add(s2))[i + s1.len()] == #[trigger] s2[i],
{
    broadcast use lemma_seq_add_index2;

}

#[deprecated(note = "Seq axioms have been verified, and are now lemmas")]
pub broadcast group group_seq_axioms {
    lemma_seq_index_decreases,
    lemma_seq_subrange_decreases,
    lemma_seq_empty,
    lemma_seq_new_len,
    lemma_seq_new_index,
    lemma_seq_push_len,
    lemma_seq_push_index_same,
    lemma_seq_push_index_different,
    lemma_seq_update_len,
    lemma_seq_update_same,
    lemma_seq_update_different,
    lemma_seq_ext_equal,
    lemma_seq_ext_equal_deep,
    lemma_seq_subrange_len,
    lemma_seq_subrange_index,
    lemma_seq_two_subranges_index,
    lemma_seq_add_len,
    lemma_seq_add_index1,
    lemma_seq_add_index2,
}

pub broadcast group group_seq_lemmas {
    lemma_seq_index_decreases,
    lemma_seq_subrange_decreases,
    lemma_seq_empty,
    lemma_seq_new_len,
    lemma_seq_new_index,
    lemma_seq_push_len,
    lemma_seq_push_index_same,
    lemma_seq_push_index_different,
    lemma_seq_update_len,
    lemma_seq_update_same,
    lemma_seq_update_different,
    lemma_seq_ext_equal,
    lemma_seq_ext_equal_deep,
    lemma_seq_subrange_len,
    lemma_seq_subrange_index,
    lemma_seq_two_subranges_index,
    lemma_seq_add_len,
    lemma_seq_add_index1,
    lemma_seq_add_index2,
}

// Expensive lemmas not in the default group (may slow down verification)
pub broadcast group group_seq_lemmas_expensive {
    lemma_seq_push_index_different_alt,
    lemma_seq_update_same_alt,
    lemma_seq_update_different_alt,
    lemma_seq_subrange_index_alt,
    lemma_seq_add_index1_alt,
    lemma_seq_add_index2_alt,
}

// ------------- Macros ---------------- //
#[doc(hidden)]
#[macro_export]
macro_rules! seq_internal {
    [] => {
        $crate::vstd::seq::Seq::empty()
    };
    [$elem:expr] => {
        $crate::vstd::seq::Seq::empty()
            .push($elem)
    };
    [$elem:expr,] => {
        $crate::vstd::seq::Seq::empty()
            .push($elem)
    };
    [$($elem:expr),* $(,)?] => {
        <_ as $crate::vstd::view::View>::view(&[$($elem),*])
    };
    [$elem:expr; $n:expr] => {
        $crate::vstd::seq::Seq::new(
            $n,
            $crate::vstd::prelude::closure_to_fn_spec(
                |_x: _| $elem
            ),
        )
    };
}

/// Creates a [`Seq`] containing the given elements.
///
/// ## Example
///
/// ```rust
/// let s = seq![11int, 12, 13];
///
/// assert(s.len() == 3);
/// assert(s[0] == 11);
/// assert(s[1] == 12);
/// assert(s[2] == 13);
/// ```
#[macro_export]
macro_rules! seq {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::seq::seq_internal!($($tail)*))
    };
}

#[doc(hidden)]
pub use seq_internal;
pub use seq;

} // verus!
