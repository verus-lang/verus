#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use vstd::seq::*;
use vstd::{pervasive::*, *};

use state_machines_macros::state_machine;

verus! {

pub open spec fn ids_distinct(ids: Seq<int>) -> bool {
    forall|i: int, j: int|
        i != j && 0 <= i && i < ids.len() && 0 <= j && j < ids.len() ==> ids.index(i) != ids.index(
            j,
        )
}

pub open spec fn between(start: int, node: int, end: int) -> bool {
    if start < end {
        start < node && node < end
    } else {
        node < end || start < node
    }
}

pub open spec fn max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

} // verus!
state_machine!(
    X {
        fields {
            pub ids: Seq<int>, // constant
            pub highest_heard: Seq<int>,
        }

        init!{
            ini(ids: Seq<int>) {
                require(ids_distinct(ids));
                require(forall |k| 0 <= k < ids.len() ==> ids[k] >= 0);
                init ids = ids;
                init highest_heard = Seq::new(ids.len(), |i: int| -1);
            }
        }

        transition!{
            transmission(srcidx: int) {
                require(0 <= srcidx && srcidx < pre.ids.len());

                let dstidx = if srcidx + 1 == pre.ids.len() { 0 } else { srcidx + 1 };
                let message = max(pre.highest_heard.index(srcidx), pre  .ids.index(srcidx));
                let dst_new_max = max(pre.highest_heard.index(dstidx), message);

                update highest_heard = pre.highest_heard.update(dstidx, dst_new_max);
            }
        }

        #[invariant]
        pub fn inv_lengths_match(self) -> bool {
            self.ids.len() == self.highest_heard.len()
        }

        #[invariant]
        pub fn inv_ids_distinct(self) -> bool {
            ids_distinct(self.ids)
        }

        pub open spec fn is_leader(self, i: int) -> bool {
            0 <= i && i < self.ids.len() &&
                self.highest_heard.index(i) == self.ids.index(i)
        }

        #[invariant]
        pub fn safety_condition(self) -> bool {
            forall |i: int, j: int|
                self.is_leader(i) && self.is_leader(j) ==> i == j
        }

        pub open spec fn OnChordHeardDominatesId(self, start: int, end: int) -> bool {
            forall |node: int| between(start, node, end) && self.valid_idx(node)
                ==> self.highest_heard.index(node) > self.ids.index(node)
        }

        pub open spec fn valid_idx(self, i: int) -> bool {
            0 <= i && i < self.ids.len()
        }

        pub open spec fn is_chord(self, start: int, end: int) -> bool {
               self.valid_idx(start)
            && self.valid_idx(end)
            && self.ids.index(start) == self.highest_heard.index(end)
        }

        #[invariant]
        pub fn on_chord_heard_dominates_id_inv(self) -> bool {
            forall |start: int, end: int|
                self.is_chord(start, end) ==> self.OnChordHeardDominatesId(start, end)
        }

        #[inductive(transmission)]
        pub fn preserves_ind(pre: Self, post: Self, srcidx: int) {
            // XXX(travis): this sort of copy-paste is extremely common, we could have
            // a language feature to let us skip it
            let dstidx = if srcidx + 1 == pre.ids.len() { 0 } else { srcidx + 1 };
            let message = max(pre.highest_heard.index(srcidx), pre.ids.index(srcidx));
            let dst_new_max = max(pre.highest_heard.index(dstidx), message);

            assert_by(post.on_chord_heard_dominates_id_inv(), {
              assert forall |start: int, end: int| post.is_chord(start, end)
                implies post.OnChordHeardDominatesId(start, end)
              by {
                assert forall |node: int|
                  between(start, node, end) && post.valid_idx(node)
                  implies post.highest_heard.index(node) > post.ids.index(node)
                by {
                  if dstidx == end {
                    // maybe this chord just sprung into existence
                    if post.highest_heard.index(end) == pre.highest_heard.index(end) {
                      // no change --
                      assert(pre.highest_heard =~= post.highest_heard);
                      assert(equal(pre.highest_heard, post.highest_heard));
                      assert(equal(pre, post));
                      assert(post.highest_heard.index(node) > post.ids.index(node));
                    } else if post.highest_heard.index(end) == pre.ids.index(srcidx) {
                      assert(false); // proof by contradiction
                      assert(post.highest_heard.index(node) > post.ids.index(node));
                    } else if post.highest_heard.index(end) == pre.highest_heard.index(srcidx) {
                      assert(pre.is_chord(start, srcidx));  // trigger
                      assert(pre.valid_idx(node));
                      assert(post.highest_heard.index(node) > post.ids.index(node));
                    }
                  } else {
                    // this chord was already here
                    assert(pre.is_chord(start, end)); // trigger
                    assert(pre.valid_idx(node)); // trigger
                    assert(post.highest_heard.index(node) > post.ids.index(node));
                  }
                }
              }
            });

            assert_by(post.safety_condition(), {
                assert forall |i: int, j: int|
                    post.is_leader(i) && post.is_leader(j) implies i == j
                by {

                    if i != j {
                        if pre.is_leader(i) {
                            assert(pre.is_chord(i, i));
                            //assert(pre.OnChordHeardDominatesId(i, i));
                            //assert(between(i, j, i));
                            assert(pre.valid_idx(j));
                            //assert(pre.highest_heard.index(j) > pre.ids.index(j));
                            assert(!post.is_leader(j));
                            assert(false);
                        }

                        if pre.is_leader(j) {
                            assert(pre.is_chord(j, j));
                            assert(pre.valid_idx(i));
                            assert(!post.is_leader(i));
                            assert(false);
                        }
                    }
                }
            });
        }

        #[inductive(ini)]
        pub fn ind_on_ini(post: Self, ids: Seq<int>) {
            assert(post.on_chord_heard_dominates_id_inv());
        }
    }
);

fn main() {}
