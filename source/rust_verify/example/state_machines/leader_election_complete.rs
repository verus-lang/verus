#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::seq::*;

use state_machines_macros::state_machine;

#[spec]
pub fn ids_distinct(ids: Seq<nat>) -> bool {
    forall(|i: int, j: int|
        i != j && 0 <= i && i < ids.len() && 0 <= j && j < ids.len()
          >>= ids.index(i) != ids.index(j)
    )
}

#[spec]
pub fn between(start: int, node: int, end: int) -> bool
{
  if start < end { start < node && node < end } else { node < end || start < node }
}

#[spec]
pub fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}


state_machine!(
    X {
        fields {
            pub ids: Seq<nat>, // constant
            pub highest_heard: Seq<int>,
        }

        #[init]
        pub fn init(ids: Seq<nat>) {
            require(ids_distinct(ids));
            init(ids, ids);
            init(highest_heard, Seq::new(ids.len(), |i: int| -1));
        }

        #[transition]
        pub fn transmission(self, srcidx: nat) {
            require(0 <= srcidx && srcidx < self.ids.len());

            let dstidx = if srcidx + 1 == self.ids.len() { 0 } else { srcidx + 1 };
            let message = max(self.highest_heard.index(srcidx), self.ids.index(srcidx));
            let dst_new_max = max(self.highest_heard.index(dstidx), message);

            update(highest_heard, self.highest_heard.update(dstidx, dst_new_max));
        }

        #[invariant]
        pub fn inv_lengths_match(self) -> bool {
            self.ids.len() == self.highest_heard.len()
        }

        #[invariant]
        pub fn inv_ids_distinct(self) -> bool {
            ids_distinct(self.ids)
        }

        #[spec]
        pub fn is_leader(self, i: int) -> bool {
            0 <= i && i < self.ids.len() &&
                self.highest_heard.index(i) == self.ids.index(i)
        }

        #[invariant]
        pub fn safety_condition(self) -> bool {
            forall(|i: int, j: int|
                self.is_leader(i) && self.is_leader(j) >>= i == j)
        }

        #[spec]
        pub fn OnChordHeardDominatesId(self, start: int, end: int) -> bool {
            forall(|node: int| between(start, node, end) && self.valid_idx(node)
                >>= self.highest_heard.index(node) > self.ids.index(node))
        }

        #[spec]
        pub fn valid_idx(self, i: int) -> bool {
            0 <= i && i < self.ids.len()
        }

        #[spec]
        pub fn is_chord(self, start: int, end: int) -> bool {
               self.valid_idx(start)
            && self.valid_idx(end)
            && self.ids.index(start) == self.highest_heard.index(end)
        }

        #[invariant]
        pub fn on_chord_heard_dominates_id_inv(self) -> bool {
            forall(|start: int, end: int|
                self.is_chord(start, end) >>= self.OnChordHeardDominatesId(start, end))
        }

        #[inductive(transmission)]
        pub fn preserves_ind(self: X, post: X, srcidx: nat) {
            // XXX(travis): this sort of copy-paste is extremely common, we could have
            // a language feature to let us skip it
            let dstidx = if srcidx + 1 == self.ids.len() { 0 } else { srcidx + 1 };
            let message = max(self.highest_heard.index(srcidx), self.ids.index(srcidx));
            let dst_new_max = max(self.highest_heard.index(dstidx), message);

            assert_by(post.on_chord_heard_dominates_id_inv(), {
              assert_forall_by(|start: int, end: int| {
                requires(post.is_chord(start, end));
                ensures(post.OnChordHeardDominatesId(start, end));
                assert_forall_by(|node: int| {
                  requires(between(start, node, end) && post.valid_idx(node));
                  ensures(post.highest_heard.index(node) > post.ids.index(node));
                  if dstidx == end {
                    // maybe this chord just sprung into existence
                    if post.highest_heard.index(end) == self.highest_heard.index(end) {
                      // no change -- 
                      assert(self.highest_heard.ext_equal(post.highest_heard));
                      assert(equal(self.highest_heard, post.highest_heard));
                      assert(equal(self, post));
                      assert(post.highest_heard.index(node) > post.ids.index(node));
                    } else if post.highest_heard.index(end) == self.ids.index(srcidx) {
                      assert(false); // proof by contradiction
                      assert(post.highest_heard.index(node) > post.ids.index(node));
                    } else if post.highest_heard.index(end) == self.highest_heard.index(srcidx) {
                      assert(self.is_chord(start, srcidx));  // trigger
                      assert(post.highest_heard.index(node) > post.ids.index(node));
                    }
                  } else {
                    // this chord was already here
                    assert(self.is_chord(start, end)); // trigger
                    assert(self.valid_idx(node)); // trigger
                    assert(post.highest_heard.index(node) > post.ids.index(node));
                  }
                });
              });
            });

            assert_by(post.safety_condition(), {
                assert_forall_by(|i: int, j: int| {
                    requires(post.is_leader(i) && post.is_leader(j));
                    ensures(i == j);

                    assert(self.is_chord(i, i));
                    assert(self.is_chord(j, j));
                });
            });
        }

        #[inductive(init)]
        pub fn ind_on_init(post: X, ids: Seq<nat>) {
            assert(post.on_chord_heard_dominates_id_inv());
        }
    }
);

fn main() { }
