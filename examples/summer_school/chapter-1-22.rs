#[allow(unused_imports)]
use prelude::*;
#[allow(unused_imports)]
use seq::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::*;

verus! {

#[is_variant]
#[derive(PartialEq, Eq)]  // TODO(utaal): Structural is not implemented for Box
enum Tree {
    Nil,
    Node { value: i64, left: Box<Tree>, right: Box<Tree> },
}

impl Tree {
    spec fn view(&self) -> Seq<int>
        decreases self,
    {
        match *self {
            Tree::Nil => seq![],
            Tree::Node { value, left, right } => left@.add(seq![value as int]).add(right@),
        }
    }

    spec fn is_sorted(&self) -> bool
        decreases self,
    {
        match *self {
            Tree::Nil => true,
            Tree::Node { value, left, right } => {
                &&& sequences_ordered_at_interface(left@, seq![value as int])
                &&& sequences_ordered_at_interface(seq![value as int], right@)
                &&& left.is_sorted()
                &&& right.is_sorted()
            },
        }
    }// #[verifier::proof] fn sorted_tree_means_sorted_sequence(&self)
    // TODO(utaal): is self being Spec too restrictive?

}

spec fn sequences_ordered_at_interface(seq1: Seq<int>, seq2: Seq<int>) -> bool {
    if seq1.len() == 0 || seq2.len() == 0 {
        true
    } else {
        seq1.last() <= seq2[0]
    }
}

spec fn sequence_is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// TODO: change the default for --multiple-errors
// we can have --jon-mode :p
// TODO: shall multiple errors in the same method be sorted?
proof fn sorted_tree_means_sorted_sequence(tree: Tree)
    requires
        tree.is_sorted(),
    ensures
        sequence_is_sorted(tree@),
    decreases tree  // guessed by Dafny ,
{
    // reveal_with_fuel(sorted_tree_means_sorted_sequence, 3); // TODO(utaal) ICE revealing current method with fuel panics in AIR
    if let Tree::Node { left, right, value: _ } = tree {
        sorted_tree_means_sorted_sequence(*left);  // guessed by Dafny
        sorted_tree_means_sorted_sequence(*right);  // guessed by Dafny
    }
}

#[is_variant]
#[derive(Eq, PartialEq, Structural)]
enum TreeSortedness {
    Unsorted,
    Empty,
    Bounded(i64, i64),
}

fn check_is_sorted_tree(tree: &Tree) -> (ret: TreeSortedness)
    ensures
        tree.is_sorted() == !ret.is_Unsorted(),
        tree.is_Nil() == ret.is_Empty(),
        if let TreeSortedness::Bounded(l, r) = ret {
            l == tree@[0] && r == tree@.last()
        } else {
            true
        },
// TODO: suboptimal span for error message:
// error: postcondition not satisfied
//   --> rust_verify/example/summer_school.rs:82:13
//    |
// 82 |             TreeSortedness::Unsorted => true,
//    |             ^^^^^^^^^^^^^^^^^^^^^^^^

    decreases tree,
{
    match tree {
        Tree::Nil => TreeSortedness::Empty,
        Tree::Node { left, value, right } => {
            let left_sortedness = check_is_sorted_tree(left);
            let left_bound;
            match left_sortedness {
                TreeSortedness::Unsorted => return TreeSortedness::Unsorted,
                TreeSortedness::Empty => left_bound = *value,
                TreeSortedness::Bounded(ll, lr) => if !(lr <= *value) {
                    // assert(!sequences_ordered_at_interface(left@, seq![*value as int]));
                    // assert(!tree.is_sorted());
                    return TreeSortedness::Unsorted;
                } else {
                    // assert(left@[0] == ll);
                    // assert(left@.last() == lr);
                    // assert(sequences_ordered_at_interface(left@, seq![*value as int]));
                    left_bound = ll;
                },
            }
            // assert(left.is_Nil() ==> left_sortedness.is_Empty());
            // assert(left_sortedness.is_Empty() ==> left.is_Nil());

            let right_sortedness = check_is_sorted_tree(right);
            let right_bound;
            match right_sortedness {
                TreeSortedness::Unsorted => return TreeSortedness::Unsorted,
                TreeSortedness::Empty => right_bound = *value,
                TreeSortedness::Bounded(rl, rr) => if !(*value <= rl) {
                    // assert(!sequences_ordered_at_interface(seq![*value as int], right@));
                    // assert(!tree.is_sorted());
                    return TreeSortedness::Unsorted;
                } else {
                    // assert(*value <= rl);
                    // assert(right@.last() == rr);
                    // assert(right@[0] == rl);
                    // assert(seq![*value as int].last() == *value as int);
                    // assert(sequences_ordered_at_interface(seq![*value as int], right@));
                    right_bound = rr;
                },
            }
            proof {
                sorted_tree_means_sorted_sequence(**left);
                sorted_tree_means_sorted_sequence(**right);
            }
            // assert(equal(tree@, left@.add(seq![*value as int]).add(right@)));
            // assert(tree@.len() > 0);
            // assert(left.is_sorted());
            // assert(right.is_sorted());
            // assert(sequences_ordered_at_interface(left@, seq![*value as int]));
            // assert(sequences_ordered_at_interface(seq![*value as int], right@));
            // assert(tree.is_sorted());
            // TODO cannot use proof variable inside forall/assert_by statements (left)
            // #[verifier::spec] let left = left;
            // assert_by(left_bound == tree@[0], {
            //     if left.is_Nil() {
            //         assert(left_sortedness.is_Empty());
            //         assert(*value as int == tree@[0]);
            //         assert(left_bound == *value);
            //         assert(left_bound == tree@[0]);
            //     } else {
            //         assert(left_bound == tree@[0]);
            //     }
            // });
            assert(right_bound == tree@.last());
            TreeSortedness::Bounded(left_bound, right_bound)
        },
    }
}

fn find_in_binary_tree(tree: &Tree, needle: i64) -> (ret: bool)
    requires
        tree.is_sorted(),
    ensures
        ret == tree@.contains(needle as int),
    decreases tree,
{
    match tree {
        Tree::Nil => false,
        Tree::Node { left, value, right } => {
            if needle == *value {
                assert(tree@[left@.len() as int] == needle);  // trigger
                true
            } else if needle < *value {
                let ret = find_in_binary_tree(left, needle);
                if ret {
                    //let idx = choose(|idx: nat| idx < left@.len() && left@.index(nat) == needle); // TODO(utaal): bad error message for stray nat?
                    proof {
                        let idx = choose|idx: int| 0 <= idx < left@.len() && left@[idx] == needle;
                        assert(tree@[idx] == needle);  // trigger
                    }
                } else {
                    proof {
                        sorted_tree_means_sorted_sequence(**right);
                    }
                    //                    assert_forall_by(|idx: nat| {
                    //                        requires(idx < tree@.len());
                    //                        ensures(tree@.index(idx) != needle);
                    //                        if idx < left@.len() {
                    //                          assert(tree@.index(idx) != needle);
                    //                        } else if idx==left@.len() {
                    //                          assert(tree@.index(idx) != needle);
                    //                        } else {
                    //                          assert(tree@.index(idx) == right@.index(idx + left@.len() + 1));    // TODO(utaal): surprising complaint "expected struct `builtin::int`, found struct `builtin::nat`"
                    //                          #[verifier::spec] let right_idx: int = idx - (left@.len() as int + 1);
                    //                          assert(tree@.index(idx) == right@.index(right_idx));
                    // assert(sequences_ordered_at_interface(seq![*value as int], right@)); // TODO(utal): How about *value as int is just value@? And then maybe even auto_view that? How cool would that be?
                    //                          assert(sequences_ordered_at_interface(seq![*value as int], right@));
                    //                          assert(sequence_is_sorted(right@));
                    //                          if 0 < right_idx {
                    //                            assert(right@.index(0) <= right@.index(right_idx));
                    //                          }
                    //                          assert((*value as int) <= right@.index(right_idx));
                    //                          assert(tree@.index(idx) != needle);
                    //                        }
                    //                    });
                }
                //                assert(ret == tree@.contains(needle));

                ret
            } else {
                let ret = find_in_binary_tree(right, needle);
                proof {
                    if ret {
                        let idx = choose|idx: int| 0 <= idx < right@.len() && right@[idx] == needle;
                        assert(tree@[left@.len() + 1 + idx] == needle);  // trigger
                    } else {
                        sorted_tree_means_sorted_sequence(**left);
                    }
                }
                //                assert(ret == tree@.contains(needle));    // TODO(jonh): symmetric case incomplete
                ret
            }
        },
    }
}

fn main() {
}

} // verus!
