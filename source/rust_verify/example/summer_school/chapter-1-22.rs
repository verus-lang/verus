#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;

#[allow(unused_imports)]
use seq::*;
#[allow(unused_imports)]
use vec::*;

#[is_variant] #[derive(PartialEq, Eq)] // TODO(utaal): Structural is not implemented for Box
enum Tree {
    Nil,
    Node { value: i64, left: Box<Tree>, right: Box<Tree> },
}

impl Tree {
    #[spec] fn view(&self) -> Seq<int> {
        decreases(self);
        match *self {
            Tree::Nil => seq![],
            Tree::Node { value, left, right } => left.view().add(seq![value as int]).add(right.view()),
        }
    }

    #[spec] fn is_sorted(&self) -> bool {
        decreases(self);
        match *self {
            Tree::Nil => true,
            Tree::Node { value, left, right } => true
                && sequences_ordered_at_interface(left.view(), seq![value])
                && sequences_ordered_at_interface(seq![value], right.view())
                && left.is_sorted()
                && right.is_sorted()
        }
    }

    // #[proof] fn sorted_tree_means_sorted_sequence(&self) // TODO(utaal): is self being Spec too restrictive?
}

#[spec]
fn sequences_ordered_at_interface(seq1: Seq<int>, seq2: Seq<int>) -> bool {
    if seq1.len() == 0 || seq2.len() == 0 {
        true
    } else {
        seq1.last() <= seq2.index(0)
    }
}

#[spec] fn sequence_is_sorted(s: Seq<int>) -> bool {
    forall(|i: nat, j: nat| i < j && j < s.len() >>= s.index(i) <= s.index(j))
}

// TODO: change the default for --multiple-errors
// we can have --jon-mode :p
// TODO: shall multiple errors in the same method be sorted?
#[proof] fn sorted_tree_means_sorted_sequence(tree: Tree) {
    decreases(tree); // guessed by Dafny
    requires(tree.is_sorted());
    ensures(sequence_is_sorted(tree.view()));

    // reveal_with_fuel(sorted_tree_means_sorted_sequence, 3); // TODO(utaal) ICE revealing current method with fuel panics in AIR
    if let Tree::Node { left, right, value: _ } = tree {
        sorted_tree_means_sorted_sequence(*left); // guessed by Dafny
        sorted_tree_means_sorted_sequence(*right); // guessed by Dafny
    }
}

#[is_variant] #[derive(Eq, PartialEq, Structural)]
enum TreeSortedness {
    Unsorted,
    Empty,
    Bounded(i64, i64),
}

fn check_is_sorted_tree(tree: &Tree) -> TreeSortedness {
    decreases(tree);
    ensures(|ret: TreeSortedness| [
        tree.is_sorted() == !ret.is_Unsorted(),
        tree.is_Nil() == ret.is_Empty(),
        if let TreeSortedness::Bounded(l, r) = ret {
            l == tree.view().index(0) && r == tree.view().last()
        } else { true }
        // TODO: suboptimal span for error message:
        // error: postcondition not satisfied
        //   --> rust_verify/example/summer_school.rs:82:13
        //    |
        // 82 |             TreeSortedness::Unsorted => true,
        //    |             ^^^^^^^^^^^^^^^^^^^^^^^^
    ]);

    match tree {
        Tree::Nil => TreeSortedness::Empty,
        Tree::Node { left, right, value } => {
            let left_sortedness = check_is_sorted_tree(left);
            let left_bound;
            match left_sortedness {
                TreeSortedness::Unsorted => return TreeSortedness::Unsorted,
                TreeSortedness::Empty => left_bound = *value,
                TreeSortedness::Bounded(ll, lr) => if !(lr <= *value) {
                    // assert(!sequences_ordered_at_interface(left.view(), seq![*value as int]));
                    // assert(!tree.is_sorted());
                    return TreeSortedness::Unsorted;
                } else {
                    // assert(left.view().index(0) == ll);
                    // assert(left.view().last() == lr);
                    // assert(sequences_ordered_at_interface(left.view(), seq![*value as int]));
                    left_bound = ll;
                },
            }

            // assert(left.is_Nil() >>= left_sortedness.is_Empty());
            // assert(left_sortedness.is_Empty() >>= left.is_Nil());

            let right_sortedness = check_is_sorted_tree(right);
            let right_bound;
            match right_sortedness {
                TreeSortedness::Unsorted => return TreeSortedness::Unsorted,
                TreeSortedness::Empty => right_bound = *value,
                TreeSortedness::Bounded(rl, rr) => if !(*value <= rl) {
                    // assert(!sequences_ordered_at_interface(seq![*value as int], right.view()));
                    // assert(!tree.is_sorted());
                    return TreeSortedness::Unsorted;
                } else {
                    // assert(*value <= rl);
                    // assert(right.view().last() == rr);
                    // assert(right.view().index(0) == rl);
                    // assert(seq![*value as int].last() == *value as int);
                    // assert(sequences_ordered_at_interface(seq![*value as int], right.view()));
                    right_bound = rr;
                },
            }

            sorted_tree_means_sorted_sequence(**left);
            // sorted_tree_means_sorted_sequence(**right); // TODO: why is only one of these calls
            // necessary?

            // assert(equal(tree.view(), left.view().add(seq![*value as int]).add(right.view())));
            // assert(tree.view().len() > 0);

            // assert(left.is_sorted());
            // assert(right.is_sorted());
            // assert(sequences_ordered_at_interface(left.view(), seq![*value as int]));
            // assert(sequences_ordered_at_interface(seq![*value as int], right.view()));
            // assert(tree.is_sorted());

            // TODO cannot use proof variable inside forall/assert_by statements (left)
            // #[spec] let left = left;
            // assert_by(left_bound == tree.view().index(0), {
            //     if left.is_Nil() {
            //         assert(left_sortedness.is_Empty());
            //         assert(*value as int == tree.view().index(0));
            //         assert(left_bound == *value);
            //         assert(left_bound == tree.view().index(0));
            //     } else {
            //         assert(left_bound == tree.view().index(0));
            //     }
            // });
            // assert(right_bound == tree.view().last());
            TreeSortedness::Bounded(left_bound, right_bound)
        }
    }
}


fn main() {}
