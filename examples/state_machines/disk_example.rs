// rust_verify/tests/example.rs ignore --- old experimental example
#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::option::*;
use vstd::pervasive::*;

verus! {

// Create the "authoritative-fragmentary" API for manipulating heap-like things
// (In this case, a disk.)
tokenized_state_machine!{ AuthFrag<#[verifier::reject_recursive_types] K, V> {
    fields {
        #[sharding(variable)]
        pub auth: Map<K, V>,

        #[sharding(map)]
        pub fragments: Map<K, V>,
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.fragments === self.auth
    }

    init!{
        initialize(m: Map<K, V>) {
            init auth = m;
            init fragments = m;
        }
    }

    transition!{
        update_key(key: K, new_value: V) {
            update auth = pre.auth.insert(key, new_value);

            remove fragments -= [ key => let _ ];
            add fragments += [ key => new_value ];
        }
    }

    property!{
        values_agree(key: K) {
            have fragments >= [ key => let frag_value ];
            assert(pre.auth.dom().contains(key)
                && frag_value === pre.auth.index(key));
        }
    }


    #[inductive(initialize)]
    fn init_inductive(post: Self, m: Map<K, V>) { }

    #[inductive(update_key)]
    fn update_key_inductive(pre: Self, post: Self, key: K, new_value: V) {
        assert_maps_equal!(post.fragments, post.auth);
    }
}}
// We want to show refinement between 2 systems.
// First system: a disk represented by a map from indices to blocks


#[is_variant]
pub enum Block {
    Leaf(u64),
    Node(nat, nat),
}

state_machine!{ DiskSM {
    fields {
        pub disk: Map<nat, Block>,      // root is 0
    }

    // update one of the children of the root

    transition!{
        update_child(left: bool, new_val: u64) {
            // Require that the root block is a node with 2 children.

            require(pre.disk.dom().contains(0));
            require let Block::Node(left_child, right_child) = pre.disk.index(0);

            // Get the address of the left or right child.
            let child = if left { left_child } else { right_child };

            // Require the child to be a leaf.
            require(pre.disk.dom().contains(child));
            require let Block::Leaf(val) = pre.disk.index(child);

            // Update the value at the leaf to a new value.
            update disk[child] = Block::Leaf(new_val);
        }
    }
}}
// state machine 2: tree


#[is_variant]
pub enum Tree {
    Leaf(u64),
    Node(Box<Tree>, Box<Tree>),
}

state_machine!{ TreeSM {
    fields {
        pub tree: Tree,
    }

    // update one of the children of the root

    transition!{
        update_child(left: bool, new_val: u64) {
            require let Tree::Node(left_child, right_child) = pre.tree;
            if left {
                require let Tree::Leaf(old_val_l) = *left_child;
                update tree = Tree::Node(Box::new(Tree::Leaf(new_val), right_child));
            } else {
                require let Tree::Leaf(old_val_r) = *right_child;
                update tree = Tree::Node(left_child, Box::new(Tree::Leaf(new_val)));
            }
        }
    }
}}
// We create the relationship with some intermediary ghost state:
//
// DiskSM::State   -->   DiskInterp   -->   LinearTree   -->   TreeSM::State
//   (spec)                (tracked)          (tracked)           (spec)
// We will devise an explicit function DiskSM::State -> DiskInterp
// and an explicit relation LinearTree -> TreeSM::State
//
// However, the relationship between DiskInterp and LinearTree will be implicit
// via ghost rules.
// First define an "interpretation" of the disk state as a linear (tracked) object DiskInterp
// This object uses the "auth" token


type DiskInterp = AuthFrag::auth<nat, Block>;

spec fn state_interp_fn(inst: AuthFrag::Instance<nat, Block>, state: DiskSM::State) -> DiskInterp {
    AuthFrag![ inst => auth => state.disk ]
}

// Define the LinearTree type
// This object uses the "fragment" tokens. This forces it to be related to the Disk.
pub enum LinearTree {
    Leaf(tracked AuthFrag::fragments<nat, Block>),
    Node(tracked AuthFrag::fragments<nat, Block>, Box<LinearTree>, Box<LinearTree>),
}

// Define the relation between LinearTree and TreeSM::State
spec fn tree_relation_rec(
    inst: AuthFrag::Instance<nat, Block>,
    lt: LinearTree,
    tree: Tree,
    addr: nat,
) -> bool
    decreases lt,
{
    match lt {
        LinearTree::Leaf(frag) => {
            match tree {
                Tree::Leaf(val) => {
                    frag === AuthFrag![ inst => fragments => addr => Block::Leaf(val) ]
                },
                Tree::Node(_, _) => false,
            }
        },
        LinearTree::Node(frag, lt_left, lt_right) => {
            match tree {
                Tree::Leaf(val) => false,
                Tree::Node(tree_left, tree_right) => {
                    &&& frag.instance === inst
                    &&& frag.key === addr
                    &&& frag.value.is_Node()
                    &&& tree_relation_rec(inst, *lt_left, *tree_left, frag.value.get_Node_0())
                    &&& tree_relation_rec(inst, *lt_right, *tree_right, frag.value.get_Node_1())
                },
            }
        },
    }
}

spec fn tree_relation(
    inst: AuthFrag::Instance<nat, Block>,
    lt: LinearTree,
    tree: TreeSM::State,
) -> bool {
    tree_relation_rec(inst, lt, tree.tree, 0)  // root is at 0

}

} // verus!
// refinement proof
// TODO this should return proof, but having trouble with mode-checking
#[verifier::proof]
fn take_step(
    state1: DiskSM::State,
    state2: DiskSM::State,
    is_left: bool,
    new_val: u64,
    #[verifier::proof] inst: AuthFrag::Instance<nat, Block>,
    #[verifier::proof] interp1: AuthFrag::auth<nat, Block>,
    #[verifier::proof] lt1: LinearTree,
    tree1_state: TreeSM::State,
) -> (Tracked<AuthFrag::auth<nat, Block>>, Tracked<LinearTree>, Gho<TreeSM::State>) {
    requires([
        DiskSM::State::update_child(state1, state2, is_left, new_val),
        equal(interp1, state_interp_fn(inst, state1)),
        tree_relation(inst, lt1, tree1_state),
    ]);
    ensures(
        |ret: (Tracked<AuthFrag::auth<nat, Block>>, Tracked<LinearTree>, Gho<TreeSM::State>)| {
            let (Tracked(interp2), Tracked(lt2), Gho(tree2)) = ret;
            equal(interp2, state_interp_fn(inst, state2))
                && TreeSM::State::update_child(tree1_state, tree2, is_left, new_val)
                && tree_relation(inst, lt2, tree2)
        },
    );
    #[verifier::proof]
    let mut interp = interp1;

    let tree1 = tree1_state.tree;

    match lt1 {
        LinearTree::Node(lt_root_fragment, lt_left, lt_right) => {
            inst.values_agree(0, &interp, &lt_root_fragment);

            if is_left {
                let left_address = lt_root_fragment.value.get_Node_0();
                assert(tree_relation_rec(inst, *lt_left, *tree1.get_Node_0(), left_address));

                match *lt_left {
                    LinearTree::Leaf(lt_leaf_fragment) => {
                        inst.values_agree(left_address, &interp, &lt_leaf_fragment);

                        let lt_leaf_fragment_new = inst.update_key(
                            lt_leaf_fragment.key,
                            Block::Leaf(new_val),
                            &mut interp,
                            lt_leaf_fragment,
                        );
                        let lt2 = LinearTree::Node(
                            lt_root_fragment,
                            Box::new(LinearTree::Leaf(lt_leaf_fragment_new)),
                            lt_right,
                        );
                        let interp2 = interp;
                        let tree2 = TreeSM::State {
                            tree: Tree::Node(Box::new(Tree::Leaf(new_val)), tree1.get_Node_1()),
                        };

                        assert(equal(interp2, state_interp_fn(inst, state2)));
                        assert(TreeSM::State::update_child(tree1_state, tree2, is_left, new_val));

                        assert(tree_relation_rec(
                            inst,
                            LinearTree::Leaf(lt_leaf_fragment_new),
                            Tree::Leaf(new_val),
                            left_address,
                        ));
                        assert(tree_relation_rec(inst, lt2, tree2.tree, 0));

                        assert(tree_relation(inst, lt2, tree2));

                        (Tracked(interp2), Tracked(lt2), Gho(tree2))
                    }
                    LinearTree::Node(lt_node_fragment, _, _) => {
                        inst.values_agree(left_address, &interp, &lt_node_fragment);

                        // by assumption, the node should be a leaf
                        proof_from_false()
                    }
                }
            } else {
                // This case should be symmetric to above
                assume(false);
                proof_from_false()
            }
        }
        LinearTree::Leaf(lt_root_fragment) => {
            inst.values_agree(0, &interp, &lt_root_fragment);

            // by assumption, root node should be a Node
            proof_from_false()
        }
    }
}

fn main() {}
