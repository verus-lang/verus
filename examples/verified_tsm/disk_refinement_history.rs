#![allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::{pervasive::*, *};
verus! {

verified_tokenized_state_machine!{  AuthFrag<#[verifier::reject_recursive_types] K, V> {
    fields {
        #[sharding(variable)]
        pub auth: Map<K, V>,

        #[sharding(map)]
        pub fragments: Map<K, V>,
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.fragments == self.auth
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
                && frag_value == pre.auth.index(key));
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

verified_state_machine_model!{ DiskSM {
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

verified_state_machine_model!{ TreeSM {
    fields {
        pub tree: Tree,
    }

    // update one of the children of the root

    transition!{
        update_child(left: bool, new_val: u64) {
            require let Tree::Node(left_child, right_child) = pre.tree;
            if left {
                require let Tree::Leaf(old_val_l) = *left_child;
                update tree = Tree::Node(Box::new(Tree::Leaf(new_val)), right_child);
            } else {
                require let Tree::Leaf(old_val_r) = *right_child;
                update tree = Tree::Node(left_child, Box::new(Tree::Leaf(new_val)));
            }
        }
    }
}}

type DiskInterp = AuthFrag::auth<nat, Block>;

spec fn state_interp_fn(
    inst: AuthFrag::Instance<nat, Block>,
    interp: DiskInterp,
    state: DiskSM::State,
) -> bool {
    interp.instance_id() == inst.id() && interp.value() == state.disk
}

pub enum LinearTree {
    Leaf(tracked AuthFrag::fragments<nat, Block>),
    Node(tracked AuthFrag::fragments<nat, Block>, Box<LinearTree>, Box<LinearTree>),
}

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
                    frag.instance_id() == inst.id() && frag.key() == addr && frag.value()
                        == Block::Leaf(val)
                },
                Tree::Node(_, _) => false,
            }
        },
        LinearTree::Node(frag, lt_left, lt_right) => {
            match tree {
                Tree::Leaf(val) => false,
                Tree::Node(tree_left, tree_right) => {
                    &&& frag.instance_id() == inst.id()
                    &&& frag.key() == addr
                    &&& frag.value() is Node
                    &&& tree_relation_rec(inst, *lt_left, *tree_left, frag.value()->Node_0)
                    &&& tree_relation_rec(inst, *lt_right, *tree_right, frag.value()->Node_1)
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
    tree_relation_rec(inst, lt, tree.tree, 0)
}

proof fn take_step(
    state1: DiskSM::State,
    state2: DiskSM::State,
    is_left: bool,
    new_val: u64,
    tracked inst: &AuthFrag::Instance<nat, Block>,
    tracked interp1: AuthFrag::auth<nat, Block>,
    tracked lt1: LinearTree,
    tree1_state: TreeSM::State,
) -> (tracked ret: (Tracked<AuthFrag::auth<nat, Block>>, Tracked<LinearTree>, Ghost<TreeSM::State>))
    requires
        DiskSM::State::update_child(state1, state2, is_left, new_val),
        state_interp_fn(*inst, interp1, state1),
        tree_relation(*inst, lt1, tree1_state),
    ensures
        state_interp_fn(*inst, ret.0@, state2),
        TreeSM::State::update_child(tree1_state, ret.2@, is_left, new_val),
        tree_relation(*inst, ret.1@, ret.2@),
{
    reveal_with_fuel(tree_relation_rec, 3);
    let tracked mut interp = interp1;
    let tree1 = tree1_state.tree;

    match lt1 {
        LinearTree::Node(lt_root_fragment, lt_left, lt_right) => {
            inst.values_agree(0, &interp, &lt_root_fragment);

            if is_left {
                let left_address = lt_root_fragment.value()->Node_0;
                assert(tree_relation_rec(*inst, *lt_left, *tree1->Node_0, left_address));

                match *lt_left {
                    LinearTree::Leaf(lt_leaf_fragment) => {
                        inst.values_agree(left_address, &interp, &lt_leaf_fragment);
                        let tracked lt_leaf_fragment_new = inst.update_key(
                            lt_leaf_fragment.key(),
                            Block::Leaf(new_val),
                            &mut interp,
                            lt_leaf_fragment,
                        );
                        let tracked lt2 = LinearTree::Node(
                            lt_root_fragment,
                            Box::new(LinearTree::Leaf(lt_leaf_fragment_new)),
                            lt_right,
                        );
                        let tracked interp2 = interp;
                        let tree2 = TreeSM::State {
                            tree: Tree::Node(Box::new(Tree::Leaf(new_val)), tree1->Node_1),
                        };
                        assert(state_interp_fn(*inst, interp2, state2));
                        assert(TreeSM::State::update_child(tree1_state, tree2, is_left, new_val));
                        assert(tree_relation_rec(
                            *inst,
                            LinearTree::Leaf(lt_leaf_fragment_new),
                            Tree::Leaf(new_val),
                            left_address,
                        ));
                        assert(tree_relation_rec(*inst, lt2, tree2.tree, 0));
                        assert(tree_relation(*inst, lt2, tree2));
                        (Tracked(interp2), Tracked(lt2), Ghost(tree2))
                    },
                    LinearTree::Node(lt_node_fragment, _, _) => {
                        inst.values_agree(left_address, &interp, &lt_node_fragment);
                        proof_from_false()
                    },
                }
            } else {
                let right_address = lt_root_fragment.value()->Node_1;
                assert(tree_relation_rec(*inst, *lt_right, *tree1->Node_1, right_address));

                match *lt_right {
                    LinearTree::Leaf(lt_leaf_fragment) => {
                        inst.values_agree(right_address, &interp, &lt_leaf_fragment);
                        let tracked lt_leaf_fragment_new = inst.update_key(
                            lt_leaf_fragment.key(),
                            Block::Leaf(new_val),
                            &mut interp,
                            lt_leaf_fragment,
                        );
                        let tracked lt2 = LinearTree::Node(
                            lt_root_fragment,
                            lt_left,
                            Box::new(LinearTree::Leaf(lt_leaf_fragment_new)),
                        );
                        let tracked interp2 = interp;
                        let tree2 = TreeSM::State {
                            tree: Tree::Node(tree1->Node_0, Box::new(Tree::Leaf(new_val))),
                        };
                        assert(state_interp_fn(*inst, interp2, state2));
                        assert(TreeSM::State::update_child(tree1_state, tree2, is_left, new_val));
                        assert(tree_relation_rec(
                            *inst,
                            LinearTree::Leaf(lt_leaf_fragment_new),
                            Tree::Leaf(new_val),
                            right_address,
                        ));
                        assert(tree_relation_rec(*inst, lt2, tree2.tree, 0));
                        assert(tree_relation(*inst, lt2, tree2));
                        (Tracked(interp2), Tracked(lt2), Ghost(tree2))
                    },
                    LinearTree::Node(lt_node_fragment, _, _) => {
                        inst.values_agree(right_address, &interp, &lt_node_fragment);
                        proof_from_false()
                    },
                }
            }
        },
        LinearTree::Leaf(lt_root_fragment) => {
            inst.values_agree(0, &interp, &lt_root_fragment);
            proof_from_false()
        },
    }
}

fn main() {
    proof {
        let disk = Map::empty().insert(0nat, Block::Node(1nat, 2nat)).insert(
            1nat,
            Block::Leaf(10u64),
        ).insert(2nat, Block::Leaf(20u64));
        let tracked (Tracked(inst), Tracked(interp), Tracked(mut fragments)) =
            AuthFrag::Instance::initialize(disk);
        let tracked lt_root_fragment = fragments.remove(0nat);
        let tracked lt_left = fragments.remove(1nat);
        let tracked lt_right = fragments.remove(2nat);
        let tracked lt1 = LinearTree::Node(
            lt_root_fragment,
            Box::new(LinearTree::Leaf(lt_left)),
            Box::new(LinearTree::Leaf(lt_right)),
        );
        let tree1_state = TreeSM::State {
            tree: Tree::Node(Box::new(Tree::Leaf(10u64)), Box::new(Tree::Leaf(20u64))),
        };
        let state1 = DiskSM::State { disk };
        let state2 = DiskSM::State { disk: disk.insert(1nat, Block::Leaf(11u64)) };
        reveal_with_fuel(tree_relation_rec, 3);
        let tracked (Tracked(interp2), Tracked(lt2), Ghost(tree2)) = take_step(
            state1,
            state2,
            true,
            11u64,
            &inst,
            interp,
            lt1,
            tree1_state,
        );
        let state3 = DiskSM::State { disk: state2.disk.insert(2nat, Block::Leaf(21u64)) };
        let tracked (Tracked(interp3), Tracked(lt3), Ghost(tree3)) = take_step(
            state2,
            state3,
            false,
            21u64,
            &inst,
            interp2,
            lt2,
            tree2,
        );
        assert(tree3.tree == Tree::Node(Box::new(Tree::Leaf(11u64)), Box::new(Tree::Leaf(21u64))));
        assert(state_interp_fn(inst, interp3, state3));
        assert(tree_relation(inst, lt3, tree3));
    }
}

} // verus!
