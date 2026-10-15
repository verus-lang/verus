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

fn main() {
}

} // verus!
