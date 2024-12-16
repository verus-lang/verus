use std::cell::Cell;
use std::ops::{Index, IndexMut};

/// Unification table
///
/// Nodes are labeled by `usize` and grouped into equivalence classes, labeled by `NodeClass`.
/// The table maps `NodeClass` to type `T`
///
/// To access the data for a given label, first get the NodeClass, then use it as an index:
/// 
///     let node = table.get_class(i);
///     let info = &mut table[node];
///
/// Of course, nodes might be invalidated after a merge.

pub struct UnificationTable<T> {
    uf_nodes: Vec<UFNode>,
    data: Vec<T>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeClass(pub usize);

// We implement standard union-find with union-by-rank
// https://en.wikipedia.org/wiki/Disjoint-set_data_structure#Union_by_rank
// The `parent` field is a Cell so that `get_class` can be implemented with `&self`.
struct UFNode {
    parent: Cell<usize>,
    rank: usize,
}

impl<T> UnificationTable<T> {
    pub fn new() -> Self {
        UnificationTable {
            uf_nodes: vec![],
            data: vec![],
        }
    }

    pub fn fresh_node(&mut self, t: T) -> usize {
        self.data.push(t);
        let me = self.uf_nodes.len();
        self.uf_nodes.push(UFNode { parent: Cell::new(me), rank: 0 });
        me
    }

    pub fn get_class(&self, i: usize) -> NodeClass {
        if self.uf_nodes[i].parent.get() == i {
            return NodeClass(i);
        }
        let root = self.get_class(self.uf_nodes[i].parent.get());
        self.uf_nodes[i].parent.set(root.0);
        return root;
    }

    pub fn merge_classes(&mut self, i: NodeClass, j: NodeClass, t: T) {
        let i = i.0;
        let j = j.0;
        assert!(i != j);
        assert!(self.uf_nodes[i].parent.get() == i);
        assert!(self.uf_nodes[j].parent.get() == j);

        let new_node;
        if self.uf_nodes[i].rank > self.uf_nodes[j].rank {
            self.uf_nodes[j].parent.set(i);
            new_node = i;
        } else if self.uf_nodes[i].rank < self.uf_nodes[j].rank {
            self.uf_nodes[i].parent.set(j);
            new_node = j;
        } else {
            self.uf_nodes[j].parent.set(i);
            self.uf_nodes[j].rank += 1;
            new_node = i;
        }

        self.data[new_node] = t;
    }

    pub fn len(&self) -> usize {
        self.uf_nodes.len()
    }

    /// Check if the given index is the root node for its class.
    /// Used for iterating over all classes.
    pub fn is_root_of_class(&self, i: usize) -> Option<NodeClass> {
        if self.uf_nodes[i].parent.get() == i {
            Some(NodeClass(i))
        } else {
            None
        }
    }
}

impl<T> Index<NodeClass> for UnificationTable<T> {
    type Output = T;

    fn index(&self, i: NodeClass) -> &T {
        let i = i.0;
        assert!(self.uf_nodes[i].parent.get() == i);
        &self.data[i]
    }
}

impl<T> IndexMut<NodeClass> for UnificationTable<T> {
    fn index_mut(&mut self, i: NodeClass) -> &mut T {
        let i = i.0;
        assert!(self.uf_nodes[i].parent.get() == i);
        &mut self.data[i]
    }
}

impl NodeClass {
    pub fn as_id(self) -> usize {
        self.0
    }
}
