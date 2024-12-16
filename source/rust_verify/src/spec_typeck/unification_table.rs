use std::cell::Cell;
use std::ops::{Index, IndexMut};

struct UFNode {
    parent: Cell<usize>,
    rank: usize,
}

pub struct UnificationTable<T> {
    uf_nodes: Vec<UFNode>,
    data: Vec<T>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeClass(pub usize);

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

    pub fn get_node(&self, i: usize) -> NodeClass {
        if self.uf_nodes[i].parent.get() == i {
            return NodeClass(i);
        }
        let root = self.get_node(self.uf_nodes[i].parent.get());
        self.uf_nodes[i].parent.set(root.0);
        return root;
    }

    pub fn merge_nodes(&mut self, i: NodeClass, j: NodeClass, t: T) {
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
