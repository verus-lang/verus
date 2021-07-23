/*
 * Create a graph and then compute the strongly-connected components
 * of that graph.
 * Derived from code written by Travis Hance.
 */
use std::cmp::min;
use std::collections::HashMap;

pub struct Graph<T> {
    h: HashMap<T, usize>,
    nodes: Vec<Node<T>>,

    has_run: bool,
    stack: Vec<usize>,
    stack_len: usize,
    index: usize,

    sccs: Vec<SCC>,
    mapping: HashMap<T, usize>,
}

struct SCC /* <T> */ {
    id: usize,
    nodes: Vec<usize>,
}

struct Node<T> {
    t: T,
    edges: Vec<usize>,
    index: usize,
    lowlink: usize,
    on_stack: bool,
}

impl SCC {
    pub fn new(id: usize) -> SCC {
        SCC { id, nodes: Vec::new() }
    }

    fn size(&self) -> usize {
        self.nodes.len()
    }

    fn rep(&self) -> usize {
        self.nodes[0]
    }
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone> Graph<T> {
    pub fn new() -> Graph<T> {
        Graph {
            h: HashMap::new(),
            nodes: Vec::new(),
            has_run: false,
            stack: Vec::new(),
            stack_len: 0,
            index: 0,
            sccs: Vec::new(),
            mapping: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, value: T) {
        if !self.h.contains_key(&value) {
            self.h.insert(value.clone(), self.nodes.len());
            self.nodes.push(Node {
                t: value,
                edges: Vec::new(),
                index: usize::MAX,
                lowlink: usize::MAX,
                on_stack: false,
            });
        }
    }

    fn get_or_add(&mut self, value: T) -> usize {
        match self.h.get(&value) {
            Some(v) => *v,
            None => {
                self.add_node(value.clone());
                *self.h.get(&value).expect("Just added this node, so get should always succeed")
            }
        }
    }

    pub fn add_edge(&mut self, src: T, dst: T) {
        let v = self.get_or_add(src);
        let w = self.get_or_add(dst);
        self.nodes[v].edges.push(w);
    }

    #[allow(dead_code)]
    pub fn add_directed_edge_if_nodes_exist(&mut self, src: T, dst: T) {
        let v = self.h.get(&src);
        if let Some(v) = v {
            let w = self.h.get(&dst);
            if let Some(w) = w {
                self.nodes[*v].edges.push(*w);
            }
        }
    }

    fn strongconnect(&mut self, v: usize) {
        self.nodes[v].index = self.index;
        self.nodes[v].lowlink = self.index;
        self.index += 1;
        self.stack[self.stack_len] = v;
        self.stack_len += 1;

        self.nodes[v].on_stack = true;

        for i in 0..self.nodes[v].edges.len() {
            let w = self.nodes[v].edges[i];
            if self.nodes[w].index == usize::MAX {
                self.strongconnect(w);
                self.nodes[v].lowlink = min(self.nodes[v].lowlink, self.nodes[w].lowlink);
            } else if self.nodes[w].on_stack {
                self.nodes[v].lowlink = min(self.nodes[v].lowlink, self.nodes[w].index);
            }
        }

        if self.nodes[v].lowlink == self.nodes[v].index {
            let mut component = SCC::new(self.sccs.len());
            loop {
                let w = self.stack[self.stack_len - 1];
                self.stack_len -= 1;
                self.nodes[w].on_stack = false;
                component.nodes.push(w);
                self.mapping.insert(self.nodes[w].t.clone(), component.id);
                if w == v {
                    break;
                }
            }
            self.sccs.push(component);
        }
    }

    pub fn compute_sccs(&mut self) {
        assert!(!self.has_run);
        self.has_run = true;

        self.stack.resize(self.nodes.len(), 0);

        for i in 0..self.nodes.len() {
            if self.nodes[i].index == usize::MAX {
                self.strongconnect(i);
            }
        }
    }

    pub fn get_scc_size(&self, t: &T) -> usize {
        assert!(self.has_run);
        match self.mapping.get(&t) {
            Some(i) => self.sccs[*i].size(),
            None => 1,
        }
    }

    pub fn get_scc_rep(&self, t: &T) -> T {
        assert!(self.has_run);
        assert!(self.mapping.contains_key(&t));
        let id = self.mapping.get(&t).expect("key was present in the line above");
        self.nodes[self.sccs[*id].rep()].t.clone()
    }
}
