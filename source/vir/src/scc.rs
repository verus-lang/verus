/*
 * Create a graph and then compute the strongly-connected components
 * of that graph.
 * Based on pseudocode from
 * https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
 */
use std::cmp::min;
use std::collections::{BTreeSet, HashMap, HashSet};

type SccId = usize;
type NodeIndex = usize;

pub struct Graph<T: std::cmp::Eq + std::hash::Hash + Clone> {
    // Map T to index in nodes
    h: HashMap<T, NodeIndex>,
    nodes: Vec<Node<T>>,

    has_run: bool,
    stack: Vec<NodeIndex>,
    stack_len: usize,
    index: usize,

    sccs: Vec<SCC>,
    // Map T to SCC.id
    mapping: HashMap<T, SccId>,
}

struct SCC /* <T> */ {
    id: SccId,
    nodes: Vec<NodeIndex>,
}

struct Node<T: std::cmp::Eq + std::hash::Hash + Clone> {
    t: T,
    edges: Vec<NodeIndex>,
    // index in Graph.nodes or usize::MAX
    index: NodeIndex,
    lowlink: NodeIndex,
    on_stack: bool,
}

impl SCC {
    pub fn new(id: SccId) -> SCC {
        SCC { id, nodes: Vec::new() }
    }

    fn size(&self) -> usize {
        self.nodes.len()
    }

    fn rep(&self) -> NodeIndex {
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

    fn get_or_add(&mut self, value: T) -> NodeIndex {
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

    fn strongconnect(&mut self, v: NodeIndex) {
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

    fn sort_sccs_node(&self, visited: &mut Vec<bool>, sorted: &mut Vec<T>, s: SccId) {
        if visited[s] {
            return;
        }
        visited[s] = true;
        for v in self.sccs[s].nodes.iter() {
            for w in self.nodes[*v].edges.iter() {
                self.sort_sccs_node(visited, sorted, self.mapping[&self.nodes[*w].t]);
            }
        }
        sorted.push(self.nodes[self.sccs[s].rep()].t.clone());
    }

    // Return vector of representatives, one for each SCC, sorted so that later
    // elements point only to earlier elements.
    pub fn sort_sccs(&self) -> Vec<T> {
        assert!(self.has_run);
        let mut visited: Vec<bool> = self.sccs.iter().map(|_| false).collect();
        let mut sorted: Vec<T> = Vec::new();
        for s in 0..self.sccs.len() {
            self.sort_sccs_node(&mut visited, &mut sorted, s);
        }
        sorted
    }

    pub fn node_has_direct_edge_to_itself(&self, t: &T) -> bool {
        assert!(self.has_run);
        assert!(self.h.contains_key(&t));
        let v: NodeIndex = self.h[t];
        for edge in self.nodes[v].edges.iter() {
            if *edge == v {
                return true;
            }
        }
        false
    }

    pub fn get_scc_size(&self, t: &T) -> usize {
        assert!(self.has_run);
        match self.mapping.get(&t) {
            Some(i) => self.sccs[*i].size(),
            None => 1,
        }
    }

    /// Returns true if the given element is part of a cycle (including self-loops)
    pub fn node_is_in_cycle(&self, t: &T) -> bool {
        self.node_has_direct_edge_to_itself(t) || self.get_scc_size(t) > 1
    }

    pub fn get_scc_rep(&self, t: &T) -> T {
        assert!(self.has_run);
        assert!(self.mapping.contains_key(&t));
        let id = self.mapping.get(&t).expect("key was present in the line above");
        self.nodes[self.sccs[*id].rep()].t.clone()
    }

    pub fn in_same_scc(&self, t1: &T, t2: &T) -> bool {
        t1 == t2 || self.get_scc_rep(t1) == self.get_scc_rep(t2)
    }

    pub fn get_scc_nodes(&self, t: &T) -> Vec<T> {
        assert!(self.has_run);
        assert!(self.mapping.contains_key(&t));
        let id = self.mapping[t];
        let scc = &self.sccs[id];
        scc.nodes.iter().map(|i| self.nodes[*i].t.clone()).collect()
    }

    pub fn shortest_cycle_back_to_self(&self, t: &T) -> Vec<T> {
        assert!(self.has_run);
        assert!(self.h.contains_key(&t));
        let root: NodeIndex = *self.h.get(t).expect("key not present");
        let mut paths_at_depth: Vec<Vec<NodeIndex>> = vec![vec![root]];
        let mut reached: HashSet<NodeIndex> = HashSet::new();
        reached.insert(root);
        loop {
            let mut paths_at_next_depth: Vec<Vec<NodeIndex>> = Vec::new();
            assert!(paths_at_depth.len() != 0);
            for p in paths_at_depth.into_iter() {
                for edge in self.nodes[*p.last().expect("path")].edges.iter() {
                    if *edge == root {
                        // reached the root, found cycle
                        return p.into_iter().map(|i| self.nodes[i].t.clone()).collect();
                    }
                    if !reached.contains(edge) {
                        reached.insert(*edge);
                        let mut p_edge = p.clone();
                        p_edge.push(*edge);
                        paths_at_next_depth.push(p_edge);
                    }
                }
            }
            paths_at_depth = paths_at_next_depth;
        }
    }

    pub fn to_dot(
        &self,
        mut w: impl std::io::Write,
        filter_by: impl Fn(&T) -> (/* always */ bool, /* only if reached */ bool),
        node_options: impl Fn(&T) -> String,
    ) {
        fn io_err<V>(o: Result<V, std::io::Error>) {
            o.unwrap_or_else(|err| panic!("i/o failed: {}", err));
        }

        io_err(writeln!(w, "digraph M {{"));
        io_err(writeln!(w, "  rankdir=LR;"));
        io_err(writeln!(w, "  node [shape=\"box\"];"));
        let mut render_nodes = BTreeSet::new();
        for (i, n) in self.nodes.iter().enumerate() {
            if n.edges.len() > 0 {
                if filter_by(&n.t).1 {
                    render_nodes.insert(i);
                }
            }
            for e in n.edges.iter() {
                if filter_by(&n.t).1 && filter_by(&self.nodes[*e].t).0 {
                    render_nodes.insert(*e);
                }
            }
        }
        for (i, n) in self.nodes.iter().enumerate() {
            if render_nodes.contains(&i) {
                io_err(writeln!(w, "  node_{} [{}]", i, node_options(&n.t)));
            }
        }
        io_err(writeln!(w, ""));
        for (i, n) in self.nodes.iter().enumerate().filter(|(i, _)| render_nodes.contains(i)) {
            for e in
                n.edges.iter().filter(|x| render_nodes.contains(x)).collect::<HashSet<_>>().iter()
            {
                io_err(writeln!(w, "  node_{} -> node_{}", i, e));
            }
        }
        io_err(writeln!(w, "}}"));
    }
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone + std::fmt::Debug> std::fmt::Debug for Graph<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Graph:\n")?;
        for node in self.nodes.iter() {
            write!(f, "    {:?}\n", node.t)?;
            for idx in node.edges.iter() {
                let succ_t = &self.nodes[*idx].t;
                write!(f, "     -> {:?}\n", succ_t)?;
            }
        }
        if self.has_run {
            write!(f, "SCCs:\n")?;
            let scc_reps = self.sort_sccs();
            for scc_rep in scc_reps.iter() {
                let nodes = self.get_scc_nodes(scc_rep);
                write!(f, "{{\n")?;
                for node in nodes {
                    write!(f, "    {:?}\n", node)?;
                }
                write!(f, "}}\n")?;
            }
        } else {
            write!(f, "SCC not yet run")?;
        }
        Ok(())
    }
}
