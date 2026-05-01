use std::collections::HashMap;

pub struct Graph<T> {
    elems: Vec<T>,
    elem_to_idx: HashMap<T, usize>,
    edges: Vec<Vec<usize>>,
    roots: Vec<usize>,
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone> Graph<T> {
    pub fn new() -> Self {
        Graph { elems: vec![], elem_to_idx: HashMap::new(), edges: vec![], roots: vec![] }
    }

    pub fn add_node(&mut self, a: T) -> usize {
        *self.elem_to_idx.entry(a.clone()).or_insert_with(|| {
            let idx = self.elems.len();
            self.elems.push(a);
            self.edges.push(vec![]);
            idx
        })
    }

    pub fn add_edge(&mut self, a: T, b: T) {
        let ai = self.add_node(a);
        let bi = self.add_node(b);
        self.edges[ai].push(bi);
    }

    pub fn add_root(&mut self, a: T) {
        let ai = self.add_node(a);
        self.roots.push(ai);
    }

    pub fn into_reachable_set(self) -> HashMap<T, bool> {
        let mut reached = vec![false; self.elems.len()];
        let mut worklist = vec![];
        for r in self.roots.iter() {
            if !reached[*r] {
                reached[*r] = true;
                worklist.push(*r);
            }
        }
        let mut q_idx = 0;
        while q_idx < worklist.len() {
            let v = worklist[q_idx];
            for w in self.edges[v].iter() {
                if !reached[*w] {
                    reached[*w] = true;
                    worklist.push(*w);
                }
            }
            q_idx += 1;
        }
        let mut reachable = HashMap::<T, bool>::new();
        for (i, elem) in self.elems.iter().enumerate() {
            reachable.insert(elem.clone(), reached[i]);
        }
        reachable
    }
}
