use std::collections::HashMap;

pub struct TopologicalSort<T> {
    values: Vec<T>,
    nodes: HashMap<T, usize>,
    edges_rev: Vec<Vec<usize>>,
}

impl<T> TopologicalSort<T>
where
    T: std::cmp::Eq + std::hash::Hash + Clone,
{
    pub fn new() -> Self {
        TopologicalSort { values: vec![], nodes: HashMap::new(), edges_rev: vec![] }
    }

    pub fn add_node(&mut self, v: T) {
        self.values.push(v.clone());
        let res = self.nodes.insert(v, self.nodes.len());
        assert!(res.is_none());
        self.edges_rev.push(vec![]);
    }

    pub fn add_edge(&mut self, a: &T, b: &T) {
        let i = *self.nodes.get(a).unwrap();
        let j = *self.nodes.get(b).unwrap();
        self.edges_rev[j].push(i);
    }

    pub fn compute_topological_sort(&mut self) -> Option<Vec<T>> {
        let mut res: Vec<T> = vec![];
        let mut visited: Vec<bool> = vec![false; self.values.len()];
        let mut in_stack: Vec<bool> = vec![false; self.values.len()];

        for i in 0..self.values.len() {
            if !self.visit(&mut res, &mut visited, &mut in_stack, i) {
                return None;
            }
        }

        Some(res)
    }

    fn visit(
        &mut self,
        res: &mut Vec<T>,
        visited: &mut Vec<bool>,
        in_stack: &mut Vec<bool>,
        i: usize,
    ) -> bool {
        if in_stack[i] {
            return false;
        }

        if visited[i] {
            return true;
        }

        visited[i] = true;
        in_stack[i] = true;

        for edge_idx in 0..self.edges_rev[i].len() {
            let j = self.edges_rev[i][edge_idx];
            if !self.visit(res, visited, in_stack, j) {
                return false;
            }
        }

        res.push(self.values[i].clone());
        in_stack[i] = false;

        return true;
    }
}
