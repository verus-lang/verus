use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Index;

#[derive(Debug)]
struct Scope<K, V> {
    undo_map: HashMap<K, (Option<V>, usize)>,
    allow_shadowing: bool,
    count: usize,
}

#[derive(Debug)]
pub struct ScopeMap<K, V> {
    map: HashMap<K, V>,
    cannot_shadow: HashSet<K>,
    scopes: Vec<Scope<K, V>>,
}

impl<K: Eq + Hash + Clone, V> ScopeMap<K, V> {
    pub fn new() -> Self {
        ScopeMap { map: HashMap::new(), cannot_shadow: HashSet::new(), scopes: Vec::new() }
    }

    pub fn push_scope(&mut self, allow_shadowing: bool) {
        let scope = Scope { undo_map: HashMap::new(), allow_shadowing, count: 0 };
        self.scopes.push(scope);
    }

    pub fn pop_scope(&mut self) {
        let scope = self.scopes.pop().expect("internal error: popped empty stack from ScopeMap");
        for (key, (value, _)) in scope.undo_map {
            self.map.remove(&key);
            if !scope.allow_shadowing {
                self.cannot_shadow.remove(&key);
            }
            if let Some(value) = value {
                self.map.insert(key, value);
            }
        }
    }

    pub fn num_scopes(&self) -> usize {
        self.scopes.len()
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    // Which scope, and which index within the scope
    pub fn scope_and_index_of_key(&self, key: &K) -> Option<(usize, usize)> {
        for i in (0..self.scopes.len()).rev() {
            if let Some((_, k)) = self.scopes[i].undo_map.get(key) {
                return Some((i, *k));
            }
        }
        None
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }

    pub fn insert_at(&mut self, scope_index: usize, key: K, value: V) -> Result<(), ()> {
        if self.cannot_shadow.contains(&key) {
            return Err(());
        }
        let scope = &mut self.scopes[scope_index];
        let prev = self.map.insert(key.clone(), value);
        if !scope.allow_shadowing {
            self.cannot_shadow.insert(key.clone());
        }
        let undo_prev = scope.undo_map.insert(key, (prev, scope.count));
        scope.count += 1;
        if undo_prev.is_none() { Ok(()) } else { Err(()) }
    }

    pub fn insert(&mut self, key: K, value: V) -> Result<(), ()> {
        if self.scopes.len() == 0 {
            panic!("internal error: must push at least one scope in ScopeMap")
        } else {
            self.insert_at(self.scopes.len() - 1, key, value)
        }
    }

    pub fn replace(&mut self, key: K, value: V) -> Result<(), ()> {
        if self.contains_key(&key) {
            self.map.insert(key, value).expect("replace");
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn map(&self) -> &HashMap<K, V> {
        &self.map
    }
}

impl<K: Eq + Hash + Clone, V> Index<&K> for ScopeMap<K, V> {
    type Output = V;
    fn index(&self, key: &K) -> &V {
        &self.map[key]
    }
}
