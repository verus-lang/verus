use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Index;

struct Scope<K, V> {
    undo_map: HashMap<K, Option<V>>,
    allow_shadowing: bool,
}

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
        let scope = Scope { undo_map: HashMap::new(), allow_shadowing };
        self.scopes.push(scope);
    }

    pub fn pop_scope(&mut self) {
        let scope = self.scopes.pop().expect("internal error: popped empty stack from ScopeMap");
        for (key, value) in scope.undo_map {
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

    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }

    pub fn insert(&mut self, key: K, value: V) -> Result<(), ()> {
        if self.cannot_shadow.contains(&key) {
            return Err(());
        }
        let scope = self
            .scopes
            .last_mut()
            .expect("internal error: must push at least one scope in ScopeMap");
        let prev = self.map.insert(key.clone(), value);
        if !scope.allow_shadowing {
            self.cannot_shadow.insert(key.clone());
        }
        let undo_prev = scope.undo_map.insert(key, prev);
        if undo_prev.is_none() { Ok(()) } else { Err(()) }
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
