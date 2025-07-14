use crate::lifetime_ast::*;
use std::collections::{HashMap};
use vir::ast::{Path};

pub(crate) struct State {
    rename_count: usize,
    typ_param_to_name: HashMap<(String, Option<u32>), Id>,
    trait_to_name: HashMap<Path, Id>,
    datatype_to_name: HashMap<Path, Id>,
    unmangle_names: HashMap<String, String>,
    pub(crate) trait_decls: Vec<TraitDecl>,
    pub(crate) datatype_decls: Vec<DatatypeDecl>,
    pub(crate) trait_impls: Vec<TraitImpl>,
}

impl State {
    pub(crate) fn new() -> State {
        State {
            rename_count: 0,
            typ_param_to_name: HashMap::new(),
            trait_to_name: HashMap::new(),
            datatype_to_name: HashMap::new(),
            unmangle_names: HashMap::new(),
            trait_decls: Vec::new(),
            datatype_decls: Vec::new(),
            trait_impls: Vec::new(),
        }
    }

    fn id_with_unmangle<Key: Clone + Eq + std::hash::Hash>(
        rename_count: &mut usize,
        key_to_name: &mut HashMap<Key, Id>,
        unmangle_names: Option<&mut HashMap<String, String>>,
        kind: IdKind,
        key: &Key,
        mk_raw_id: impl Fn() -> String,
    ) -> Id {
        let name = key_to_name.get(key);
        if let Some(name) = name {
            return name.clone();
        }
        *rename_count += 1;
        let raw_id = mk_raw_id();
        let name = Id::new(kind, *rename_count, raw_id.clone());
        key_to_name.insert(key.clone(), name.clone());
        if let Some(unmangle_names) = unmangle_names {
            unmangle_names.insert(name.to_string(), raw_id);
        }
        name
    }

    fn id<Key: Clone + Eq + std::hash::Hash>(
        rename_count: &mut usize,
        key_to_name: &mut HashMap<Key, Id>,
        kind: IdKind,
        key: &Key,
        mk_raw_id: impl Fn() -> String,
    ) -> Id {
        Self::id_with_unmangle(rename_count, key_to_name, None, kind, key, mk_raw_id)
    }

    pub(crate) fn typ_param<S: Into<String>>(
        &mut self,
        raw_id: S,
        maybe_impl_index: Option<u32>,
    ) -> Id {
        let raw_id = raw_id.into();
        let (is_impl, impl_index) = match (raw_id.starts_with("impl "), maybe_impl_index) {
            (false, _) => (false, None),
            (true, None) => panic!("unexpected impl type"),
            (true, Some(i)) => (true, Some(i)),
        };
        let f = || if is_impl { "impl".to_string() } else { raw_id.clone() };
        let key = (raw_id.clone(), impl_index);
        Self::id(&mut self.rename_count, &mut self.typ_param_to_name, IdKind::TypParam, &key, f)
    }
    
    pub(crate) fn trait_name<'tcx>(&mut self, path: &Path) -> Id {
        let f = || path.segments.last().expect("path").to_string();
        Self::id(&mut self.rename_count, &mut self.trait_to_name, IdKind::Trait, path, f)
    }

    pub(crate) fn datatype_name<'tcx>(&mut self, path: &Path) -> Id {
        let f = || path.segments.last().expect("path").to_string();
        Self::id_with_unmangle(
            &mut self.rename_count,
            &mut self.datatype_to_name,
            Some(&mut self.unmangle_names),
            IdKind::Datatype,
            path,
            f,
        )
    }

    pub(crate) fn unmangle_names<S: Into<String>>(&self, s: S) -> String {
        let mut s = s.into();
        for (name, raw_id) in &self.unmangle_names {
            if s.contains(name) {
                s = s.replace(name, raw_id);
            }
        }
        s
    }
}
