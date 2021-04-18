use crate::ast::{Function, Ident, Krate};
use std::collections::HashMap;

pub struct Ctx {
    pub(crate) functions: HashMap<Ident, Function>,
}

impl Ctx {
    pub fn new(krate: &Krate) -> Self {
        let mut functions: HashMap<Ident, Function> = HashMap::new();
        for function in krate.iter() {
            functions.insert(function.x.name.clone(), function.clone());
        }
        Ctx { functions }
    }
}
