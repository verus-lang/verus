use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use crate::ast::{Ident};
//use z3::ast::Dynamic;
//use z3::{FuncDecl, Sort};


#[derive(Debug)]
pub(crate) struct Model<'a> {
    pub(crate) z3: z3::Model<'a>,
    pub(crate) snapshots: HashMap<Ident, HashMap<Ident, u32>>,
}


impl<'a> Model<'a> {
    pub fn new(model: z3::Model<'a>) -> Model<'a> {
        Model {
            z3: model,
            snapshots: HashMap::new(),
        }
    }
}

