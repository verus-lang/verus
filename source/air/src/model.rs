use std::collections::{HashMap};
//use std::collections::{HashMap, HashSet};
//use std::rc::Rc;
use crate::ast::{Ident};
//use z3::ast::Dynamic;
//use z3::{FuncDecl, Sort};

pub(crate) type SnapShot = HashMap<Ident, u32>;
pub(crate) type SnapShots = HashMap<Ident, SnapShot>;

#[derive(Debug)]
pub(crate) struct Model<'a> {
    z3: z3::Model<'a>,
    snapshots: SnapShots,
}


impl<'a> Model<'a> {
    pub fn new(model: z3::Model<'a>) -> Model<'a> {
        Model {
            z3: model,
            snapshots: HashMap::new(),
        }
    }

    pub fn save_snapshots(&self, snapshots: SnapShots) {
        self.snapshots = snapshots.clone();
    }
}

