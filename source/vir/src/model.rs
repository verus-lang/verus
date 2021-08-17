use crate::ast::Ident;
use air::model::Model as AModel;
use std::collections::HashMap;

#[derive(Debug)]
pub struct Model<'a> {
    air_model: AModel<'a>,
    line_snapshots: HashMap<usize, HashMap<Ident, String>>,
}

impl<'a> Model<'a> {
    pub fn new(air_model: AModel<'a>) -> Model<'a> {
        Model { air_model, line_snapshots: HashMap::new() }
    }
}
