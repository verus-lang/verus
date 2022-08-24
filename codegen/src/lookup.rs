use syn_codegen::{Definitions, Node};

pub fn node<'a>(defs: &'a Definitions, name: &str) -> &'a Node {
    for node in &defs.types {
        if node.ident == name {
            return node;
        }
    }
    panic!("not found: {}", name)
}
