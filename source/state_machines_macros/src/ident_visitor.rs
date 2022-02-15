use syn::visit::Visit;
use syn::{Error, Ident};

pub struct IdentVisitor {
    pub error: syn::parse::Result<()>,
}

impl IdentVisitor {
    pub fn new() -> IdentVisitor {
        IdentVisitor { error: Ok(()) }
    }
}

impl<'ast> Visit<'ast> for IdentVisitor {
    fn visit_ident(&mut self, node: &'ast Ident) {
        if self.error.is_err() {
            return;
        }

        if node.to_string() == "post" {
            self.error = Err(Error::new(
                node.span(),
                format!("'post' is a reserved identifier in state machine definitions"),
            ));
        }
    }
}
