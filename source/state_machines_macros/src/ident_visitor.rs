use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{Error, ExprMacro, Ident, ImplItemMethod};

/// Error if any identifiers conflict with reserved IDs used by macro expanion.
///
/// Since macros might introduce arbitrary identifiers or otherwise interfere with
/// our checks or transformations, we also disallow macros entirely.
/// (TODO This makes the whole transformation process feel very brittle / non-robust.
/// Is there something better we can do?)

pub fn validate_idents_impl_item_method(iim: &ImplItemMethod) -> syn::parse::Result<()> {
    let mut idv = IdentVisitor::new();
    idv.visit_impl_item_method(iim);

    if idv.errors.len() > 0 {
        let mut error = idv.errors[0].clone();
        for i in 1..idv.errors.len() {
            error.combine(idv.errors[i].clone());
        }
        return Err(error);
    }

    Ok(())
}

struct IdentVisitor {
    pub errors: Vec<Error>,
}

impl IdentVisitor {
    pub fn new() -> IdentVisitor {
        IdentVisitor { errors: Vec::new() }
    }
}

impl<'ast> Visit<'ast> for IdentVisitor {
    fn visit_ident(&mut self, node: &'ast Ident) {
        if node.to_string() == "post" {
            self.errors.push(Error::new(
                node.span(),
                format!("'post' is a reserved identifier in state machine definitions"),
            ));
        }
    }

    fn visit_expr_macro(&mut self, node: &'ast ExprMacro) {
        self.errors
            .push(Error::new(node.span(), format!("macro not allowed in transition expression")));
    }
}
