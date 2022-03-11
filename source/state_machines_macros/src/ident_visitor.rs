use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{Error, ExprMacro, Ident, ImplItemMethod};

/// Error if any identifiers conflict with reserved IDs used by macro expanion.
///
/// This validation should be applied to:
///  * the entire body of any transition definition
///  * any field name
///
/// Since macros might introduce arbitrary identifiers or otherwise interfere with
/// our checks or transformations, we also disallow macros entirely.
/// (See the more detailed explanation in `field_access_visitor.rs`.)

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
        match validate_ident(node) {
            Err(err) => self.errors.push(err),
            Ok(()) => {}
        }
    }

    fn visit_expr_macro(&mut self, node: &'ast ExprMacro) {
        self.errors
            .push(Error::new(node.span(), format!("macro not allowed in transition expression")));
    }
}

/// Validate a single identifier.
pub fn validate_ident(ident: &Ident) -> Result<(), Error> {
    for kw in vec!["post", "instance", "tmp_tuple", "tmp_e"] {
        if ident.to_string() == kw {
            return Err(Error::new(
                ident.span(),
                format!("'{kw:}' is a reserved identifier in state machine definitions"),
            ));
        }
    }

    for prefix in vec!["token_", "original_field_"] {
        if ident.to_string().starts_with(prefix) {
            return Err(Error::new(
                ident.span(),
                format!(
                    "identifiers starting with '{prefix:}' are reserved identifiers in state machine definitions"
                ),
            ));
        }
    }

    Ok(())
}
