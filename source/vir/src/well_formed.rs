use crate::ast::{Expr, ExprX, Function, Ident, Krate, Mode, VirErr};
use crate::ast_util::err_string;
use crate::ast_visitor::map_expr_visitor;
use std::collections::HashMap;

struct Ctxt {
    pub(crate) funs: HashMap<Ident, Function>,
}

fn check_function(ctxt: &Ctxt, function: &Function) -> Result<(), VirErr> {
    // Check that public, non-abstract spec function bodies don't refer to private items
    if function.x.is_abstract || function.x.visibility.is_private || function.x.mode != Mode::Spec {
        return Ok(());
    }
    if let Some(body) = &function.x.body {
        map_expr_visitor(body, &mut |expr: &Expr| {
            match &expr.x {
                ExprX::Call(x, _, _) => {
                    let callee = &ctxt.funs[x];
                    if callee.x.visibility.is_private {
                        return err_string(
                            &expr.span,
                            format!(
                                "public spec function cannot refer to private items, unless function is marked #[verifier(pub_abstract)]"
                            ),
                        );
                    }
                }
                _ => {}
            }
            Ok(expr.clone())
        })?;
    }
    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<(), VirErr> {
    let mut funs: HashMap<Ident, Function> = HashMap::new();
    for function in krate.functions.iter() {
        funs.insert(function.x.name.clone(), function.clone());
    }
    let ctxt = Ctxt { funs };
    for function in krate.functions.iter() {
        check_function(&ctxt, function)?;
    }
    Ok(())
}
