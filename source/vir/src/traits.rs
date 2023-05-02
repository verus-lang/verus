use crate::ast::{Fun, Function, FunctionKind, GenericBoundX, Krate, Path, VirErr};
use crate::ast_util::error;
use crate::def::Spanned;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// We currently do not support trait bounds for traits from other crates
// and we consider methods for traits from other crates to be static.
pub fn demote_foreign_traits(krate: &Krate) -> Result<Krate, VirErr> {
    let traits: HashSet<Path> = krate.traits.iter().map(|t| t.x.name.clone()).collect();
    let func_map: HashMap<Fun, Function> =
        krate.functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();

    let mut kratex = (**krate).clone();
    for function in &mut kratex.functions {
        for (_, bounds) in function.x.typ_bounds.iter() {
            let GenericBoundX::Traits(traits) = &**bounds;
            for trait_path in traits {
                let our_trait = traits.contains(trait_path);
                if !our_trait {
                    return error(
                        &function.span,
                        format!(
                            "cannot use trait {} from another crate as a bound",
                            crate::ast_util::path_as_rust_name(trait_path)
                        ),
                    );
                }
            }
        }

        if let FunctionKind::TraitMethodImpl { method, trait_path, .. } = &function.x.kind {
            let our_trait = traits.contains(trait_path);
            let mut functionx = function.x.clone();
            if our_trait {
                let decl = &func_map[method];
                let mut retx = functionx.ret.x.clone();
                retx.name = decl.x.ret.x.name.clone();
                functionx.ret = Spanned::new(functionx.ret.span.clone(), retx);
            } else {
                functionx.kind = FunctionKind::Static;
            }
            *function = Spanned::new(function.span.clone(), functionx);
        }
    }

    Ok(Arc::new(kratex))
}
