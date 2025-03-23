use crate::ast::{
    Fun, Function, FunctionKind, Krate, MaskSpec, Mode, Path, Trait, UnwindSpec, VirErr,
};
use crate::ast_util::fun_as_friendly_rust_name;
use crate::messages::error;
use std::collections::HashMap;

pub fn check_safe_api(krate: &Krate) -> Result<(), VirErr> {
    let mut trait_map = HashMap::<Path, Trait>::new();
    for t in krate.traits.iter() {
        trait_map.insert(t.x.name.clone(), t.clone());
    }
    let mut function_map = HashMap::<Fun, Function>::new();
    for f in krate.functions.iter() {
        function_map.insert(f.x.name.clone(), f.clone());
    }

    for function in krate.functions.iter() {
        if function.x.mode == Mode::Exec
            && function.x.visibility.is_public()
            && !function.x.attrs.is_unsafe
            && matches!(&function.x.kind, FunctionKind::Static)
            && function.x.require.len() > 0
        {
            return Err(error(
                &function.span,
                &format!(
                    "Safe API violation: 'requires' clause is nontrivial for function `{:}`. Unverified, safe client code may be able to call this function without satisfying the precondition.",
                    fun_as_friendly_rust_name(&function.x.name),
                ),
            ));
        }

        if let FunctionKind::TraitMethodImpl { trait_path, method, .. } = &function.x.kind {
            if function.x.mode == Mode::Exec && !function.x.attrs.is_unsafe {
                let trait_fn = function_map.get(method).unwrap();
                let t = trait_map.get(trait_path).unwrap();
                if t.x.visibility.is_public() && trait_fn.x.require.len() > 0 {
                    return Err(error(
                        &function.span,
                        &format!(
                            "Safe API violation: 'requires' clause is nontrivial for function `{:}`. Unverified, safe client code may be able to call this function without satisfying the precondition.",
                            fun_as_friendly_rust_name(&function.x.name),
                        ),
                    ));
                }
            }
        }

        if (function.x.mode == Mode::Exec || function.x.mode == Mode::Proof)
            && is_decl_in_safe_public_trait(&trait_map, function)
        {
            if function.x.ensure.len() > 0 {
                return Err(error(
                    &function.span,
                    &format!(
                        "Safe API violation: 'ensures' clause is nontrivial for trait function `{:}`. Unverified, safe client code may be able to implement this trait without satisfying the postcondition.",
                        fun_as_friendly_rust_name(&function.x.name),
                    ),
                ));
            }
            if function.x.mode == Mode::Exec
                && !matches!(function.x.unwind_spec_or_default(), UnwindSpec::MayUnwind)
            {
                return Err(error(
                    &function.span,
                    &format!(
                        "Safe API violation: 'unwind' clause is nontrivial for trait function `{:}`. Unverified, safe client code may be able to implement this trait without meeting these unwinding requirements.",
                        fun_as_friendly_rust_name(&function.x.name),
                    ),
                ));
            }
            if mask_spec_restricts_implementation(&function.x.mask_spec_or_default(&function.span))
            {
                return Err(error(
                    &function.span,
                    &format!(
                        "Safe API violation: 'invariant' clause is nontrivial for trait function `{:}`. Unverified, safe client code may be able to implement this trait without obeying invariant-reentrancy requirements.",
                        fun_as_friendly_rust_name(&function.x.name),
                    ),
                ));
            }
        }
    }

    Ok(())
}

fn is_decl_in_safe_public_trait(trait_map: &HashMap<Path, Trait>, function: &Function) -> bool {
    if let FunctionKind::TraitMethodDecl { trait_path, has_default: _ } = &function.x.kind {
        let t = trait_map.get(trait_path).unwrap();
        t.x.visibility.is_public() && !t.x.is_unsafe
    } else {
        false
    }
}

fn mask_spec_restricts_implementation(mask_spec: &MaskSpec) -> bool {
    match mask_spec {
        MaskSpec::InvariantOpens(_span, _es) => true,
        MaskSpec::InvariantOpensExcept(_span, es) => es.len() > 0,
        MaskSpec::InvariantOpensSet(_e) => true,
    }
}
