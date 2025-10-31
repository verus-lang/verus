use quote::ToTokens;
use syn::spanned::Spanned;
use syn::{
    Attribute, Block, ExprForLoop, ExprLoop, ExprWhile, ImplItemFn, ItemFn, Signature, TraitItemFn,
};

fn is_inside_impl_by_span(span: proc_macro2::Span, target_sig: &Signature) -> Option<bool> {
    // Parse the entire source file and check if a function beginning at this span
    // resides inside an impl block.
    let path = span.file();
    let Ok(content) = std::fs::read_to_string(path) else {
        return None;
    };
    let Ok(ast) = syn::parse_file(&content) else {
        return None;
    };
    // Build a normalized token string for the target signature to match against the file AST.
    let target_sig_str = target_sig.to_token_stream().to_string();
    for item in &ast.items {
        if let syn::Item::Impl(imp) = item {
            for impl_item in &imp.items {
                if let syn::ImplItem::Fn(m) = impl_item {
                    let sig_str = m.sig.to_token_stream().to_string();
                    if sig_str == target_sig_str {
                        return Some(true);
                    }
                }
            }
        }
        if let syn::Item::Fn(f) = item {
            let sig_str = f.sig.to_token_stream().to_string();
            if sig_str == target_sig_str {
                return Some(false);
            }
        }
    }
    None
}

pub trait AnyAttrBlock {
    #[allow(dead_code)]
    fn attrs_mut(&mut self) -> &mut Vec<Attribute>;
    fn block_mut(&mut self) -> Option<&mut Block>;
}

impl AnyAttrBlock for ItemFn {
    fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        &mut self.attrs
    }

    fn block_mut(&mut self) -> Option<&mut Block> {
        Some(&mut self.block)
    }
}

impl AnyAttrBlock for ImplItemFn {
    fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        &mut self.attrs
    }

    fn block_mut(&mut self) -> Option<&mut Block> {
        Some(&mut self.block)
    }
}

impl AnyAttrBlock for ExprLoop {
    fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        &mut self.attrs
    }

    fn block_mut(&mut self) -> Option<&mut Block> {
        Some(&mut self.body)
    }
}

impl AnyAttrBlock for ExprForLoop {
    fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        &mut self.attrs
    }

    fn block_mut(&mut self) -> Option<&mut Block> {
        Some(&mut self.body)
    }
}

impl AnyAttrBlock for ExprWhile {
    fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        &mut self.attrs
    }

    fn block_mut(&mut self) -> Option<&mut Block> {
        Some(&mut self.body)
    }
}

impl AnyAttrBlock for TraitItemFn {
    fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        &mut self.attrs
    }

    fn block_mut(&mut self) -> Option<&mut Block> {
        self.default.as_mut()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AnyFnOrLoop {
    ImplFn(syn::ImplItemFn),
    Fn(syn::ItemFn),
    TraitMethod(syn::TraitItemFn),
    Loop(syn::ExprLoop),
    ForLoop(syn::ExprForLoop),
    While(syn::ExprWhile),
    Closure(syn::ExprClosure), // Added for completeness, if needed
}

impl syn::parse::Parse for AnyFnOrLoop {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative;
        // Dual-parse ImplItemFn and ItemFn, then disambiguate.
        let fork_impl = input.fork();
        let parsed_impl = fork_impl.parse::<ImplItemFn>();
        let fork_fn = input.fork();
        let parsed_fn = fork_fn.parse::<ItemFn>();

        match (parsed_impl, parsed_fn) {
            (Ok(method), Err(_)) => {
                input.advance_to(&fork_impl);
                return Ok(AnyFnOrLoop::ImplFn(method));
            }
            (Err(_), Ok(func)) => {
                input.advance_to(&fork_fn);
                return Ok(AnyFnOrLoop::Fn(func));
            }
            (Ok(method), Ok(func)) => {
                // Use span-based disambiguation only (if-else style).
                if let Some(true) = is_inside_impl_by_span(method.span(), &method.sig) {
                    input.advance_to(&fork_impl);
                    return Ok(AnyFnOrLoop::ImplFn(method));
                } else {
                    input.advance_to(&fork_fn);
                    return Ok(AnyFnOrLoop::Fn(func));
                }
            }
            (Err(_), Err(_)) => { /* continue to other parses below */ }
        }

        // Try to parse as TraitItemFn
        let fork = input.fork();
        if let Ok(method) = fork.parse::<TraitItemFn>() {
            input.advance_to(&fork);
            return Ok(AnyFnOrLoop::TraitMethod(method));
        }

        // Try to parse as ExprLoop
        let fork = input.fork();
        if let Ok(loop_expr) = fork.parse::<ExprLoop>() {
            input.advance_to(&fork);
            return Ok(AnyFnOrLoop::Loop(loop_expr));
        }

        // Try to parse as ExprForLoop
        let fork = input.fork();
        if let Ok(for_loop_expr) = fork.parse::<ExprForLoop>() {
            input.advance_to(&fork);
            return Ok(AnyFnOrLoop::ForLoop(for_loop_expr));
        }

        // Try to parse as ExprWhile
        let fork = input.fork();
        if let Ok(while_expr) = fork.parse::<ExprWhile>() {
            input.advance_to(&fork);
            return Ok(AnyFnOrLoop::While(while_expr));
        }

        // Try to parse as ExprClosure (if needed)
        let fork = input.fork();
        if let Ok(closure_expr) = fork.parse::<syn::ExprClosure>() {
            input.advance_to(&fork);
            if input.peek(syn::token::Comma) {
                input.parse::<syn::token::Comma>()?;
            }
            return Ok(AnyFnOrLoop::Closure(closure_expr));
        }

        // If none of the above matched, return an error
        Err(input.error("Expected a function item or loop expression"))
    }
}

pub trait FunctionLike: AnyAttrBlock + ToTokens + Clone {
    fn sig(&self) -> &Signature;
    fn sig_mut(&mut self) -> &mut Signature;
}

impl FunctionLike for ItemFn {
    fn sig(&self) -> &Signature {
        &self.sig
    }
    fn sig_mut(&mut self) -> &mut Signature {
        &mut self.sig
    }
}

impl FunctionLike for ImplItemFn {
    fn sig(&self) -> &Signature {
        &self.sig
    }
    fn sig_mut(&mut self) -> &mut Signature {
        &mut self.sig
    }
}
