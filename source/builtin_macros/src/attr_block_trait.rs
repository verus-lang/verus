use syn::{
    Attribute, Block, ExprForLoop, ExprLoop, ExprWhile, ImplItemMethod, ItemFn, TraitItemMethod,
};

pub trait AnyAttrBlock {
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

impl AnyAttrBlock for ImplItemMethod {
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

impl AnyAttrBlock for TraitItemMethod {
    fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        &mut self.attrs
    }

    fn block_mut(&mut self) -> Option<&mut Block> {
        self.default.as_mut()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AnyFnOrLoop {
    Fn(syn::ItemFn),
    TraitMethod(syn::TraitItemMethod),
    Loop(syn::ExprLoop),
    ForLoop(syn::ExprForLoop),
    While(syn::ExprWhile),
}

impl syn::parse::Parse for AnyFnOrLoop {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative;
        // Try to parse as ItemFn
        let fork = input.fork();
        if let Ok(func) = fork.parse::<ItemFn>() {
            input.advance_to(&fork);
            return Ok(AnyFnOrLoop::Fn(func));
        }

        // Try to parse as TraitItemMethod
        let fork = input.fork();
        if let Ok(method) = fork.parse::<TraitItemMethod>() {
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

        // If none of the above matched, return an error
        Err(input.error("Expected a function item or loop expression"))
    }
}
