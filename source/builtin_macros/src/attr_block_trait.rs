//#[warn(unused_imports)]
/*use syn::parse_quote;*/
use syn::{
    Attribute, Block, ExprForLoop, ExprLoop, ExprWhile, ImplItemMethod, ItemFn,
    TraitItemMethod
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
