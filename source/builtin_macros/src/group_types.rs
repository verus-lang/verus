use std::f32::consts::E;

use syn::{
    parse, Expr, ExprForLoop, ExprLoop, ExprWhile, ImplItemMethod, Item, ItemFn, TraitItemMethod,
};

#[derive(Debug, PartialEq, Eq)]
pub enum AnyFnItem {
    Fn(ItemFn),
    TraitMethod(TraitItemMethod),
    ImplMethod(ImplItemMethod),
}

impl parse::Parse for AnyFnItem {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative;
        let fork = input.fork();
        let item_fn = fork.parse();
        match item_fn {
            Ok(res) => {
                // We have an item Fn.
                input.advance_to(&fork);
                Ok(AnyFnItem::Fn(res))
            }
            Err(_) => {
                // It is not a valid ItemFn.
                let item_method = input.parse();
                match item_method {
                    Ok(m) => Ok(AnyFnItem::TraitMethod(item_method)),
                    Err(e) => Ok(AnyFnItem::ImplMethod(input.parse()?)),
                }
            }
        }
    }
}

impl AnyFnItem {
    pub fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        match self {
            AnyFnItem::Fn(item) => &mut item.attrs,
            AnyFnItem::TraitMethod(item) => &mut item.attrs,
            AnyFnItem::ImplMethod(item) => &mut item.attrs,
        }
    }

    pub fn block_mut(&mut self) -> Option<&mut Block> {
        match self {
            AnyFnItem::Fn(item) => Some(&mut item.block),
            AnyFnItem::ImplMethod(item) => Some(&mut item.block),
            AnyFnItem::TraitMethod(item) => item.default.as_mut(),
        }
    }
}

impl quote::ToTokens for AnyFnItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            AnyFnItem::Fn(item) => item.to_tokens(tokens),
            AnyFnItem::TraitMethod(item) => item.to_tokens(tokens),
            AnyFnItem::ImplMethod(item) => item.to_tokens(tokens),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AnyLoopItem {
    While(ExprWhile),
    Loop(ExprLoop),
    ForLoop(ExprForLoop),
}

impl parse::Parse for AnyLoopItem {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let item: Result<Expr> = input.parse();
        match item {
            Ok(e) => match e {
                Expr::ForLoop(w) => Ok(AnyLoopItem::ForLoop(w)),
                Expr::Loop(w) => Ok(AnyLoopItem::Loop(w)),
                Expr::While(w) => Ok(AnyLoopItem::While(w)),
                _ => {
                    panic!("Not in loop")
                }
            },
            Err(e) => Err(e),
        }
    }
}

impl AnyLoopItem {
    pub fn attrs_mut(&mut self) -> &mut Vec<Attribute> {
        match self {
            AnyLoopItem::ForLoop(e) => &mut l.attrs,
            AnyLoopItem::Loop(e) => &mut l.attrs,
            AnyLoopItem::While(e) => &mut l.attrs,
        }
    }

    pub fn block_mut(&mut self) -> Option<&mut Block> {
        match self {
            AnyLoopItem::ForLoop(e) => Some(&mut e.body),
            AnyLoopItem::Loop(e) => Some(&mut e.body),
            AnyLoopItem::While(e) => Some(&mut e.body),
        }
    }
}

impl quote::ToTokens for AnyLoopItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            AnyLoopItem::ForLoop(e) => e.to_tokens(tokens),
            AnyLoopItem::Loop(e) => e.to_tokens(tokens),
            AnyLoopItem::While(e) => e.to_tokens(tokens),
        }
    }
}
