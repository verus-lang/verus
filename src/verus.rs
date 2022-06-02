use super::*;
use crate::punctuated::Punctuated;

ast_enum_of_structs! {
    pub enum Mode {
        Spec(ModeSpec),
        Proof(ModeProof),
        Exec(ModeExec),
        Default,
    }
}

ast_enum_of_structs! {
    pub enum FnMode {
        Spec(ModeSpec),
        SpecChecked(ModeSpecChecked),
        Proof(ModeProof),
        Exec(ModeExec),
        Default,
    }
}

ast_struct! {
    pub struct ModeSpec {
        pub spec_token: Token![spec],
    }
}

ast_struct! {
    pub struct ModeProof {
        pub proof_token: Token![proof],
    }
}

ast_struct! {
    pub struct ModeExec {
        pub exec_token: Token![exec],
    }
}

ast_struct! {
    pub struct ModeSpecChecked {
        pub spec_token: Token![spec],
        pub paren_token: token::Paren,
        pub checked: Box<Ident>,
    }
}

ast_struct! {
    pub struct Specification {
        pub exprs: Punctuated<Expr, Token![,]>,
    }
}

ast_struct! {
    pub struct Requires {
        pub token: Token![requires],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct Recommends {
        pub token: Token![recommends],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct Ensures {
        pub token: Token![ensures],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct Decreases {
        pub token: Token![requires],
        pub exprs: Specification,
    }
}

#[cfg(feature = "parsing")]
pub mod parsing {
    use super::*;
    use crate::parse::{Parse, ParseStream, Result};

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Mode {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![spec]) {
                let spec_token: Token![spec] = input.parse()?;
                Ok(Mode::Spec(ModeSpec { spec_token }))
            } else if input.peek(Token![proof]) {
                let proof_token: Token![proof] = input.parse()?;
                Ok(Mode::Proof(ModeProof { proof_token }))
            } else if input.peek(Token![exec]) {
                let exec_token: Token![exec] = input.parse()?;
                Ok(Mode::Exec(ModeExec { exec_token }))
            } else {
                Ok(Mode::Default)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for FnMode {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![spec]) {
                let spec_token: Token![spec] = input.parse()?;
                if input.peek(token::Paren) {
                    let content;
                    let paren_token = parenthesized!(content in input);
                    let checked = Box::new(input.parse()?);
                    if !content.is_empty() {
                        return Err(content.error("expected `)`"));
                    }
                    Ok(FnMode::SpecChecked(ModeSpecChecked {
                        spec_token,
                        paren_token,
                        checked,
                    }))
                } else {
                    Ok(FnMode::Spec(ModeSpec { spec_token }))
                }
            } else if input.peek(Token![proof]) {
                let proof_token: Token![proof] = input.parse()?;
                Ok(FnMode::Proof(ModeProof { proof_token }))
            } else if input.peek(Token![exec]) {
                let exec_token: Token![exec] = input.parse()?;
                Ok(FnMode::Exec(ModeExec { exec_token }))
            } else {
                Ok(FnMode::Default)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Specification {
        fn parse(input: ParseStream) -> Result<Self> {
            let mut exprs = Punctuated::new();
            while !(input.is_empty()
                || input.peek(token::Brace)
                || input.peek(Token![ensures])
                || input.peek(Token![decreases]))
            {
                let expr: Expr = input.parse()?;
                exprs.push(expr);
                if !input.peek(Token![,]) {
                    break;
                }
                let punct = input.parse()?;
                exprs.push_punct(punct);
            }
            Ok(Specification { exprs })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Requires {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(Requires {
                token: input.parse()?,
                exprs: input.parse()?,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Recommends {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(Recommends {
                token: input.parse()?,
                exprs: input.parse()?,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Ensures {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(Ensures {
                token: input.parse()?,
                exprs: input.parse()?,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Decreases {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(Decreases {
                token: input.parse()?,
                exprs: input.parse()?,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Option<Requires> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![requires]) {
                input.parse().map(Some)
            } else {
                Ok(None)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Option<Recommends> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![recommends]) {
                input.parse().map(Some)
            } else {
                Ok(None)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Option<Ensures> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![ensures]) {
                input.parse().map(Some)
            } else {
                Ok(None)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Option<Decreases> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![decreases]) {
                input.parse().map(Some)
            } else {
                Ok(None)
            }
        }
    }
}

#[cfg(feature = "printing")]
mod printing {
    use super::*;
    use proc_macro2::TokenStream;
    use quote::ToTokens;

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeSpec {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.spec_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeProof {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.proof_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeExec {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.exec_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeSpecChecked {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.spec_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.checked.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Specification {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.exprs.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Requires {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
            self.exprs.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Recommends {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
            self.exprs.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Ensures {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
            self.exprs.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Decreases {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
            self.exprs.to_tokens(tokens);
        }
    }
}

pub(crate) fn disallow_prefix_binop(input: crate::parse::ParseStream) -> crate::parse::Result<()> {
    // Be conservative with &&& and ||| so we don't run into any ambiguities.
    // We could try to allow (&&&...) and (|||...), but (...) can also be used for tuples,
    // which might be more than we want.
    if input.peek(Token![&&&]) {
        Err(input.error("leading &&& must be inside a block {...}"))
    } else if input.peek(Token![|||]) {
        Err(input.error("leading ||| must be inside a block {...}"))
    } else {
        Ok(())
    }
}

#[cfg(feature = "full")]
pub(crate) fn parse_prefix_binop(
    input: crate::parse::ParseStream,
    attrs: &Vec<Attribute>,
) -> Result<Option<(crate::op::UnOp, crate::op::BinOp)>> {
    if input.peek(Token![&&&]) {
        if attrs.len() != 0 {
            return Err(input.error("`&&&` cannot have attributes"));
        }
        let token: Token![&&&] = input.parse().expect("&&&");
        Ok(Some((
            crate::op::UnOp::BigAnd(token),
            crate::op::BinOp::BigAnd(token),
        )))
    } else if input.peek(Token![|||]) {
        if attrs.len() != 0 {
            return Err(input.error("`|||` cannot have attributes"));
        }
        let token: Token![|||] = input.parse().expect("|||");
        Ok(Some((
            crate::op::UnOp::BigOr(token),
            crate::op::BinOp::BigOr(token),
        )))
    } else {
        Ok(None)
    }
}
