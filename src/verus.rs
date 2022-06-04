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

ast_struct! {
    pub struct Assert {
        pub attrs: Vec<Attribute>,
        pub assert_token: Token![assert],
        pub paren_token: token::Paren,
        pub expr: Box<Expr>,
        /// by_token is only used if prover and/or body is Some
        pub by_token: Option<Token![by]>,
        pub prover: Option<(token::Paren, Ident)>,
        pub body: Option<Box<(Option<Requires>, Block)>>,
    }
}

ast_struct! {
    pub struct AssertForall {
        pub attrs: Vec<Attribute>,
        pub assert_token: Token![assert],
        pub forall_token: Token![forall],
        pub paren_token: token::Paren,
        pub inputs: Punctuated<Pat, Token![,]>,
        pub expr: Box<Expr>,
        pub implies: Option<(Token![implies], Box<Expr>)>,
        pub by_token: Token![by],
        pub body: Box<Block>,
    }
}

ast_struct! {
    pub struct Assume {
        pub attrs: Vec<Attribute>,
        pub assume_token: Token![assume],
        pub paren_token: token::Paren,
        pub expr: Box<Expr>,
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
                let expr = Expr::parse_without_eager_brace(input)?;
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

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Assume {
        fn parse(input: ParseStream) -> Result<Self> {
            let attrs = Vec::new();
            let assume_token: Token![assume] = input.parse()?;
            let content;
            let paren_token = parenthesized!(content in input);
            let expr = content.parse()?;
            if !content.is_empty() {
                return Err(content.error("expected `)`"));
            }
            Ok(Assume {
                attrs,
                assume_token,
                paren_token,
                expr,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Assert {
        fn parse(input: ParseStream) -> Result<Self> {
            let attrs = Vec::new();
            let assert_token: Token![assert] = input.parse()?;
            let content;
            let paren_token = parenthesized!(content in input);
            let expr = content.parse()?;
            if !content.is_empty() {
                return Err(content.error("expected `)`"));
            }
            if input.peek(Token![by]) {
                let by_token = input.parse()?;
                let prover = if input.peek(token::Paren) {
                    let content;
                    let paren_token = parenthesized!(content in input);
                    let id = content.parse()?;
                    Some((paren_token, id))
                } else {
                    None
                };
                let body = if input.peek(Token![requires]) || input.peek(token::Brace) {
                    let requires = input.parse()?;
                    let block = input.parse()?;
                    Some(Box::new((requires, block)))
                } else {
                    None
                };
                if prover.is_none() && body.is_none() {
                    return Err(content.error("expected `(` or `{` after `by`"));
                }
                Ok(Assert {
                    attrs,
                    assert_token,
                    paren_token,
                    expr,
                    by_token,
                    prover,
                    body,
                })
            } else {
                let by_token = None;
                let prover = None;
                let body = None;
                Ok(Assert {
                    attrs,
                    assert_token,
                    paren_token,
                    expr,
                    by_token,
                    prover,
                    body,
                })
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for AssertForall {
        fn parse(input: ParseStream) -> Result<Self> {
            let attrs = Vec::new();
            let assert_token: Token![assert] = input.parse()?;
            let forall_token: Token![forall] = input.parse()?;
            let content;
            let paren_token = parenthesized!(content in input);
            let mut inputs = Punctuated::new();
            while !content.is_empty() {
                let mut pat = content.parse()?;
                if content.peek(Token![:]) {
                    let colon_token = content.parse()?;
                    let ty = content.parse()?;
                    pat = Pat::Type(PatType {
                        attrs: vec![],
                        pat: Box::new(pat),
                        colon_token,
                        ty,
                    });
                }
                inputs.push_value(pat);
                if content.is_empty() {
                    break;
                }
                let comma: Token![,] = content.parse()?;
                inputs.push_punct(comma);
            }
            let expr = input.parse()?;
            let implies = if input.peek(Token![implies]) {
                let implies_token = input.parse()?;
                let expr2 = input.parse()?;
                Some((implies_token, expr2))
            } else {
                None
            };
            let by_token = input.parse()?;
            let body = input.parse()?;
            Ok(AssertForall {
                attrs,
                assert_token,
                forall_token,
                paren_token,
                inputs,
                expr,
                implies,
                by_token,
                body,
            })
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

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Assume {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            crate::expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            self.assume_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Assert {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            crate::expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            self.assert_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
            });
            if let Some(by_token) = &self.by_token {
                if self.prover.is_some() || self.body.is_some() {
                    by_token.to_tokens(tokens);
                    if let Some((paren, id)) = &self.prover {
                        paren.surround(tokens, |tokens| {
                            id.to_tokens(tokens);
                        });
                    }
                    if let Some(box (requires, body)) = &self.body {
                        requires.to_tokens(tokens);
                        body.to_tokens(tokens);
                    }
                }
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for AssertForall {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            crate::expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            self.assert_token.to_tokens(tokens);
            self.forall_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.inputs.to_tokens(tokens);
            });
            self.expr.to_tokens(tokens);
            if let Some((implies, expr)) = &self.implies {
                implies.to_tokens(tokens);
                expr.to_tokens(tokens);
            }
            self.by_token.to_tokens(tokens);
            self.body.to_tokens(tokens);
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
