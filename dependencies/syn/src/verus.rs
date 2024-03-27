use super::*;
use crate::punctuated::Punctuated;

ast_enum_of_structs! {
    pub enum Publish {
        Closed(Closed),
        Open(Open),
        OpenRestricted(OpenRestricted),
        Default,
    }
}

ast_struct! {
    pub struct Closed {
        pub token: Token![closed],
    }
}

ast_struct! {
    pub struct Open {
        pub token: Token![open],
    }
}

ast_struct! {
    pub struct OpenRestricted {
        pub open_token: Token![open],
        pub paren_token: token::Paren,
        pub in_token: Option<Token![in]>,
        pub path: Box<Path>,
    }
}

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

ast_enum_of_structs! {
    pub enum DataMode {
        Ghost(ModeGhost),
        Tracked(ModeTracked),
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
    pub struct ModeGhost {
        pub ghost_token: Token![ghost],
    }
}

ast_struct! {
    pub struct ModeProof {
        pub proof_token: Token![proof],
    }
}

ast_struct! {
    pub struct ModeTracked {
        pub tracked_token: Token![tracked],
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
        pub via: Option<(Token![via], Expr)>,
    }
}

ast_struct! {
    pub struct Ensures {
        pub attrs: Vec<Attribute>,
        pub token: Token![ensures],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct InvariantExceptBreak {
        pub token: Token![invariant_except_break],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct Invariant {
        pub token: Token![invariant],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct InvariantEnsures {
        pub token: Token![invariant_ensures],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct Decreases {
        pub token: Token![decreases],
        pub exprs: Specification,
    }
}

ast_struct! {
    pub struct SignatureDecreases {
        pub decreases: Decreases,
        pub when: Option<(Token![when], Expr)>,
        pub via: Option<(Token![via], Expr)>,
    }
}

ast_struct! {
    pub struct SignatureInvariants {
        pub token: Token![opens_invariants],
        pub set: InvariantNameSet,
    }
}

ast_enum_of_structs! {
    pub enum InvariantNameSet {
        Any(InvariantNameSetAny),
        None(InvariantNameSetNone),
        List(InvariantNameSetList),
    }
}

ast_struct! {
    pub struct InvariantNameSetAny {
        pub token: Token![any],
    }
}

ast_struct! {
    pub struct InvariantNameSetNone {
        pub token: Token![none],
    }
}

ast_struct! {
    pub struct InvariantNameSetList {
        pub bracket_token: token::Bracket,
        pub exprs: Punctuated<Expr, Token![,]>,
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
        pub requires: Option<Requires>,
        pub body: Option<Box<Block>>,
    }
}

ast_struct! {
    pub struct AssertForall {
        pub attrs: Vec<Attribute>,
        pub assert_token: Token![assert],
        pub forall_token: Token![forall],
        pub or1_token: Token![|],
        pub inputs: Punctuated<Pat, Token![,]>,
        pub or2_token: Token![|],
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

ast_struct! {
    pub struct RevealHide {
        pub attrs: Vec<Attribute>,
        pub reveal_token: Option<Token![reveal]>,
        pub reveal_with_fuel_token: Option<Token![reveal_with_fuel]>,
        pub hide_token: Option<Token![hide]>,
        pub paren_token: token::Paren,
        pub path: Box<ExprPath>,
        pub fuel: Option<(Token![,], Box<Expr>)>,
    }
}

ast_struct! {
    pub struct ItemBroadcastGroup {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub broadcast_group_tokens: (Token![broadcast], Token![group]),
        pub ident: Ident,
        pub brace_token: token::Brace,
        pub paths: Punctuated<ExprPath, Token![,]>,
    }
}

ast_struct! {
    pub struct BroadcastUse {
        pub attrs: Vec<Attribute>,
        pub broadcast_use_tokens: (Token![broadcast], Token![use]),
        pub paths: Punctuated<ExprPath, Token![,]>,
        pub semi: Token![;],
    }
}

ast_struct! {
    pub struct View {
        pub attrs: Vec<Attribute>,
        pub expr: Box<Expr>,
        pub at_token: Token![@],
    }
}

ast_struct! {
    /// A FnSpec type: `FnSpec(usize) -> bool`.
    /// Parsed similarly to TypeBareFn
    pub struct TypeFnSpec {
        pub fn_spec_token: Option<Token![FnSpec]>, // deprecated TODO remove
        pub spec_fn_token: Option<Token![SpecFn]>,
        pub paren_token: token::Paren,
        pub inputs: Punctuated<BareFnArg, Token![,]>,
        pub output: ReturnType,
    }
}

ast_struct! {
    pub struct BigAnd {
        /// exprs.len() must be >= 1
        pub exprs: Vec<(Token![&&&], Box<Expr>)>,
    }
}

ast_struct! {
    pub struct BigOr {
        /// exprs.len() must be >= 1
        pub exprs: Vec<(Token![|||], Box<Expr>)>,
    }
}

ast_struct! {
    pub struct ExprIs {
        pub attrs: Vec<Attribute>,
        pub base: Box<Expr>,
        pub is_token: Token![is],
        pub variant_ident: Box<Ident>,
    }
}

ast_struct! {
    pub struct ExprHas {
        pub attrs: Vec<Attribute>,
        pub lhs: Box<Expr>,
        pub has_token: Token![has],
        pub rhs: Box<Expr>,
    }
}

ast_enum! {
    pub enum MatchesOpToken {
        Implies(Token![==>]),
        AndAnd(Token![&&]),
        BigAnd,
    }
}

ast_struct! {
    pub struct MatchesOpExpr {
        pub op_token: MatchesOpToken,
        pub rhs: Box<Expr>,
    }
}

ast_struct! {
    pub struct GlobalSizeOf {
        pub size_of_token: Token![size_of],
        pub type_: Type,
        pub eq_token: Token![==],
        pub expr_lit: ExprLit,
    }
}

ast_struct! {
    pub struct GlobalLayout {
        pub layout_token: Token![layout],
        pub type_: Type,
        pub is_token: Token![is],
        pub size: (Ident, Token![==], ExprLit),
        pub align: Option<(Token![,], Ident, Token![==], ExprLit)>,
    }
}

ast_enum_of_structs! {
    pub enum GlobalInner {
        SizeOf(GlobalSizeOf),
        Layout(GlobalLayout),
    }
}

ast_struct! {
    pub struct Global {
        pub attrs: Vec<Attribute>,
        pub global_token: Token![global],
        pub inner: GlobalInner,
        pub semi: Token![;],
    }
}

ast_struct! {
    pub struct ExprMatches {
        pub attrs: Vec<Attribute>,
        pub lhs: Box<Expr>,
        pub matches_token: Token![matches],
        pub pat: Pat,
        pub op_expr: Option<MatchesOpExpr>,
    }
}

ast_struct! {
    pub struct ExprGetField {
        pub attrs: Vec<Attribute>,
        pub base: Box<Expr>,
        pub arrow_token: Token![->],
        pub member: Member,
    }
}

#[cfg(feature = "parsing")]
pub mod parsing {
    use super::*;
    use crate::parse::{Parse, ParseStream, Result};

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Publish {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![closed]) {
                let token = input.parse::<Token![closed]>()?;
                Ok(Publish::Closed(Closed { token }))
            } else if input.peek(Token![open]) {
                let token = input.parse::<Token![open]>()?;
                if let Some((paren_token, in_token, path)) = Visibility::parse_restricted(input)? {
                    Ok(Publish::OpenRestricted(OpenRestricted {
                        open_token: token,
                        paren_token,
                        in_token,
                        path,
                    }))
                } else {
                    Ok(Publish::Open(Open { token }))
                }
            } else {
                Ok(Publish::Default)
            }
        }
    }

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
    impl Parse for DataMode {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![ghost]) {
                let ghost_token: Token![ghost] = input.parse()?;
                Ok(DataMode::Ghost(ModeGhost { ghost_token }))
            } else if input.peek(Token![tracked]) {
                let tracked_token: Token![tracked] = input.parse()?;
                Ok(DataMode::Tracked(ModeTracked { tracked_token }))
            } else if input.peek(Token![exec]) {
                let exec_token: Token![exec] = input.parse()?;
                Ok(DataMode::Exec(ModeExec { exec_token }))
            } else {
                Ok(DataMode::Default)
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
                    let checked = Box::new(content.parse()?);
                    if !matches!(&*checked, Ident { .. }) || checked.to_string() != "checked" {
                        return Err(content.error("expected `spec(checked)`"));
                    }
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
                || input.peek(Token![;])
                || input.peek(Token![invariant_except_break])
                || input.peek(Token![invariant])
                || input.peek(Token![invariant_ensures])
                || input.peek(Token![ensures])
                || input.peek(Token![decreases])
                || input.peek(Token![via])
                || input.peek(Token![when])
                || input.peek(Token![opens_invariants]))
            {
                let expr = Expr::parse_without_eager_brace(input)?;
                exprs.push(expr);
                if !input.peek(Token![,]) {
                    break;
                }
                let punct = input.parse()?;
                exprs.push_punct(punct);
            }
            if input.peek(token::Brace) {
                if input.peek2(token::Brace) {
                    return Err(input.error("This block would be parsed as the function/loop body, but it is followed immediately by another block (if you meant this block to be part of the specification, try parenthesizing it)"));
                }
                if input.peek2(token::Comma) {
                    return Err(input.error("This block would be parsed as the function/loop body, but it is followed immediately by a comma (if you meant this block to be part of the specification, try parenthesizing it)"));
                }
                if input.peek2(Token![ensures]) {
                    return Err(input.error("This block would be parsed as the function/loop body, but it is followed immediately by an 'ensures' (if you meant this block to be part of the specification, try parenthesizing it)"));
                }
                if input.peek2(Token![opens_invariants]) {
                    return Err(input.error("This block would be parsed as the function/loop body, but it is followed immediately by an 'opens_invariants' (if you meant this block to be part of the specification, try parenthesizing it)"));
                }
                if input.peek2(Token![invariant_except_break]) {
                    return Err(input.error("This block would be parsed as the function/loop body, but it is followed immediately by an 'invariant_except_break' (if you meant this block to be part of the specification, try parenthesizing it)"));
                }
                if input.peek2(Token![invariant]) {
                    return Err(input.error("This block would be parsed as the function/loop body, but it is followed immediately by an 'invariant' (if you meant this block to be part of the specification, try parenthesizing it)"));
                }
                if input.peek2(Token![decreases]) {
                    return Err(input.error("This block would be parsed as the function/loop body, but it is followed immediately by a 'decreases' (if you meant this block to be part of the specification, try parenthesizing it)"));
                }
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
            let token = input.parse()?;
            let exprs = input.parse()?;
            let via = if input.peek(Token![via]) {
                let via_token: Token![via] = input.parse()?;
                // let expr = input.parse()?;
                let expr = Expr::parse_without_eager_brace(input)?;
                Some((via_token, expr))
            } else {
                None
            };
            Ok(Recommends { token, exprs, via })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Ensures {
        fn parse(input: ParseStream) -> Result<Self> {
            let mut attrs = Vec::new();
            let token = input.parse()?;
            attr::parsing::parse_inner(input, &mut attrs)?;
            Ok(Ensures {
                attrs,
                token,
                exprs: input.parse()?,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for InvariantExceptBreak {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(InvariantExceptBreak {
                token: input.parse()?,
                exprs: input.parse()?,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Invariant {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(Invariant {
                token: input.parse()?,
                exprs: input.parse()?,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for InvariantEnsures {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(InvariantEnsures {
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
    impl Parse for SignatureDecreases {
        fn parse(input: ParseStream) -> Result<Self> {
            let decreases = input.parse()?;
            let when = if input.peek(Token![when]) {
                let when_token = input.parse()?;
                let expr = Expr::parse_without_eager_brace(input)?;
                Some((when_token, expr))
            } else {
                None
            };
            let via = if input.peek(Token![via]) {
                let via_token = input.parse()?;
                let expr = Expr::parse_without_eager_brace(input)?;
                Some((via_token, expr))
            } else {
                None
            };
            Ok(SignatureDecreases {
                decreases,
                when,
                via,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for SignatureInvariants {
        fn parse(input: ParseStream) -> Result<Self> {
            let opens_invariants = input.parse()?;
            let set = input.parse()?;

            Ok(SignatureInvariants {
                token: opens_invariants,
                set,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Option<SignatureInvariants> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![opens_invariants]) {
                input.parse().map(Some)
            } else {
                Ok(None)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for InvariantNameSet {
        fn parse(input: ParseStream) -> Result<Self> {
            let set = if input.peek(Token![any]) {
                let all = input.parse()?;
                InvariantNameSet::Any(all)
            } else if input.peek(Token![none]) {
                let none = input.parse()?;
                InvariantNameSet::None(none)
            } else if input.peek(token::Bracket) {
                let list = input.parse()?;
                InvariantNameSet::List(list)
            } else {
                return Err(input.error("invariant clause expected `any` or `none`"));
            };
            Ok(set)
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for InvariantNameSetAny {
        fn parse(input: ParseStream) -> Result<Self> {
            let token_all = input.parse()?;
            Ok(InvariantNameSetAny { token: token_all })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for InvariantNameSetNone {
        fn parse(input: ParseStream) -> Result<Self> {
            let token_none = input.parse()?;
            Ok(InvariantNameSetNone { token: token_none })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for InvariantNameSetList {
        fn parse(input: ParseStream) -> Result<Self> {
            let content;
            let bracket_token = bracketed!(content in input);
            let exprs = content.parse_terminated(Expr::parse)?;
            Ok(InvariantNameSetList {
                bracket_token,
                exprs,
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
    impl Parse for Option<InvariantExceptBreak> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![invariant_except_break]) {
                input.parse().map(Some)
            } else {
                Ok(None)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Option<Invariant> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![invariant]) {
                input.parse().map(Some)
            } else {
                Ok(None)
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Option<InvariantEnsures> {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![invariant_ensures]) {
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
    impl Parse for Option<SignatureDecreases> {
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
                let (requires, body) = if input.peek(Token![requires]) || input.peek(token::Brace) {
                    let requires = input.parse()?;
                    let block = if input.peek(token::Brace) {
                        Some(Box::new(input.parse()?))
                    } else {
                        None
                    };
                    (requires, block)
                } else {
                    (None, None)
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
                    requires,
                    body,
                })
            } else {
                let by_token = None;
                let prover = None;
                let requires = None;
                let body = None;
                Ok(Assert {
                    attrs,
                    assert_token,
                    paren_token,
                    expr,
                    by_token,
                    prover,
                    requires,
                    body,
                })
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for AssertForall {
        fn parse(input: ParseStream) -> Result<Self> {
            let mut attrs = Vec::new();
            let assert_token: Token![assert] = input.parse()?;
            let forall_token: Token![forall] = input.parse()?;
            let or1_token: Token![|] = input.parse()?;
            let mut inputs = Punctuated::new();
            while !input.peek(Token![|]) {
                let mut pat = input.parse()?;
                if input.peek(Token![:]) {
                    let colon_token = input.parse()?;
                    let ty = input.parse()?;
                    pat = Pat::Type(PatType {
                        attrs: vec![],
                        pat: Box::new(pat),
                        colon_token,
                        ty,
                    });
                }
                inputs.push_value(pat);
                if input.peek(Token![|]) {
                    break;
                }
                let comma: Token![,] = input.parse()?;
                inputs.push_punct(comma);
            }
            let or2_token: Token![|] = input.parse()?;
            attr::parsing::parse_inner(input, &mut attrs)?;
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
                or1_token,
                inputs,
                or2_token,
                expr,
                implies,
                by_token,
                body,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for RevealHide {
        fn parse(input: ParseStream) -> Result<Self> {
            let attrs = Vec::new();
            let lookahead = input.lookahead1();
            let mut reveal_token = None;
            let mut reveal_with_fuel_token = None;
            let mut hide_token = None;
            if lookahead.peek(Token![reveal]) {
                reveal_token = input.parse()?;
            } else if lookahead.peek(Token![reveal_with_fuel]) {
                reveal_with_fuel_token = input.parse()?;
            } else if lookahead.peek(Token![hide]) {
                hide_token = input.parse()?;
            } else {
                return Err(lookahead.error());
            }

            let content;
            let paren_token = parenthesized!(content in input);
            let path = content.parse()?;

            // Parse a possible comma (either trailing for hide/reveal,
            // or as a preface to a fuel argument
            let comma: Option<Token![,]> = content.parse()?;

            let fuel = if reveal_with_fuel_token.is_some() && comma.is_some() {
                let f = Some((comma.unwrap(), content.parse()?));
                let _trailing_comma: Option<Token![,]> = content.parse()?;
                f
            } else {
                None
            };

            Ok(RevealHide {
                attrs,
                reveal_token,
                reveal_with_fuel_token,
                hide_token,
                paren_token,
                path,
                fuel,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for BroadcastUse {
        fn parse(input: ParseStream) -> Result<Self> {
            let attrs = Vec::new();
            let broadcast_use_tokens: (Token![broadcast], Token![use]) =
                (input.parse()?, input.parse()?);
            let mut paths = Punctuated::new();
            let semi = loop {
                let path: ExprPath = input.parse()?;
                paths.push(path);
                if input.peek(Token![,]) {
                    let _: Token![,] = input.parse()?;
                    continue;
                } else {
                    let semi: Token![;] = input.parse()?;
                    break semi;
                }
            };

            Ok(BroadcastUse {
                attrs,
                broadcast_use_tokens,
                paths,
                semi,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for ItemBroadcastGroup {
        fn parse(input: ParseStream) -> Result<Self> {
            let attrs = Vec::new();
            let vis: Visibility = input.parse()?;
            let broadcast_group_tokens: (Token![broadcast], Token![group]) =
                (input.parse()?, input.parse()?);
            let ident = input.parse()?;
            let content;
            let brace_token = braced!(content in input);
            let paths = content.parse_terminated(ExprPath::parse)?;

            Ok(ItemBroadcastGroup {
                attrs,
                vis,
                ident,
                broadcast_group_tokens,
                brace_token,
                paths,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for Global {
        fn parse(input: ParseStream) -> Result<Self> {
            let attrs = Vec::new();
            let global_token: Token![global] = input.parse()?;
            let inner: GlobalInner = input.parse()?;
            let semi: Token![;] = input.parse()?;

            Ok(Global {
                attrs,
                global_token,
                inner,
                semi,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for GlobalSizeOf {
        fn parse(input: ParseStream) -> Result<Self> {
            let size_of_token: Token![size_of] = input.parse()?;
            let type_: Type = input.parse()?;
            let eq_token: Token![==] = input.parse()?;
            let expr_lit: ExprLit = input.parse()?;

            Ok(GlobalSizeOf {
                size_of_token,
                type_,
                eq_token,
                expr_lit,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for GlobalLayout {
        fn parse(input: ParseStream) -> Result<Self> {
            let layout_token: Token![layout] = input.parse()?;
            let type_: Type = input.parse()?;
            let is_token: Token![is] = input.parse()?;
            let size_ident: Ident = input.parse()?;
            if size_ident.to_string() != "size" {
                return Err(input.error("expected `size`"));
            }
            let size_eq_token: Token![==] = input.parse()?;
            let size_expr_lit: ExprLit = input.parse()?;
            let size = (size_ident, size_eq_token, size_expr_lit);
            let align = if input.peek(Token![,]) {
                let comma: Token![,] = input.parse()?;
                let align_ident: Ident = input.parse()?;
                if align_ident.to_string() != "align" {
                    return Err(input.error("expected `align`"));
                }
                let align_eq_token: Token![==] = input.parse()?;
                let align_expr_lit: ExprLit = input.parse()?;
                Some((comma, align_ident, align_eq_token, align_expr_lit))
            } else {
                None
            };
            Ok(GlobalLayout {
                layout_token,
                type_,
                is_token,
                size,
                align,
            })
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "parsing")))]
    impl Parse for GlobalInner {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(Token![size_of]) {
                Ok(GlobalInner::SizeOf(input.parse()?))
            } else if input.peek(Token![layout]) {
                Ok(GlobalInner::Layout(input.parse()?))
            } else {
                Err(input.error("expected `size_of` or `layout`"))
            }
        }
    }
}

#[cfg(feature = "printing")]
mod printing {
    use crate::expr::printing::outer_attrs_to_tokens;

    use super::*;
    use proc_macro2::TokenStream;
    use quote::ToTokens;

    impl ToTokens for Closed {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
        }
    }

    impl ToTokens for Open {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
        }
    }

    impl ToTokens for OpenRestricted {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.open_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.in_token.to_tokens(tokens);
                self.path.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeSpec {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.spec_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeGhost {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ghost_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeProof {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.proof_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ModeTracked {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.tracked_token.to_tokens(tokens);
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
    impl ToTokens for InvariantExceptBreak {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
            self.exprs.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Invariant {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
            self.exprs.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for InvariantEnsures {
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
    impl ToTokens for SignatureDecreases {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.decreases.to_tokens(tokens);
            if let Some((when_token, when)) = &self.via {
                when_token.to_tokens(tokens);
                when.to_tokens(tokens);
            }
            if let Some((via_token, via)) = &self.via {
                via_token.to_tokens(tokens);
                via.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for SignatureInvariants {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
            self.set.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for InvariantNameSetAny {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for InvariantNameSetNone {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for InvariantNameSetList {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.bracket_token.surround(tokens, |tokens| {
                self.exprs.to_tokens(tokens);
            });
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
                    self.requires.to_tokens(tokens);
                    self.body.to_tokens(tokens);
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
            self.or1_token.to_tokens(tokens);
            self.inputs.to_tokens(tokens);
            self.or2_token.to_tokens(tokens);
            self.expr.to_tokens(tokens);
            if let Some((implies, expr)) = &self.implies {
                implies.to_tokens(tokens);
                expr.to_tokens(tokens);
            }
            self.by_token.to_tokens(tokens);
            self.body.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for RevealHide {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            crate::expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            if let Some(reveal_token) = &self.reveal_token {
                reveal_token.to_tokens(tokens);
            }
            if let Some(reveal_with_fuel_token) = &self.reveal_with_fuel_token {
                reveal_with_fuel_token.to_tokens(tokens);
            }
            self.paren_token.surround(tokens, |tokens| {
                self.path.to_tokens(tokens);
                if let Some((comma_token, expr)) = &self.fuel {
                    comma_token.to_tokens(tokens);
                    expr.to_tokens(tokens);
                }
            });
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for BroadcastUse {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            crate::expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            let BroadcastUse {
                attrs: _,
                broadcast_use_tokens,
                paths,
                semi,
            } = self;
            broadcast_use_tokens.0.to_tokens(tokens);
            broadcast_use_tokens.1.to_tokens(tokens);
            paths.to_tokens(tokens);
            semi.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemBroadcastGroup {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            crate::expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            let ItemBroadcastGroup {
                attrs: _,
                vis,
                ident,
                broadcast_group_tokens,
                brace_token,
                paths,
            } = self;
            vis.to_tokens(tokens);
            broadcast_group_tokens.0.to_tokens(tokens);
            broadcast_group_tokens.1.to_tokens(tokens);
            ident.to_tokens(tokens);
            brace_token.surround(tokens, |tokens| {
                paths.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for View {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            crate::expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            self.expr.to_tokens(tokens);
            self.at_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeFnSpec {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.fn_spec_token.to_tokens(tokens);
            self.spec_fn_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.inputs.to_tokens(tokens);
            });
            self.output.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for BigAnd {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            for (prefix, expr) in &self.exprs {
                prefix.to_tokens(tokens);
                expr.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for BigOr {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            for (prefix, expr) in &self.exprs {
                prefix.to_tokens(tokens);
                expr.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprIs {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.base.to_tokens(tokens);
            self.is_token.to_tokens(tokens);
            self.variant_ident.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprHas {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.lhs.to_tokens(tokens);
            self.has_token.to_tokens(tokens);
            self.rhs.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for GlobalSizeOf {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.size_of_token.to_tokens(tokens);
            self.type_.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.expr_lit.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for GlobalLayout {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.layout_token.to_tokens(tokens);
            self.type_.to_tokens(tokens);
            self.is_token.to_tokens(tokens);
            self.size.0.to_tokens(tokens);
            self.size.1.to_tokens(tokens);
            self.size.2.to_tokens(tokens);
            if let Some(align) = &self.align {
                align.0.to_tokens(tokens);
                align.1.to_tokens(tokens);
                align.2.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for Global {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.global_token.to_tokens(tokens);
            self.inner.to_tokens(tokens);
            self.semi.to_tokens(tokens);
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprMatches {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.lhs.to_tokens(tokens);
            self.matches_token.to_tokens(tokens);
            self.pat.to_tokens(tokens);
            if let Some(MatchesOpExpr { op_token, rhs }) = &self.op_expr {
                match op_token {
                    MatchesOpToken::Implies(t) => t.to_tokens(tokens),
                    MatchesOpToken::AndAnd(t) => t.to_tokens(tokens),
                    MatchesOpToken::BigAnd => (),
                }
                rhs.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprGetField {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.base.to_tokens(tokens);
            self.arrow_token.to_tokens(tokens);
            self.member.to_tokens(tokens);
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
pub(crate) fn parse_matches(
    input: crate::parse::ParseStream,
    lhs: Expr,
    allow_struct: expr::parsing::AllowStruct,
    big_and: bool,
) -> Result<Expr> {
    let matches_token: Token![matches] = input.parse()?;
    let pat = input.parse()?;

    let op_expr = if input.peek(Token![&&&]) {
        if big_and {
            let attrs = input.call(expr::parsing::expr_attrs)?;
            let Some(rhs) = parse_prefix_binop(input, &attrs, true)? else {
                return Err(input.error("expected &&&"));
            };
            Some(MatchesOpExpr {
                op_token: MatchesOpToken::BigAnd,
                rhs: Box::new(rhs),
            })
        } else {
            return Err(input.error("in &&&, a matches expression needs to be prefixed with &&&"));
        }
    } else if input.peek(Token![==>]) || input.peek(Token![&&]) {
        let op_token = if input.peek(Token![==>]) {
            MatchesOpToken::Implies(input.parse()?)
        } else if input.peek(Token![&&]) {
            MatchesOpToken::AndAnd(input.parse()?)
        } else {
            unreachable!()
        };
        let mut rhs = expr::parsing::unary_expr(input, allow_struct)?;
        loop {
            let next = expr::parsing::peek_precedence(input);
            if matches!(op_token, MatchesOpToken::Implies(_))
                && next >= expr::parsing::Precedence::Imply
                || matches!(op_token, MatchesOpToken::AndAnd(_))
                    && next >= expr::parsing::Precedence::And
            {
                rhs = expr::parsing::parse_expr(input, rhs, allow_struct, next)?;
            } else {
                break;
            }
        }
        Some(MatchesOpExpr {
            op_token,
            rhs: Box::new(rhs),
        })
    } else {
        None
    };

    Ok(Expr::Matches(ExprMatches {
        attrs: Vec::new(),
        lhs: Box::new(lhs),
        matches_token,
        pat,
        op_expr,
    }))
}

#[cfg(feature = "full")]
pub(crate) fn parse_prefix_binop(
    input: crate::parse::ParseStream,
    attrs: &Vec<Attribute>,
    big_and_only: bool,
) -> Result<Option<Expr>> {
    use crate::expr::parsing::AllowStruct;

    if input.peek(Token![&&&]) {
        if attrs.len() != 0 {
            return Err(input.error("`&&&` cannot have attributes"));
        }
        let mut exprs: Vec<(Token![&&&], Box<Expr>)> = Vec::new();
        while let Ok(token) = input.parse() {
            let lhs = expr::parsing::unary_expr(input, AllowStruct(true))?;
            let expr: Expr = if input.peek(Token![matches]) {
                let attrs = input.call(expr::parsing::expr_attrs)?;
                let mut expr = parse_matches(input, lhs, AllowStruct(true), true)?;
                expr.replace_attrs(attrs);
                expr
            } else {
                expr::parsing::parse_expr(
                    input,
                    lhs,
                    AllowStruct(true),
                    expr::parsing::Precedence::Any,
                )?
            };

            exprs.push((token, Box::new(expr)));
        }
        Ok(Some(Expr::BigAnd(BigAnd { exprs })))
    } else if !big_and_only && input.peek(Token![|||]) {
        if attrs.len() != 0 {
            return Err(input.error("`|||` cannot have attributes"));
        }
        let mut exprs: Vec<(Token![|||], Box<Expr>)> = Vec::new();
        while let Ok(token) = input.parse() {
            let expr: Expr = input.parse()?;
            exprs.push((token, Box::new(expr)));
        }
        Ok(Some(Expr::BigOr(BigOr { exprs })))
    } else {
        Ok(None)
    }
}
