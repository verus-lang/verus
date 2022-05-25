use super::*;

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
