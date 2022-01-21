use regex::Regex;

pub const IS_VARIANT_PREFIX: &str = "is_";
pub const GET_VARIANT_PREFIX: &str = "get_";

/// Returns `Some((name, field))` if the ident matches the expected name for #[is_variant] functions
/// `name` is the variant name
/// `field` is `Some(num)` if this was a `.get_Variant_num()` function
/// `field` is `None` if this was a `.is_Variant` function
pub(crate) fn is_get_variant_fn_name(
    ident: &rustc_span::symbol::Ident,
) -> Option<(String, Option<usize>)> {
    let fn_name = ident.as_str();
    fn_name.strip_prefix(crate::def::IS_VARIANT_PREFIX).map(|n| (n.to_string(), None)).or_else(
        || {
            let re =
                Regex::new(&("^".to_string() + crate::def::GET_VARIANT_PREFIX + r"(.*)_(\d+)$"))
                    .unwrap();
            re.captures(&fn_name).and_then(|c| {
                c.get(2)
                    .unwrap()
                    .as_str()
                    .parse::<usize>()
                    .ok()
                    .map(|f| (c.get(1).unwrap().as_str().to_string(), Some(f)))
            })
        },
    )
}
