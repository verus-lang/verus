use regex::Regex;

pub const IS_VARIANT_PREFIX: &str = "is_";
pub const GET_VARIANT_PREFIX: &str = "get_";

pub(crate) enum FieldName {
    Named(String),
    Unnamed(usize),
}

/// Returns `Some((name, field))` if the ident matches the expected name for #[is_variant] functions
/// `name` is the variant name
/// `field` is `Some(num)` if this was a `.get_Variant_num()` function
/// `field` is `None` if this was a `.is_Variant` function
pub(crate) fn is_get_variant_fn_name(
    ident: &rustc_span::symbol::Ident,
) -> Option<(String, Option<FieldName>)> {
    let fn_name = ident.as_str();
    fn_name.strip_prefix(crate::def::IS_VARIANT_PREFIX).map(|n| (n.to_string(), None)).or_else(
        || {
            let re =
                Regex::new(&("^".to_string() + crate::def::GET_VARIANT_PREFIX + r"(.+)_(.+)$"))
                    .unwrap();
            re.captures(&fn_name).map(|c| {
                let f_name = c.get(2).unwrap().as_str().to_string();
                let v_name = c.get(1).unwrap().as_str().to_string();

                (
                    v_name,
                    Some(match f_name.parse::<usize>().ok() {
                        Some(i) => FieldName::Unnamed(i),
                        None => FieldName::Named(f_name),
                    }),
                )
            })
        },
    )
}
