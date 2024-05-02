// Here, we modify each function item by appending rustdoc
// containing information about the Verus signature that we want to appear
// in auto-generated rustdoc. For example, we add information about
// 'requires' and 'ensures' clauses, and we also add 'mode' information.
// This information would be absent if we tried to run rustdoc without any
// processing.
//
// The flow is:
//  - the verus! macro (this file) adds extra information into a rustdoc comment
//  - rustdoc (unmodified) generates the rustdoc HTML
//  - we run a postprocessor (verusdoc crate) to present the information in a nice way.
//
// Specifically, we add "attributes" in a kinda-silly format that the post-processing
// step can recognize.  The format is:
//
//     ```rust
//     // verusdoc_special_attr $ATTR_NAME
//     $ATTR_VALUE
//     ```
//
// The ATTR_NAME can be requires, ensures, recommends or modes.
//
// The reason we use a codeblock here is that so rustdoc will perform syntax highlighting
// on the value which is applicable if it's an expression. For example, if it's a
// requires, ensures, or recommends attribute then ATTR_VALUE will be a (pretty-printed)
// boolean expression.
//
// The other type, 'modes', is a bit more complicated: the value is a JSON blob with
// some data explaining the function mode, param modes, and return mode.

use proc_macro2::Span;
use proc_macro2::TokenTree;
use std::iter::FromIterator;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::{
    AttrStyle, Attribute, Block, Expr, ExprBlock, FnMode, Ident, ImplItemMethod, ItemFn, Meta,
    MetaList, NestedMeta, Path, PathArguments, PathSegment, Publish, ReturnType, Signature,
    TraitItemMethod,
};

/// Check if VERUSDOC=1.

#[cfg(verus_keep_ghost)]
pub fn env_rustdoc() -> bool {
    match proc_macro::tracked_env::var("VERUSDOC") {
        Err(_) => false, // VERUSDOC key not present in environment
        Ok(s) => s == "1",
    }
}

#[cfg(not(verus_keep_ghost))]
pub fn env_rustdoc() -> bool {
    false
}

// Main hooks for the verus! macro to manipulate ItemFn, etc.

pub fn process_item_fn(item: &mut ItemFn) {
    match attr_for_sig(&mut item.attrs, &item.sig, Some(&item.block)) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

pub fn process_item_fn_broadcast_group(item: &mut ItemFn) {
    match attr_for_broadcast_group(&mut item.attrs, &item.sig) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

pub fn process_impl_item_method(item: &mut ImplItemMethod) {
    match attr_for_sig(&mut item.attrs, &item.sig, Some(&item.block)) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

pub fn process_trait_item_method(item: &mut TraitItemMethod) {
    match attr_for_sig(&mut item.attrs, &item.sig, item.default.as_ref()) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

/// Process a signature to get all the information, apply the codeblock
/// formatting tricks, and then package it all up into a #[doc = "..."] attribute
/// (as a syn_verus::Attribute object) that we can apply to the item.

fn attr_for_sig(
    attrs: &mut Vec<Attribute>,
    sig: &Signature,
    block: Option<&Block>,
) -> Option<Attribute> {
    let mut v = vec![];

    v.push(encoded_sig_info(sig));

    match &sig.requires {
        Some(es) => {
            for expr in es.exprs.exprs.iter() {
                v.push(encoded_expr("requires", expr));
            }
        }
        None => {}
    }
    match &sig.recommends {
        Some(es) => {
            for expr in es.exprs.exprs.iter() {
                v.push(encoded_expr("recommends", expr));
            }
        }
        None => {}
    }
    match &sig.ensures {
        Some(es) => {
            for expr in es.exprs.exprs.iter() {
                v.push(encoded_expr("ensures", expr));
            }
        }
        None => {}
    }

    match block {
        Some(block) => {
            if is_spec(&sig) {
                if show_body(attrs) {
                    let b =
                        Expr::Block(ExprBlock { attrs: vec![], label: None, block: block.clone() });
                    v.push(encoded_body("body", &b));
                }
            }
        }
        None => {}
    }

    if v.len() == 0 { None } else { Some(doc_attr_from_string(&v.join("\n\n"), sig.span())) }
}

fn attr_for_broadcast_group(_attrs: &mut Vec<Attribute>, sig: &Signature) -> Option<Attribute> {
    let mut v = vec![];

    v.push(encoded_str("broadcast_group", ""));

    if v.len() == 0 { None } else { Some(doc_attr_from_string(&v.join("\n\n"), sig.span())) }
}

fn is_spec(sig: &Signature) -> bool {
    match &sig.mode {
        FnMode::Spec(_) | FnMode::SpecChecked(_) => true,
        FnMode::Proof(_) | FnMode::Exec(_) | FnMode::Default => false,
    }
}

/// Check for:
///  #[doc(verus_show_body)]

fn show_body(attrs: &mut Vec<Attribute>) -> bool {
    for (i, attr) in attrs.iter().enumerate() {
        match attr.parse_meta() {
            Ok(Meta::List(MetaList { path, nested, .. })) => {
                if nested.len() == 1 && path.is_ident("doc") {
                    match nested.iter().next().unwrap() {
                        NestedMeta::Meta(Meta::Path(p)) => {
                            if p.is_ident("verus_show_body") {
                                // Remove the attribute; otherwise when rustdoc runs
                                // it will give an error about the unrecognized attribute.
                                attrs.remove(i);

                                return true;
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    false
}

fn fn_mode_to_string(mode: &FnMode, publish: &Publish) -> String {
    match mode {
        FnMode::Spec(_) | FnMode::SpecChecked(_) => match publish {
            Publish::Closed(_) => "closed spec".to_string(),
            Publish::Open(_) => "open spec".to_string(),
            Publish::OpenRestricted(res) => {
                "open(".to_string() + &module_path_to_string(&res.path) + ") spec"
            }
            Publish::Default => "spec".to_string(),
        },
        FnMode::Proof(_) => "proof".to_string(),
        FnMode::Exec(_) => "exec".to_string(),
        FnMode::Default => "exec".to_string(),
    }
}

fn module_path_to_string(p: &Path) -> String {
    // path is for a module; we can ignore type arguments

    let lead = if p.leading_colon.is_some() { "::" } else { "" };
    let main = p
        .segments
        .iter()
        .map(|path_seg| path_seg.ident.to_string())
        .collect::<Vec<String>>()
        .join("::");
    lead.to_string() + &main
}

fn encoded_sig_info(sig: &Signature) -> String {
    let fn_mode = fn_mode_to_string(&sig.mode, &sig.publish);
    let ret_mode = match &sig.output {
        ReturnType::Default => "Default",
        ReturnType::Type(_, tracked_token, _, _) => {
            if tracked_token.is_some() {
                "Tracked"
            } else {
                "Default"
            }
        }
    };

    let param_modes = sig
        .inputs
        .iter()
        .map(|fn_arg| if fn_arg.tracked.is_some() { "\"Tracked\"" } else { "\"Default\"" })
        .collect::<Vec<&str>>();
    let param_modes = param_modes.join(",");

    let broadcast = sig.broadcast.is_some();

    // JSON blob is parsed by the verusdoc post-processor into a `DocModeInfo` object.
    // I decided not to pull in serde as a dependency for builtin_macros,
    // but if serialization gets too complicated, we should probably do that instead.

    // We put it in a comment to avoid extra syntax highlighting or anything that would
    // complicate the post-processing.

    let info = format!(
        r#"// {{ "fn_mode": "{fn_mode:}", "ret_mode": "{ret_mode:}", "param_modes": [{param_modes:}], "broadcast": {broadcast:} }}"#
    );

    encoded_str("modes", &info)
}

/// Pretty print the expression, then wrap in a code block.

fn encoded_expr(kind: &str, code: &Expr) -> String {
    let s = prettyplease_verus::unparse_expr(&code);
    let s = format!("{s:},");
    encoded_str(kind, &s)
}

fn encoded_body(kind: &str, code: &Expr) -> String {
    let s = prettyplease_verus::unparse_expr(&code);
    let s = format!("{s:}");
    encoded_str(kind, &s)
}

/// Wrap the given string into a code block,
/// into the format that the postprocessor will recognize.

fn encoded_str(kind: &str, data: &str) -> String {
    "```rust\n// verusdoc_special_attr ".to_string() + kind + "\n" + data + "\n```"
}

/// Create an attr that looks like #[doc = "doc_str"]

fn doc_attr_from_string(doc_str: &str, span: Span) -> Attribute {
    Attribute {
        pound_token: token::Pound { spans: [span] },
        style: AttrStyle::Outer,
        bracket_token: token::Bracket { span },
        path: Path {
            leading_colon: None,
            segments: Punctuated::from_iter(vec![PathSegment {
                ident: Ident::new("doc", span),
                arguments: PathArguments::None,
            }]),
        },
        tokens: proc_macro2::TokenStream::from_iter(vec![
            TokenTree::Punct(proc_macro2::Punct::new('=', proc_macro2::Spacing::Alone)),
            TokenTree::Literal(proc_macro2::Literal::string(doc_str)),
        ]),
    }
}
