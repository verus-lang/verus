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
use std::iter::FromIterator;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::{
    AssumeSpecification, AttrStyle, Attribute, Block, Expr, ExprBlock, ExprPath, FnMode, Ident,
    ImplItemFn, ItemFn, Pat, PatIdent, Path, PathArguments, PathSegment, Publish, QSelf,
    ReturnType, Signature, TraitItemFn, Type, TypeGroup, TypePath,
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
    match attr_for_sig(&item.sig, Some(&item.block), None) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

pub fn process_item_fn_assume_specification(item: &mut ItemFn, as_spec: &AssumeSpecification) {
    match attr_for_sig(&item.sig, Some(&item.block), Some(as_spec)) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

pub fn process_item_fn_broadcast_group(item: &mut ItemFn) {
    match attr_for_broadcast_group(&item.sig) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

pub fn process_impl_item_method(item: &mut ImplItemFn) {
    match attr_for_sig(&item.sig, Some(&item.block), None) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

pub fn process_trait_item_method(item: &mut TraitItemFn) {
    match attr_for_sig(&item.sig, item.default.as_ref(), None) {
        Some(attr) => item.attrs.insert(0, attr),
        None => {}
    }
}

/// Process a signature to get all the information, apply the codeblock
/// formatting tricks, and then package it all up into a #[doc = "..."] attribute
/// (as a syn_verus::Attribute object) that we can apply to the item.

fn attr_for_sig(
    sig: &Signature,
    block: Option<&Block>,
    as_spec: Option<&AssumeSpecification>,
) -> Option<Attribute> {
    let mut v = vec![];

    v.push(encoded_sig_info(sig));

    match &sig.spec.requires {
        Some(es) => {
            for expr in es.exprs.exprs.iter() {
                v.push(encoded_expr("requires", expr));
            }
        }
        None => {}
    }
    match &sig.spec.recommends {
        Some(es) => {
            for expr in es.exprs.exprs.iter() {
                v.push(encoded_expr("recommends", expr));
            }
        }
        None => {}
    }
    match &sig.spec.ensures {
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
                if show_body(sig) {
                    let b =
                        Expr::Block(ExprBlock { attrs: vec![], label: None, block: block.clone() });
                    v.push(encoded_body("body", &b));
                }
            }
        }
        None => {}
    }

    if let Some(as_spec) = as_spec {
        let e = Expr::Path(ExprPath {
            attrs: vec![],
            qself: as_spec.qself.clone(),
            path: as_spec.path.clone(),
        });
        v.push(encoded_expr("assume_specification", &e));
        v.push(assume_specification_link_line(&e));
    }

    if v.len() == 0 { None } else { Some(doc_attr_from_string(&v.join("\n\n"), sig.span())) }
}

fn attr_for_broadcast_group(sig: &Signature) -> Option<Attribute> {
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

/// Do we want to show the body for the given spec function?
/// If it's 'open', then yes

fn show_body(sig: &Signature) -> bool {
    matches!(sig.publish, Publish::Open(_))
}

fn fn_mode_to_string(mode: &FnMode, publish: &Publish) -> String {
    match mode {
        FnMode::Spec(_) | FnMode::SpecChecked(_) => match publish {
            Publish::Closed(_) => "closed spec".to_string(),
            Publish::Open(_) => "open spec".to_string(),
            Publish::OpenRestricted(res) => {
                "open(".to_string() + &module_path_to_string(&res.path) + ") spec"
            }
            Publish::Uninterp(_) => "uninterp".to_string(),
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
    let (ret_mode, ret_name) = match &sig.output {
        ReturnType::Default => ("Default", "".to_string()),
        ReturnType::Type(_, tracked_token, opt_name, _) => {
            let mode = if tracked_token.is_some() { "Tracked" } else { "Default" };

            let name = match opt_name {
                None => "".to_string(),
                Some(b) => match &b.1 {
                    Pat::Ident(PatIdent { ident, .. }) => ident.to_string(),
                    _ => "".to_string(),
                },
            };

            (mode, name)
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
        r#"// {{ "fn_mode": "{fn_mode:}", "ret_mode": "{ret_mode:}", "param_modes": [{param_modes:}], "broadcast": {broadcast:}, "ret_name": "{ret_name:}" }}"#
    );

    encoded_str("modes", &info)
}

/// Get the assume_specification line

fn assume_specification_link_line(e: &Expr) -> String {
    // Change `<A>::B` to `A::B` if it's reasonable to do so, so the link is more likely to work
    let mut e = e.clone();
    match &e {
        Expr::Path(ExprPath {
            attrs,
            qself: Some(QSelf { lt_token: _, ty, position: 0, as_token: None, gt_token: _ }),
            path: Path { leading_colon: Some(leading_colon), segments },
        }) => {
            let mut ty = ty;
            if let Type::Group(TypeGroup { group_token: _, elem }) = &**ty {
                ty = elem;
            }
            if let Type::Path(TypePath { qself: None, path: inner_path }) = &**ty {
                if !inner_path.segments.trailing_punct() && !segments.trailing_punct() {
                    let mut new_path = inner_path.clone();
                    new_path.segments.push_punct(leading_colon.clone());
                    for (i, value) in segments.iter().enumerate() {
                        new_path.segments.push_value(value.clone());
                        if i + 1 < segments.len() {
                            new_path.segments.push_punct(leading_colon.clone());
                        }
                    }
                    e = Expr::Path(ExprPath { attrs: attrs.clone(), qself: None, path: new_path });
                }
            }
        }
        _ => {}
    }

    let s = prettyplease_verus::unparse_expr(&e);
    let s = s.replace("\n", " ");
    format!("**Specification for [`{:}`]**", s)
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
    let path = Path {
        leading_colon: None,
        segments: Punctuated::from_iter(vec![PathSegment {
            ident: Ident::new("doc", span),
            arguments: PathArguments::None,
        }]),
    };
    let lit = syn_verus::Lit::Str(syn_verus::LitStr::new(doc_str, span));
    let name_value = syn_verus::MetaNameValue {
        path,
        eq_token: token::Eq { spans: [span] },
        value: Expr::Lit(syn_verus::ExprLit { attrs: vec![], lit }),
    };
    Attribute {
        pound_token: token::Pound { spans: [span] },
        style: AttrStyle::Outer,
        bracket_token: token::Bracket { span: crate::syntax::into_spans(span) },
        meta: syn_verus::Meta::NameValue(name_value),
    }
}
