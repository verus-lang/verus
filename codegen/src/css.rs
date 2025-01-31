use crate::workspace_path;
use anyhow::Result;
use indoc::{formatdoc, indoc};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fs;
use syn_codegen::Definitions;

pub fn generate(defs: &Definitions) -> Result<()> {
    let mut styles = String::new();
    for ty in defs.tokens.keys() {
        styles += &format!("a.struct[title=\"struct syn::token::{ty}\"],\n");
    }
    styles.truncate(styles.len() - 2);
    styles += indoc! {"
         {
        \tdisplay: inline-block;
        \tcolor: transparent;
        \twhite-space: nowrap;
        }
    "};
    styles.push('\n');
    for ty in defs.tokens.keys() {
        styles += &format!("a.struct[title=\"struct syn::token::{ty}\"]::before,\n");
    }
    styles.truncate(styles.len() - 2);
    styles += indoc! {"
         {
        \tdisplay: inline-block;
        \tcolor: var(--type-link-color);
        \twidth: 0;
        }
    "};
    let mut shrink = BTreeMap::new();
    let mut grow = BTreeMap::new();
    for (ty, repr) in &defs.tokens {
        let macro_len = "Token![]".len() + repr.len();
        let ty_len = ty.len();
        styles.push('\n');
        styles += &match Ord::cmp(&macro_len, &ty_len) {
            Ordering::Less => {
                shrink
                    .entry((macro_len, ty_len))
                    .or_insert_with(Vec::new)
                    .push(ty);
                formatdoc! {"
                    a.struct[title=\"struct syn::token::{ty}\"]::before {{
                    \tcontent: \"Token![{repr}]\";
                    \tfont-size: calc(100% * {ty_len} / {macro_len});
                    }}
                "}
            }
            Ordering::Equal => unreachable!(),
            Ordering::Greater => {
                let padding = macro_len.saturating_sub(ty.len());
                grow.entry(padding).or_insert_with(Vec::new).push(ty);
                formatdoc! {"
                    a.struct[title=\"struct syn::token::{ty}\"]::before {{
                    \tcontent: \"Token![{repr}]\";
                    }}
                "}
            }
        };
    }
    for ((macro_len, ty_len), types) in shrink {
        for ty in types {
            styles += &format!("\na.struct[title=\"struct syn::token::{ty}\"],");
        }
        styles.truncate(styles.len() - 1);
        styles += &formatdoc! {"
             {{
            \tfont-size: calc(100% * {macro_len} / {ty_len});
            }}
        "};
    }
    for (padding, types) in grow {
        for ty in types {
            styles += &format!("\na.struct[title=\"struct syn::token::{ty}\"]::after,");
        }
        styles.truncate(styles.len() - 1);
        let padding = ".".repeat(padding);
        styles += &formatdoc! {"
             {{
            \tcontent: \"{padding}\";
            }}
        "};
    }

    let css_path = workspace_path::get("src/gen/token.css");
    fs::write(css_path, styles)?;
    Ok(())
}
