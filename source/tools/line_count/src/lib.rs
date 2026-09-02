use std::collections::BTreeSet;
use std::rc::Rc;

use verus_syn::File;
use verus_syn::Meta;
use verus_syn::MetaList;
use verus_syn::visit::Visit;

use self::attribution::CodeKind;
use self::attribution::LineContent;
use self::attribution::LineInfo;
use self::config::Config;
use self::stats::FileStats;
use self::syn_visitor::Visitor;

pub mod attribution;
pub mod config;
pub mod deps;
pub mod files;
pub mod stats;
pub mod syn_visitor;

pub fn cut_string(s: String, len: usize) -> String {
    s.chars().take(len).collect()
}

pub fn sorted_vec_to_fit_string<V: std::fmt::Debug>(h: &[V], len: usize) -> String {
    if h.len() != 0 {
        let each_len = (len / h.len()) - 1;
        h.iter().map(|x| cut_string(format!("{:?}", x), each_len)).collect::<Vec<_>>().join(" ")
    } else {
        "".into()
    }
}

pub fn btree_set_to_sorted_vec<V: Clone + Ord>(h: &BTreeSet<V>) -> Vec<V> {
    h.iter().cloned().collect()
}

pub fn process_file(config: Rc<Config>, input_path: &std::path::Path) -> Result<FileStats, String> {
    let file_content = std::fs::read_to_string(input_path)
        .map_err(|e| format!("cannot read {} ({})", input_path.display(), e))?;
    let file = verus_syn::parse_file(&file_content).map_err(|e| {
        dbg!(&e.span().start(), &e.span().end());
        format!("failed to parse file {}: {}", input_path.display(), e)
    })?;

    let mut file_stats = FileStats {
        lines: file_content
            .lines()
            .map(|x| LineInfo {
                kinds: BTreeSet::new(),
                path: Vec::new(),
                line_content: BTreeSet::new(),
                text: x.into(),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    };
    let mut visitor = Visitor {
        file_stats: &mut file_stats,
        in_body: None,
        trusted: 0,
        in_proof_directive: 0,
        inside_verus_macro_or_verify_or_consider: 0,
        in_state_machine_macro: 0,
        inside_line_count_ignore_or_external: 0,
        config: config.clone(),
    };
    for attr in file.attrs.iter() {
        match &attr.meta {
            Meta::Path(path) => {
                let mut path_iter = path.segments.iter();
                match (path_iter.next(), path_iter.next()) {
                    (Some(first), Some(second))
                        if first.ident == "verus" && second.ident == "trusted" =>
                    {
                        visitor.trusted += 1;
                    }
                    _ => {}
                }
            }
            Meta::List(MetaList { path, delimiter: _, tokens: _ }) => {
                let mut path_iter = path.segments.iter();
                match (path_iter.next(), path_iter.next()) {
                    (Some(first), None) if first.ident == "cfg_attr" => {
                        let nested = attr.parse_args_with(verus_syn::punctuated::Punctuated::<Meta, verus_syn::Token![,]>::parse_terminated)
                            .map_err(|e| {
                                dbg!(&e.span().start(), &e.span().end());
                                format!("failed to parse attribute: {} {:?}", e, e.span())
                            })?;
                        let mut nested_iter = nested.iter();
                        match (nested_iter.next(), nested_iter.next()) {
                            (Some(Meta::Path(first)), Some(Meta::Path(second)))
                                if first
                                    .segments
                                    .iter()
                                    .next()
                                    .as_ref()
                                    .map(|x| x.ident == "verus_keep_ghost")
                                    .unwrap_or(false) =>
                            {
                                let mut path_iter = second.segments.iter();
                                match (path_iter.next(), path_iter.next()) {
                                    (Some(first), Some(second))
                                        if first.ident == "verus" && second.ident == "trusted" =>
                                    {
                                        visitor.trusted += 1;
                                    }
                                    _ => {}
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => (),
                }
            }
            _ => (),
        }
    }
    for item in file.items.into_iter() {
        match item {
            verus_syn::Item::Macro(ref m) => {
                if m.mac.path.segments.last().map(|s| s.ident == "verus").unwrap_or(false) {
                    let source_toks = &m.mac.tokens;
                    let rejoined_toks = verus_syn::rejoin_tokens(source_toks.clone());
                    let macro_content: File = verus_syn::parse2(rejoined_toks).map_err(|e| {
                        dbg!(&e.span().start(), &e.span().end());
                        format!(
                            "failed to parse file {}: {} {:?}",
                            input_path.display(),
                            e,
                            e.span()
                        )
                    })?;
                    visitor.inside_verus_macro_or_verify_or_consider += 1;
                    visitor.visit_file(&macro_content);
                    visitor.inside_verus_macro_or_verify_or_consider -= 1;
                } else {
                    visitor.visit_item(&item);
                }
            }
            _ => {
                visitor.visit_item(&item);
            }
        }
    }
    let mut multiline_comment = 0;
    let mut kind_multiline_override = None;
    let override_re = regex::Regex::new(r"\$line_count\$(([A-Za-z,]*)(\$\{)?\$)|(\}\$)").unwrap();
    for line in file_stats.lines.iter_mut() {
        let trimmed = line.text.trim();
        let mut start_not_comment = (multiline_comment == 0).then(|| 0);
        let mut all_comment_indices = trimmed
            .match_indices("/*")
            .map(|(m, _)| (m, true))
            .chain(trimmed.match_indices("*/").map(|(m, _)| (m + 2, false)))
            .collect::<Vec<_>>();
        all_comment_indices.sort_by_key(|(m, _)| *m);
        let mut entirely_comment = true;
        let had_comment_start_end = all_comment_indices.len() > 0;
        for (i, s) in all_comment_indices {
            if !s {
                multiline_comment -= 1;
                if multiline_comment == 0 {
                    start_not_comment = Some(i);
                }
            } else {
                multiline_comment += 1;
                if multiline_comment == 1 {
                    if let Some(_) = start_not_comment
                        .take()
                        .map(|x| line.text[x..i].trim())
                        .filter(|x| x.is_empty())
                    {
                    } else {
                        entirely_comment = false;
                    }
                }
            }
        }
        let entirely_comment = entirely_comment && (multiline_comment > 0 || had_comment_start_end);
        if entirely_comment {
            line.line_content = BTreeSet::from([LineContent::Comment]);
            line.kinds = BTreeSet::from([CodeKind::Comment])
        }
        if trimmed.starts_with("//") {
            line.line_content = BTreeSet::from([LineContent::Comment]);
            line.kinds = BTreeSet::from([CodeKind::Comment])
        }
        if trimmed == "" {
            if !line.kinds.is_empty() {
                line.kinds = BTreeSet::from([CodeKind::Layout])
            }
        }
        if config.delimiters_are_layout
            && trimmed
                .chars()
                .all(|c| c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']')
        {
            if !line.kinds.is_empty() {
                line.kinds = BTreeSet::from([CodeKind::Layout])
            }
        }
        if config.proofs_arent_trusted {
            if (line.line_content.contains(&LineContent::Body(CodeKind::Proof))
                || line.line_content.contains(&LineContent::Signature(CodeKind::Proof)))
                && line.kinds == BTreeSet::from([CodeKind::Trusted])
            {
                if line.line_content.contains(&LineContent::FunctionSpec) {
                    line.kinds = BTreeSet::from([CodeKind::Spec]);
                } else {
                    line.kinds = BTreeSet::from([CodeKind::Proof]);
                }
            }
        }
        if let Some(captures) = override_re.captures(trimmed) {
            if captures.get(1).is_some() {
                let kinds_str = captures.get(2).unwrap().as_str();
                let kinds = if kinds_str != "" {
                    kinds_str
                        .split(',')
                        .map(|x| match x {
                            "Trusted" => CodeKind::Trusted,
                            "Spec" => CodeKind::Spec,
                            "Proof" => CodeKind::Proof,
                            "Exec" => CodeKind::Exec,
                            "Comment" => CodeKind::Comment,
                            "Layout" => CodeKind::Layout,
                            "Directives" => CodeKind::Directives,
                            "Definitions" => CodeKind::Definitions,
                            _ => panic!("unknown code kind {}", x),
                        })
                        .collect::<BTreeSet<_>>()
                } else {
                    BTreeSet::new()
                };
                if captures.get(3).is_some() {
                    kind_multiline_override = Some(kinds);
                } else {
                    line.kinds = kinds.clone();
                }
            }
            if captures.get(4).is_some() {
                kind_multiline_override = None;
            }
        }
        if let Some(kinds) = &kind_multiline_override {
            if line.kinds != BTreeSet::from([CodeKind::Comment])
                && line.kinds != BTreeSet::from([CodeKind::Layout])
                && line.kinds != BTreeSet::from([])
            {
                line.kinds = kinds.clone();
            }
        }
    }
    Ok(file_stats)
}
