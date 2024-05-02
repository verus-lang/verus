// HTML Postprocessor for verusdoc.
// The 'other half' to this mechanism is in builtin_macros/src/rustdoc.rs
// which has more high-level details.

use html5ever::{local_name, namespace_url, ns, QualName};
use kuchiki::traits::TendrilSink;
use kuchiki::NodeRef;
use serde::{Deserialize, Serialize};
use std::io::Write;
use std::path::Path;
use walkdir::WalkDir;

#[derive(Serialize, Deserialize)]
pub enum ParamMode {
    Tracked,
    Default,
}

#[derive(Serialize, Deserialize)]
pub struct DocSigInfo {
    pub fn_mode: String,
    pub ret_mode: ParamMode,
    pub param_modes: Vec<ParamMode>,
    pub broadcast: bool,
}

enum VerusDocAttr {
    ModeInfo(DocSigInfo),
    Specification(String, NodeRef),
    BroadcastGroup,
}

// Types of spec clauses we handle.
static SPEC_NAMES: [&str; 4] = ["requires", "ensures", "recommends", "body"];

fn main() {
    // Manipulate the auto-generated files in `doc/` to clean them up to make
    // the more presentable.

    // First modify the main .css file to add the CSS rules for the classes we're going to use

    write_css(Path::new("doc"));

    // Process every documentation HTML file in the directory.

    for entry in WalkDir::new("doc").into_iter().filter_map(|e| e.ok()) {
        if entry.path().extension().map(|s| s == "html").unwrap_or(false) {
            process_file(entry.path())
        }
    }
}

fn process_file(path: &Path) {
    let html = std::fs::read_to_string(path).expect("read file");

    if !html.contains("verusdoc_special_attr") {
        return;
    }

    let document = kuchiki::parse_html().one(html);

    // Rustdoc generates HTML for an ImplItem that looks like this:
    //
    //   <summary>signature here (fn foo(...) -> ...)</summary>
    //   <div class="docblock">
    //
    //     <div class="example-wrap">     // This encapsulates a single "verusdoc attribute"
    //       <pre class="rust rust-example-rendered">
    //         <code>
    //           <span class="comment">// verusdoc_special_attr modes</span>
    //           ... additional content here
    //         </code>
    //       </pre>
    //     </div>
    //
    //     ... possibly more blocks here
    //   </div>
    //
    // Our plan is:
    //
    //   1. Collect all <div class="docblock"> elements
    //
    //   2. Check for <pre> elements that use our special format.
    //      Parse the information inside and remove them.
    //
    //   3. For the 'modes' information, we parse the modes information, then annotate
    //      the signature line with the mode information
    //
    //   4. For the requires/ensures/reocmmends information, we collect the
    //      syntax-highlighted HTML and add that HTML back in a nicely-formatted way.

    for docblock_elem in document.select(".docblock").expect("code selector") {
        let docblock_elem: &NodeRef = docblock_elem.as_node();

        // Iterate over elements. For each one, check if it is a
        // verusdoc_special_attr block. If so, remove it.

        let mut child_opt = docblock_elem.first_child();
        let mut attrs: Vec<VerusDocAttr> = vec![];
        while child_opt.is_some() {
            let child = child_opt.unwrap();

            match interpret_as_verusdoc_attribute(&child) {
                None => {
                    child_opt = child.next_sibling();
                }
                Some(attr) => {
                    attrs.push(attr);
                    child_opt = child.next_sibling();
                    child.detach();
                }
            }
        }

        // Now add content based on the data we just collected.

        update_docblock(&docblock_elem, &attrs);
    }

    document.serialize_to_file(path).expect("serialize_to_file");
}

fn interpret_as_verusdoc_attribute(node: &NodeRef) -> Option<VerusDocAttr> {
    let pre_node = get_single_child(node)?;
    if !is_element(&pre_node, "pre") {
        return None;
    }

    let code_node = get_single_child(&pre_node)?;
    if !is_element(&code_node, "code") {
        return None;
    }

    let span_node = code_node.first_child()?;
    if !is_element(&span_node, "span") {
        return None;
    }

    let text_node = get_single_child(&span_node)?;
    let text_ref = text_node.as_text()?;
    let text: &String = &text_ref.borrow();

    let attr_data = text.strip_prefix("// verusdoc_special_attr ")?;
    let attr_name = attr_data.split_whitespace().next().unwrap();

    if attr_name == "modes" {
        let comment_idx = attr_data.find("// ").unwrap();
        let json_text = &attr_data[comment_idx + 3..];

        let doc_mode_info: DocSigInfo = serde_json::from_str(json_text).unwrap();

        Some(VerusDocAttr::ModeInfo(doc_mode_info))
    } else if SPEC_NAMES.contains(&attr_name) {
        span_node.detach();
        pre_node.detach();

        Some(VerusDocAttr::Specification(attr_name.to_string(), pre_node))
    } else if attr_name == "broadcast_group" {
        Some(VerusDocAttr::BroadcastGroup)
    } else {
        panic!("unrecognized attr_name: '{:}'", attr_name);
    }
}

/// If this node has a single child, return it. Otherwise, None.

fn get_single_child(node: &NodeRef) -> Option<NodeRef> {
    let child = node.first_child()?;
    if child.next_sibling().is_some() {
        return None;
    }
    Some(child)
}

/// Check if the node is an element with the given tag name

fn is_element(node: &NodeRef, name: &str) -> bool {
    match node.as_element() {
        None => false,
        Some(data) => data.name.local == name.to_string(),
    }
}

/// Returns node that looks like
///     <span class="verus-spec-keyword">requires</span>
/// (the inner text is given by `spec_name`

fn mk_spec_keyword_node(spec_name: &str) -> NodeRef {
    let t = NodeRef::new_text(spec_name);

    let qual_name = QualName::new(None, ns!(html), local_name!("span"));
    let nr = NodeRef::new_element(qual_name, vec![]);
    set_class_attribute(&nr, "verus-spec-keyword");
    nr.append(t);

    nr
}

/// <span class="verus-sig-keyword">{spec name}</span>

fn mk_sig_keyword_node(spec_name: &str) -> NodeRef {
    let t = NodeRef::new_text(spec_name);

    let qual_name = QualName::new(None, ns!(html), local_name!("span"));
    let nr = NodeRef::new_element(qual_name, vec![]);
    set_class_attribute(&nr, "verus-sig-keyword");
    nr.append(t);

    nr
}

/// <div class="verus-spec"></div>

fn mk_spec_node() -> NodeRef {
    let qual_name = QualName::new(None, ns!(html), local_name!("div"));
    let nr = NodeRef::new_element(qual_name, vec![]);
    set_class_attribute(&nr, "verus-spec");

    nr
}

fn set_class_attribute(nr: &NodeRef, value: &str) {
    let el = nr.as_element().unwrap();
    let mut attr_ref = el.attributes.borrow_mut();
    attr_ref.insert(local_name!("class"), value.to_string());
}

fn update_docblock(docblock_elem: &NodeRef, attrs: &Vec<VerusDocAttr>) {
    let mut elems: Vec<NodeRef> = vec![];

    // Add code that looks like
    // <div class="verus-spec">
    //   <span class="verus-spec-keyword">requires</span>
    //   <pre class="... verus-spec-code">...</pre>
    //   <span class="verus-spec-keyword">ensures</span>
    //   <pre class="... verus-spec-code">...</pre>
    // </div>

    if attrs.iter().find(|x| matches!(x, VerusDocAttr::BroadcastGroup)).is_some() {
        docblock_elem.append(mk_spec_keyword_node("broadcast group"));
    }

    for spec_name in SPEC_NAMES.iter() {
        let code_blocks: Vec<NodeRef> = attrs
            .iter()
            .filter_map(|a| match a {
                VerusDocAttr::Specification(s, nr) if s == spec_name => Some(nr.clone()),
                _ => None,
            })
            .collect();

        let is_body = spec_name == &"body";

        if code_blocks.len() > 0 && !is_body {
            elems.push(mk_spec_keyword_node(spec_name));
        }

        for code_block in code_blocks.into_iter() {
            if is_body {
                set_class_attribute(&code_block, "rust rest-example-rendered verus-body-code");
            } else {
                set_class_attribute(&code_block, "rust rest-example-rendered verus-spec-code");
            }
            elems.push(code_block);
        }
    }

    if elems.len() > 0 {
        let spec_node = mk_spec_node();
        for elem in elems.into_iter() {
            spec_node.append(elem);
        }
        docblock_elem.prepend(spec_node);
    }

    // Add mode info to the signature

    for attr in attrs.iter() {
        match attr {
            VerusDocAttr::ModeInfo(doc_mode_info) => {
                update_sig_info(docblock_elem, UpdateSigMode::DocSigInfo(doc_mode_info));
                break;
            }
            VerusDocAttr::BroadcastGroup => {
                update_sig_info(docblock_elem, UpdateSigMode::BroadcastGroup);
                break;
            }
            _ => {}
        }
    }
}

enum UpdateSigMode<'a> {
    DocSigInfo(&'a DocSigInfo),
    BroadcastGroup,
}

fn update_sig_info(docblock_elem: &NodeRef, info: UpdateSigMode<'_>) {
    // The signature is a dom tree with special formatting for syntax highlighting and such.
    // We first collect it as pure text, to get a string like
    //    pub fn foo<...>(...) -> ...
    // We identify the locations where content needs to be inserted,
    // collected all in the 'splices' vec.
    // Then we add the content.

    let mut summary = docblock_elem.previous_sibling().unwrap();

    if summary.text_contents() == "Expand description" {
        // This is applicable to pages devoted to a single fn not inside an impl
        let details = summary.parent().unwrap();
        summary = details.previous_sibling().unwrap();
    }

    let code_header = summary.select_first(".code-header");
    match code_header {
        Ok(ch) => {
            summary = ch.as_node().clone();
        }
        Err(_) => {
            let code_block = summary.select_first("code");
            match code_block {
                Ok(cb) => {
                    summary = cb.as_node().clone();
                }
                Err(_) => {}
            }
        }
    }

    let full_text = summary.text_contents();

    let mut splices: Vec<(usize, String)> = vec![];

    let fn_idx = if let Some(fn_idx) = full_text.find("fn") {
        fn_idx
    } else {
        return;
    };

    match info {
        UpdateSigMode::DocSigInfo(info) => {
            // TODO: separate these if possible
            let broadcast = if info.broadcast { "broadcast ".to_owned() } else { "".to_owned() };
            let fn_mode = format!("{:} ", info.fn_mode);
            splices.push((fn_idx, broadcast + &fn_mode));

            let arg0_idx = get_arg0_idx(&full_text, fn_idx);

            let mut arg_idx = arg0_idx;

            for i in 0..info.param_modes.len() {
                match info.param_modes[i] {
                    ParamMode::Default => {}
                    ParamMode::Tracked => {
                        splices.push((arg_idx, "tracked ".to_string()));
                    }
                }

                arg_idx = next_comma_or_rparen(&full_text, arg_idx);

                // skip of the comma and space
                arg_idx += 2;
            }

            match info.ret_mode {
                ParamMode::Default => {}
                ParamMode::Tracked => {
                    let arrow_idx = full_text[arg_idx..].find("->").unwrap() + arg_idx;
                    let type_idx = arrow_idx + 3;
                    splices.push((type_idx, "tracked ".to_string()));
                }
            }
        }
        UpdateSigMode::BroadcastGroup => {
            splices.push((fn_idx, "broadcast group ".to_owned()));
        }
    }

    // Reverse order since inserting text should invalidate later indices
    for (idx, s) in splices.into_iter().rev() {
        let mut idx = idx;
        let new_node = mk_sig_keyword_node(&s);
        do_text_splice(&summary, &new_node, &mut idx, true);
    }
}

// traverse a dom tree, counting characters, to insert the given node at the right spot
fn do_text_splice(elem: &NodeRef, inserted: &NodeRef, idx: &mut usize, root: bool) -> bool {
    match elem.as_text() {
        Some(text_ref) => {
            let t: &mut String = &mut text_ref.borrow_mut();

            if *idx == 0 {
                elem.insert_before(inserted.clone());
                true
            } else if *idx == t.len() && root {
                elem.insert_after(inserted.clone());
                true
            } else if *idx < t.len() {
                let second_text_node = NodeRef::new_text(&t[*idx..]);
                *t = t[..*idx].to_string();
                elem.insert_after(second_text_node);
                elem.insert_after(inserted.clone());
                true
            } else {
                *idx -= t.len();
                false
            }
        }
        None => {
            if *idx == 0 {
                elem.prepend(inserted.clone());
                return true;
            }

            let mut child_opt = elem.first_child();
            while let Some(c) = child_opt {
                let done = do_text_splice(&c, inserted, idx, false);
                if done {
                    return true;
                }

                child_opt = c.next_sibling();

                if *idx == 0 && (child_opt.is_some() || root) {
                    c.append(inserted.clone());
                    return true;
                }
            }

            false
        }
    }
}

fn get_arg0_idx(s: &str, i: usize) -> usize {
    let s: &[u8] = s.as_bytes();

    let mut depth: usize = 0;
    let mut i = i;
    loop {
        if depth == 0 && s[i] == b'(' {
            return i + 1;
        } else if s[i] == b'(' || s[i] == b'[' || s[i] == b'{' || s[i] == b'<' {
            depth += 1;
        } else if s[i] == b')' || s[i] == b']' || s[i] == b'}' || (s[i] == b'>' && s[i - 1] != b'-')
        {
            depth -= 1;
        }

        i += 1;
    }
}

fn next_comma_or_rparen(s: &str, i: usize) -> usize {
    let s: &[u8] = s.as_bytes();

    let mut depth: usize = 0;
    let mut i = i;
    loop {
        if s[i] == b'(' || s[i] == b'[' || s[i] == b'{' || s[i] == b'<' {
            depth += 1;
        } else if depth == 0 && (s[i] == b',' || s[i] == b')') {
            return i;
        } else if s[i] == b')' || s[i] == b']' || s[i] == b'}' || (s[i] == b'>' && s[i - 1] != b'-')
        {
            depth -= 1;
        }

        i += 1;
    }
}

fn write_css(dir_path: &Path) {
    let css_dir = dir_path.join("static.files");

    let mut rustdoc_css_path = None;

    for dir_entry in std::fs::read_dir(css_dir).unwrap() {
        let path = dir_entry.unwrap().path();
        if let Some(filename_os) = path.file_name() {
            if let Some(filename) = filename_os.to_str() {
                if filename.starts_with("rustdoc-") {
                    rustdoc_css_path = Some(path);
                }
            }
        }
    }

    let rustdoc_css_path = rustdoc_css_path.unwrap();

    let mut rustdoc_css =
        std::fs::OpenOptions::new().write(true).append(true).open(rustdoc_css_path).unwrap();
    rustdoc_css
        .write_all(
            r#"
.verus-spec-code {
  padding: 0px !important;
  margin: 0px;
  font-size: 14px;
}

pre.verus-spec-code {
  margin-left: 40px !important;
}

.verus-body-code {
  padding: 0px !important;
  margin: 0px;
  font-size: 14px;
}

pre.verus-body-code {
  margin-left: 8px !important;
}

.verus-spec-keyword {
  font-family: "Source Code Pro", monospace;
  color: #006400;
  font-size: 14px;
}

.verus-sig-keyword {
  font-family: "Source Code Pro", monospace;
  color: #006400;
}

.verus-spec {
    margin-top: -8px;
    padding-bottom: 18px;
    margin-left: 16px;
}

:root[data-theme="dark"] .verus-body-code { background-color: #353535 !important; }
:root[data-theme="dark"] .verus-spec-code { background-color: #353535 !important; }
:root[data-theme="dark"] .verus-body-code code { background-color: #353535 !important; }
:root[data-theme="dark"] .verus-spec-code code { background-color: #353535 !important; }

:root[data-theme="ayu"] .verus-body-code { background-color: #0f1419 !important; }
:root[data-theme="ayu"] .verus-spec-code { background-color: #0f1419 !important; }
:root[data-theme="ayu"] .verus-body-code code { background-color: #0f1419 !important; }
:root[data-theme="ayu"] .verus-spec-code code { background-color: #0f1419 !important; }

:root[data-theme="light"] .verus-body-code { background-color: #ffffff !important; }
:root[data-theme="light"] .verus-spec-code { background-color: #ffffff !important; }
:root[data-theme="light"] .verus-body-code code { background-color: #ffffff !important; }
:root[data-theme="light"] .verus-spec-code code { background-color: #ffffff !important; }
"#
            .as_bytes(),
        )
        .expect("write css file");
}
