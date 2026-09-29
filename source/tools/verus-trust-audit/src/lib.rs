use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};

pub const MANIFEST_VERSION: u32 = 1;
pub const OMITTED: &str = "/* untrusted code omitted */";

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Trust {
    Untrusted,
    Trusted,
    TrustedSpec,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum NodeKind {
    Function,
    Module,
    Impl,
    Trait,
    Foreign,
    Other,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
pub struct SourceRange {
    pub file: String,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SourceFile {
    pub path: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Node {
    pub id: u64,
    pub parent: Option<u64>,
    pub name: String,
    pub kind: NodeKind,
    pub trust: Trust,
    pub range: SourceRange,
    pub body: Option<SourceRange>,
    pub from_expansion: bool,
    pub call_site: Option<SourceRange>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Manifest {
    pub format_version: u32,
    pub crate_name: String,
    pub root_trust: Trust,
    pub crate_attributes: Vec<SourceRange>, // Trust-related attributes, like #![verus::trusted]
    pub files: Vec<SourceFile>,
    pub nodes: Vec<Node>,
}

pub fn source_hash(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|byte| format!("{byte:02x}")).collect()
}

fn line_start(source: &str, pos: usize) -> usize {
    source[..pos].rfind('\n').map_or(0, |i| i + 1)
}

fn indentation_at(source: &str, pos: usize) -> &str {
    let start = line_start(source, pos);
    let whitespace =
        source[start..pos].bytes().take_while(|byte| matches!(byte, b' ' | b'\t')).count();
    &source[start..start + whitespace]
}

fn extend_leading_comments(source: &str, start: usize) -> usize {
    let mut current = line_start(source, start);
    let mut candidate = current;
    let mut saw_comment = false;
    while current > 0 {
        let previous_end = current - 1;
        let previous_start = line_start(source, previous_end);
        let line = source[previous_start..previous_end].trim();
        if line.starts_with("//") {
            candidate = previous_start;
            current = previous_start;
            saw_comment = true;
        } else if line.is_empty() && saw_comment {
            break;
        } else {
            break;
        }
    }
    candidate
}

fn brace_bounds(source: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    let bytes = source.as_bytes();
    let mut i = start;
    let mut depth = 0usize;
    let mut open = None;
    while i < end {
        match bytes[i] {
            b'/' if i + 1 < end && bytes[i + 1] == b'/' => {
                i += 2;
                while i < end && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if i + 1 < end && bytes[i + 1] == b'*' => {
                i += 2;
                while i + 1 < end && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(end);
            }
            b'"' | b'\'' => {
                let quote = bytes[i];
                i += 1;
                while i < end {
                    if bytes[i] == b'\\' {
                        i = (i + 2).min(end);
                    } else if bytes[i] == quote {
                        i += 1;
                        break;
                    } else {
                        i += 1;
                    }
                }
            }
            b'{' => {
                if open.is_none() {
                    open = Some(i);
                }
                depth += 1;
                i += 1;
            }
            b'}' if open.is_some() => {
                depth -= 1;
                if depth == 0 {
                    return Some((open.unwrap(), i));
                }
                i += 1;
            }
            _ => i += 1,
        }
    }
    None
}

struct Renderer<'a> {
    source: &'a str,
    nodes: &'a HashMap<u64, &'a Node>,
    children: &'a HashMap<Option<u64>, Vec<u64>>,
}

#[derive(Clone, Copy)]
struct VerusBlock {
    start: usize,
    open: usize,
    close: usize,
}

fn verus_blocks(source: &str) -> Vec<VerusBlock> {
    let bytes = source.as_bytes();
    let mut blocks = Vec::new();
    let mut i = 0;
    while i + 5 <= bytes.len() {
        if &bytes[i..i + 5] == b"verus" && (i == 0 || !(bytes[i - 1] as char).is_alphanumeric()) {
            let mut bang = i + 5;
            while bang < bytes.len() && bytes[bang].is_ascii_whitespace() {
                bang += 1;
            }
            if bang < bytes.len() && bytes[bang] == b'!' {
                let mut open = bang + 1;
                while open < bytes.len() && bytes[open].is_ascii_whitespace() {
                    open += 1;
                }
                if open < bytes.len()
                    && bytes[open] == b'{'
                    && let Some((_, close)) = brace_bounds(source, open, bytes.len())
                {
                    blocks.push(VerusBlock { start: i, open, close });
                    i = close + 1;
                    continue;
                }
            }
        }
        match bytes[i] {
            b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'/' => {
                i += 2;
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'*' => {
                i += 2;
                while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(bytes.len());
            }
            b'"' | b'\'' => {
                let quote = bytes[i];
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i = (i + 2).min(bytes.len());
                    } else if bytes[i] == quote {
                        i += 1;
                        break;
                    } else {
                        i += 1;
                    }
                }
            }
            _ => i += 1,
        }
    }
    blocks
}

impl<'a> Renderer<'a> {
    fn relevant(&self, id: u64) -> bool {
        let node = self.nodes[&id];
        node.trust != Trust::Untrusted
            || self
                .children
                .get(&Some(id))
                .is_some_and(|children| children.iter().any(|child| self.relevant(*child)))
    }

    fn render_children(&self, parent: Option<u64>) -> Result<String> {
        let Some(children) = self.children.get(&parent) else {
            return Ok(String::new());
        };
        let relevant: Vec<u64> =
            children.iter().copied().filter(|child| self.relevant(*child)).collect();
        let parent_bounds = parent.map(|id| {
            let node = self.nodes[&id];
            (node.range.start, node.range.end)
        });
        let blocks: Vec<VerusBlock> = verus_blocks(self.source)
            .into_iter()
            .filter(|block| {
                parent_bounds.is_none_or(|(start, end)| start <= block.start && block.close < end)
            })
            .collect();
        let mut block_children: BTreeMap<usize, Vec<u64>> = BTreeMap::new();
        let mut plain = Vec::new();
        for child in relevant {
            let node = self.nodes[&child];
            if let Some(block) = blocks
                .iter()
                .filter(|block| block.open < node.range.start && node.range.end <= block.close)
                .min_by_key(|block| block.close - block.open)
            {
                block_children.entry(block.start).or_default().push(child);
            } else {
                plain.push(child);
            }
        }
        enum Unit {
            Node(u64),
            Block(VerusBlock, Vec<u64>),
        }
        let mut units = Vec::new();
        for child in plain {
            units.push((self.nodes[&child].range.start, Unit::Node(child)));
        }
        for (start, children) in block_children {
            let block = blocks.iter().find(|block| block.start == start).unwrap();
            units.push((start, Unit::Block(*block, children)));
        }
        units.sort_by_key(|(start, _)| *start);

        let mut output = String::new();
        for (_, unit) in units {
            if !output.is_empty() {
                output.push_str("\n\n");
            }
            match unit {
                Unit::Node(child) => output.push_str(&self.render_node(child)?),
                Unit::Block(block, children) => {
                    let start = extend_leading_comments(self.source, block.start);
                    output.push_str(&self.source[start..=block.open]);
                    output.push('\n');
                    for (i, child) in children.into_iter().enumerate() {
                        if i > 0 {
                            output.push_str("\n\n");
                        }
                        output.push_str(&self.render_node(child)?);
                    }
                    output.push('\n');
                    output.push_str(&self.source[block.close..=block.close]);
                }
            }
        }
        Ok(output)
    }

    fn render_node(&self, id: u64) -> Result<String> {
        let node = self.nodes[&id];
        if node.from_expansion {
            bail!(
                "trusted item `{}` is generated by a macro; its expansion cannot yet be rendered",
                node.name
            );
        }
        let start = extend_leading_comments(self.source, node.range.start);
        match node.trust {
            Trust::TrustedSpec => {
                let body = node.body.as_ref().context("trusted(spec) function has no body span")?;
                let mut output = self.source[start..body.start].to_owned();
                let indent = indentation_at(self.source, body.start);
                output.push_str("{\n");
                output.push_str(indent);
                output.push_str("    ");
                output.push_str(OMITTED);
                output.push('\n');
                output.push_str(indent);
                output.push('}');
                Ok(output)
            }
            Trust::Trusted => {
                let children = self.children.get(&Some(id));
                if children.is_none() {
                    return Ok(self.source[start..node.range.end].to_owned());
                }
                let mut output = String::new();
                let mut cursor = start;
                for child in children.unwrap() {
                    let child_node = self.nodes[child];
                    if child_node.range.file != node.range.file {
                        continue;
                    }
                    let child_start = extend_leading_comments(self.source, child_node.range.start);
                    output.push_str(&self.source[cursor..child_start]);
                    if self.relevant(*child) {
                        output.push_str(&self.render_node(*child)?);
                    } else {
                        output.push_str(indentation_at(self.source, child_node.range.start));
                        output.push_str(OMITTED);
                    }
                    cursor = child_node.range.end;
                }
                output.push_str(&self.source[cursor..node.range.end]);
                Ok(output)
            }
            Trust::Untrusted => {
                let rendered = self.render_children(Some(id))?;
                if rendered.is_empty() {
                    return Ok(String::new());
                }
                if let Some((open, close)) =
                    brace_bounds(self.source, node.range.start, node.range.end)
                {
                    let mut output = self.source[start..=open].to_owned();
                    output.push('\n');
                    output.push_str(&rendered);
                    output.push('\n');
                    output.push_str(&self.source[close..node.range.end]);
                    Ok(output)
                } else {
                    Ok(rendered)
                }
            }
        }
    }
}

fn common_root(paths: &[PathBuf]) -> PathBuf {
    let Some(first) = paths.first() else {
        return PathBuf::new();
    };
    let mut root = first.parent().unwrap_or(Path::new("")).to_path_buf();
    while !paths.iter().all(|path| path.starts_with(&root)) {
        if !root.pop() {
            break;
        }
    }
    root
}

pub fn render_manifest(manifest_path: &Path, output_dir: &Path) -> Result<Vec<PathBuf>> {
    let manifest_bytes = fs::read(manifest_path)
        .with_context(|| format!("failed to read {}", manifest_path.display()))?;
    let manifest: Manifest = serde_json::from_slice(&manifest_bytes)
        .with_context(|| format!("failed to parse {}", manifest_path.display()))?;
    if manifest.format_version != MANIFEST_VERSION {
        bail!(
            "unsupported TCB manifest version {}, expected {}",
            manifest.format_version,
            MANIFEST_VERSION
        );
    }

    let paths: Vec<PathBuf> = manifest.files.iter().map(|f| PathBuf::from(&f.path)).collect();
    let root = common_root(&paths);
    let nodes: HashMap<u64, &Node> = manifest.nodes.iter().map(|node| (node.id, node)).collect();
    let mut by_file: BTreeMap<&str, Vec<&Node>> = BTreeMap::new();
    for node in &manifest.nodes {
        by_file.entry(&node.range.file).or_default().push(node);
    }

    let mut written = Vec::new();
    for file in &manifest.files {
        let source = fs::read_to_string(&file.path)
            .with_context(|| format!("failed to read source file {}", file.path))?;
        if source_hash(source.as_bytes()) != file.sha256 {
            bail!("source file changed since manifest generation: {}", file.path);
        }
        let file_nodes = by_file.get(file.path.as_str()).cloned().unwrap_or_default();
        let file_ids: std::collections::HashSet<u64> =
            file_nodes.iter().map(|node| node.id).collect();
        let mut children: HashMap<Option<u64>, Vec<u64>> = HashMap::new();
        for node in file_nodes {
            let parent = node.parent.filter(|parent| file_ids.contains(parent));
            children.entry(parent).or_default().push(node.id);
        }
        for ids in children.values_mut() {
            ids.sort_by_key(|id| nodes[id].range.start);
        }
        let renderer = Renderer { source: &source, nodes: &nodes, children: &children };
        let mut rendered = String::new();
        for range in manifest.crate_attributes.iter().filter(|range| range.file == file.path) {
            if !rendered.is_empty() {
                rendered.push('\n');
            }
            rendered.push_str(&source[range.start..range.end]);
        }
        let children = renderer.render_children(None)?;
        if !rendered.is_empty() && !children.is_empty() {
            rendered.push_str("\n\n");
        }
        rendered.push_str(&children);
        if rendered.is_empty() {
            continue;
        }
        let input_path = Path::new(&file.path);
        let relative = input_path.strip_prefix(&root).unwrap_or(input_path);
        let output_path = output_dir.join(relative);
        if let Some(parent) = output_path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&output_path, format!("{rendered}\n"))?;
        written.push(output_path);
    }
    Ok(written)
}
