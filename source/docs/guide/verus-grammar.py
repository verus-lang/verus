#!/usr/bin/env python3
"""
mdBook preprocessor for Verus grammar styling.

In verus-grammar fenced code blocks and in regular prose (but NOT in other
fenced code blocks or inline code spans), transforms:
  V@[text]  ->  <span style="color: #000080; font-style: italic">text</span>
  R@[text]  ->  <span style="color: #800000; font-style: italic">text</span>

In verus-grammar blocks, V@[name] on the LHS of ::= gets id="grammar-name"
so it can serve as a link target. All other V@[name] references become
hyperlinks to the page+anchor where that item is defined (if known).

verus-grammar fenced blocks are also converted to:
  <pre class="verus-grammar"><code>...</code></pre>
"""

import html
import json
import os
import re
import sys

# Matches fenced code blocks (``` or ~~~).
FENCED_BLOCK_RE = re.compile(
    r'^(?P<fence>`{3,}|~{3,})(?P<info>[^\n]*)\n(?P<body>.*?)^(?P=fence)[ \t]*\n?',
    re.MULTILINE | re.DOTALL,
)

INLINE_CODE_RE = re.compile(r'`+[^`\n]*`+')

# Matches a grammar definition: V@[name] optionally followed by whitespace then ::=
DEFINITION_RE = re.compile(r'V@\[([^\]]*)\](\s*::=)')
V_AT_RE = re.compile(r'V@\[([^\]]*)\]')
R_AT_RE = re.compile(r'R@\[([^\]]*)\]')

V_COLOR = '#000080'
R_COLOR = '#800000'


def v_span(name, anchor=None):
    if anchor:
        return (f'<span id="{anchor}" style="color: {V_COLOR}; '
                f'font-style: italic">{name}</span>')
    return f'<span style="color: {V_COLOR}; font-style: italic">{name}</span>'


def r_span(name):
    return f'<span style="color: {R_COLOR}; font-style: italic">{name}</span>'


def compute_relative_link(from_path, to_path):
    """Return a relative .html link from one chapter path to another."""
    from_dir = os.path.dirname(from_path) if from_path else ''
    rel = os.path.relpath(to_path, from_dir) if from_dir else to_path
    return os.path.splitext(rel)[0] + '.html'


def collect_definitions(book):
    """
    First pass: scan every verus-grammar block and return a dict mapping
    grammar item name -> chapter path for the first definition found.
    """
    definitions = {}

    def scan(content, path):
        for m in FENCED_BLOCK_RE.finditer(content):
            if m.group('info').strip() == 'verus-grammar':
                for dm in DEFINITION_RE.finditer(m.group('body')):
                    name = dm.group(1)
                    if name not in definitions:
                        definitions[name] = path

    def walk(item):
        if 'Chapter' in item:
            chapter = item['Chapter']
            path = chapter.get('path') or ''
            if path:
                scan(chapter['content'], path)
            for sub in chapter.get('sub_items', []):
                walk(sub)

    for section in book.get('sections', []):
        walk(section)
    return definitions


def transform_block_body(body, current_path, definitions):
    """Transform the body of a verus-grammar fenced block."""
    body = html.escape(body)

    # Definitions: V@[name] ::=  →  <span id="grammar-name">name</span> ::=
    def replace_definition(m):
        name, rest = m.group(1), m.group(2)
        return v_span(name, anchor=f'grammar-{name}') + rest

    # References: V@[name]  →  linked span (or plain span if not in map)
    def replace_v_ref(m):
        name = m.group(1)
        span = v_span(name)
        if name in definitions:
            target = definitions[name]
            rel = compute_relative_link(current_path, target)
            return f'<a href="{rel}#grammar-{name}">{span}</a>'
        return span

    body = DEFINITION_RE.sub(replace_definition, body)
    body = V_AT_RE.sub(replace_v_ref, body)
    body = R_AT_RE.sub(lambda m: r_span(m.group(1)), body)
    body = body.replace('?', '<sup>?</sup>')
    return body


def transform_prose_segment(text, current_path, definitions):
    """Apply V@/R@ transforms to a prose segment (outside inline code)."""
    def replace_v(m):
        name = m.group(1)
        span = f'<code>{v_span(name)}</code>'
        if name in definitions:
            target = definitions[name]
            rel = compute_relative_link(current_path, target)
            return f'<a href="{rel}#grammar-{name}">{span}</a>'
        return span

    text = V_AT_RE.sub(replace_v, text)
    text = R_AT_RE.sub(lambda m: f'<code>{r_span(m.group(1))}</code>', text)
    return text


def transform_prose(text, current_path, definitions):
    """Apply V@/R@ transforms to prose, skipping inline code spans."""
    result = []
    last_end = 0
    for m in INLINE_CODE_RE.finditer(text):
        result.append(transform_prose_segment(text[last_end:m.start()], current_path, definitions))
        result.append(m.group(0))
        last_end = m.end()
    result.append(transform_prose_segment(text[last_end:], current_path, definitions))
    return ''.join(result)


def transform_content(content, current_path, definitions):
    result = []
    last_end = 0
    for m in FENCED_BLOCK_RE.finditer(content):
        result.append(transform_prose(content[last_end:m.start()], current_path, definitions))
        info = m.group('info').strip()
        body = m.group('body')
        if info == 'verus-grammar':
            transformed = transform_block_body(body, current_path, definitions)
            result.append(f'<pre class="verus-grammar"><code>{transformed}</code></pre>\n')
        else:
            result.append(m.group(0))
        last_end = m.end()
    result.append(transform_prose(content[last_end:], current_path, definitions))
    return ''.join(result)


def walk_item(item, definitions):
    if 'Chapter' in item:
        chapter = item['Chapter']
        path = chapter.get('path') or ''
        chapter['content'] = transform_content(chapter['content'], path, definitions)
        for sub in chapter.get('sub_items', []):
            walk_item(sub, definitions)


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == 'supports':
        renderer = sys.argv[2] if len(sys.argv) >= 3 else ''
        sys.exit(0 if renderer == 'html' else 1)

    _context, book = json.load(sys.stdin)
    definitions = collect_definitions(book)
    for section in book.get('sections', []):
        walk_item(section, definitions)
    print(json.dumps(book))


if __name__ == '__main__':
    main()
