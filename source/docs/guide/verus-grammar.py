#!/usr/bin/env python3
"""
mdBook preprocessor for Verus grammar styling.

In verus-grammar fenced code blocks and in regular prose (but NOT in other
fenced code blocks or inline code spans), transforms:
  V@[text]  ->  <span style="color: #000080; font-style: italic">text</span>
  R@[text]  ->  <span style="color: #800000; font-style: italic">text</span>

verus-grammar fenced blocks are also converted to:
  <pre class="verus-grammar"><code>...</code></pre>
"""

import html
import json
import re
import sys

# Used inside verus-grammar blocks (already in <pre><code> context).
BLOCK_TRANSFORMS = [
    (re.compile(r'V@\[([^\]]*)\]'),
     r'<span style="color: #000080; font-style: italic">\1</span>'),
    (re.compile(r'R@\[([^\]]*)\]'),
     r'<span style="color: #800000; font-style: italic">\1</span>'),
]

# Used in prose — adds a <code> wrapper for monospace font.
PROSE_TRANSFORMS = [
    (re.compile(r'V@\[([^\]]*)\]'),
     r'<code><span style="color: #000080; font-style: italic">\1</span></code>'),
    (re.compile(r'R@\[([^\]]*)\]'),
     r'<code><span style="color: #800000; font-style: italic">\1</span></code>'),
]

# Matches fenced code blocks (``` or ~~~). The closing fence must use the
# same fence character sequence as the opening (via back-reference).
FENCED_BLOCK_RE = re.compile(
    r'^(?P<fence>`{3,}|~{3,})(?P<info>[^\n]*)\n(?P<body>.*?)^(?P=fence)[ \t]*\n?',
    re.MULTILINE | re.DOTALL,
)

# Matches inline code spans (simplified: same-delimiter open and close).
INLINE_CODE_RE = re.compile(r'`+[^`\n]*`+')


def apply_transforms(text, transforms):
    for pattern, replacement in transforms:
        text = pattern.sub(replacement, text)
    return text


def transform_prose(text):
    """Apply V@/R@ transforms to prose, skipping inline code spans."""
    result = []
    last_end = 0
    for m in INLINE_CODE_RE.finditer(text):
        result.append(apply_transforms(text[last_end:m.start()], PROSE_TRANSFORMS))
        result.append(m.group(0))
        last_end = m.end()
    result.append(apply_transforms(text[last_end:], PROSE_TRANSFORMS))
    return ''.join(result)


def transform_content(content):
    result = []
    last_end = 0

    for m in FENCED_BLOCK_RE.finditer(content):
        # Transform the prose segment before this fenced block.
        result.append(transform_prose(content[last_end:m.start()]))

        info = m.group('info').strip()
        body = m.group('body')

        if info == 'verus-grammar':
            # HTML-escape first so the raw body text is safe, then apply
            # transforms to inject the <span> markup, then superscript '?'.
            transformed = apply_transforms(html.escape(body), BLOCK_TRANSFORMS)
            transformed = transformed.replace('?', '<sup>?</sup>')
            result.append(f'<pre class="verus-grammar"><code>{transformed}</code></pre>\n')
        else:
            # Leave all other fenced blocks entirely untouched.
            result.append(m.group(0))

        last_end = m.end()

    # Transform any trailing prose after the last fenced block.
    result.append(transform_prose(content[last_end:]))
    return ''.join(result)


def walk_item(item):
    if 'Chapter' in item:
        chapter = item['Chapter']
        chapter['content'] = transform_content(chapter['content'])
        for sub_item in chapter.get('sub_items', []):
            walk_item(sub_item)


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == 'supports':
        renderer = sys.argv[2] if len(sys.argv) >= 3 else ''
        sys.exit(0 if renderer == 'html' else 1)

    _context, book = json.load(sys.stdin)
    for section in book.get('sections', []):
        walk_item(section)
    print(json.dumps(book))


if __name__ == '__main__':
    main()
