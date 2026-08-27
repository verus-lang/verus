#!/usr/bin/env python3
"""
mdBook preprocessor for custom admonitions
"""

import json
import sys

# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

SVG_DATA = None
def svg():
    global SVG_DATA
    if SVG_DATA == None:
        with open("src/graphics/verus-rust.svg") as f:
            c = f.read()
        SVG_DATA = ''.join(c.split('\n')[2:])
    return SVG_DATA

def transform_content(content):
    lines = content.split('\n')
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("> [!DIFF]"):
            out.append('<blockquote class="blockquote-tag blockquote-tag-caution">')
            out.append('<p class="blockquote-tag-title">' + svg() + 'Verus/Rust difference</p>')
            i = i + 1
            while True:
                if lines[i].startswith(">"):
                    line = lines[i][1:]
                    if line.strip() == '':
                        # blank line
                        i = i + 1
                    else:
                        out.append('')
                        out.append(line)
                        i = i + 1
                        while True:
                            if lines[i].strip() == '':
                                out.append('')
                                break
                            elif lines[i].startswith(">"):
                                out.append(lines[i][1:])
                                i = i + 1
                            else:
                                out.append(lines[i])
                                i = i + 1
                else:
                    break

            out.append('</blockquote>')
        else:
            out.append(line)
            i = i + 1
    return '\n'.join(out)

def walk_item(item):
    if 'Chapter' in item:
        chapter = item['Chapter']
        chapter['content'] = transform_content(chapter['content'])
        for sub in chapter.get('sub_items', []):
            walk_item(sub)

def main():
    if len(sys.argv) >= 2 and sys.argv[1] == 'supports':
        renderer = sys.argv[2] if len(sys.argv) >= 3 else ''
        sys.exit(0 if renderer == 'html' else 1)

    _context, book = json.load(sys.stdin)
    for section in book.get('sections', []):
        walk_item(section)
    for section in book.get('items', []):
        walk_item(section)
    print(json.dumps(book))


if __name__ == '__main__':
    main()
