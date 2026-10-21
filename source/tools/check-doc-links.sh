#! /bin/bash
# Checks links between the guide, the state machines book and verusdoc.
# Links to https://verus-lang.github.io/verus/ are checked against a local build.
# Run from `source/` after `tools/docs-cargo.sh`; needs `mdbook` and `lychee` on PATH.

set -e

SITE=$(mktemp -d)
trap 'rm -rf "$SITE"' EXIT

mdbook build -d "$SITE/guide" docs/guide
mdbook build -d "$SITE/state_machines" docs/state_machines
cp -R doc "$SITE/verusdoc"

# rustdoc's source-page line anchors only exist after its JavaScript runs
lychee --offline --no-progress --include-fragments \
  --remap "https://verus-lang\.github\.io/verus/(.*) file://$SITE/\$1" \
  --root-dir "$SITE" \
  --exclude-path "$SITE/guide/print.html" \
  --exclude-path "$SITE/state_machines/print.html" \
  --exclude-path "$SITE/verusdoc/help.html" \
  --exclude-path "$SITE/verusdoc/settings.html" \
  --exclude "^file://$SITE/verusdoc/src/" \
  "$SITE/**/*.html"
