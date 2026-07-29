#!/usr/bin/env bash
# Fetch and install the Lean 4 WebAssembly runtime into site/lean-wasm/.
#
#   site/tools/fetch-lean-wasm.sh
#
# ~295 MB installed, so it is gitignored rather than committed. This script
# reproduces it from scratch.
#
# What it installs, and why these exact pieces:
#   lean.js / lean.wasm       the Lean 4.33-pre kernel and elaborator, compiled
#                             to wasm32 by the cauli/lean4 `reinstate-wasm` fork
#   lean-lib/                 Init's .olean files. Only Init — this course
#                             imports nothing, so Std/Lean/Lake (a further
#                             ~410 MB) are not needed
#   snapshots/init.snap       a baked image of the imported Init environment.
#                             Without it every session pays ~100 s importing
#                             Init; with it, startup is ~11 s
#   lean-worker.js            the Web Worker host (kept in git, not fetched)
set -euo pipefail

REPO=cauli/lean4-wasm-in-browser
TAG=test-fixtures-4.33
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEST="$HERE/../lean-wasm"

command -v gh >/dev/null || { echo "needs the GitHub CLI (gh)" >&2; exit 1; }
command -v node >/dev/null || { echo "needs node" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo "→ downloading $TAG from $REPO (~190 MB)"
( cd "$TMP" && gh release download "$TAG" -R "$REPO" --clobber )
echo "→ extracting"
( cd "$TMP" && tar xzf ./*.tar.gz 2>/dev/null || true )
find "$TMP" -name '._*' -delete

[ -f "$TMP/bin/lean.js" ] || { echo "unexpected archive layout" >&2; exit 1; }

mkdir -p "$DEST/snapshots"
echo "→ installing binaries"
cp "$TMP/bin/lean.js" "$DEST/lean.js"
cp "$TMP/bin/lean.wasm" "$DEST/lean.wasm"

echo "→ installing Init oleans only (skipping Std/Lean/Lake)"
rm -rf "$DEST/lean-lib"
mkdir -p "$DEST/lean-lib"
cp -r "$TMP/lib/lean/Init" "$DEST/lean-lib/"
cp "$TMP/lib/lean/Init.olean" "$DEST/lean-lib/"
find "$DEST/lean-lib" -name '._*' -delete

echo "→ capping declared wasm memory at 2 GB to match the worker's request"
python3 "$HERE/patch-wasm-memory.py" "$DEST/lean.wasm" "$DEST/lean.wasm.tmp" >/dev/null
mv "$DEST/lean.wasm.tmp" "$DEST/lean.wasm"

echo "→ writing lean-lib-files.json"
node "$HERE/gen-lib-files.mjs" "$DEST/lean-lib" "$DEST/lean-lib-files.json" >/dev/null

echo "→ baking the Init snapshot (a few minutes — this is what makes startup fast)"
mkdir -p "$TMP/work"
printf '#check 2+2\n' > "$TMP/work/probe.lean"
LEAN_WASM_NODE_MEMORY_MB=2000 node --stack-size=60000 "$HERE/lean-wasm-node.cjs" \
  "$TMP" "$TMP/work" --incr-header-save=/work/init.snap /work/probe.lean >/dev/null 2>&1 || true
if [ -f "$TMP/work/init.snap" ]; then
  mv "$TMP/work/init.snap" "$DEST/snapshots/init.snap"
  echo "   snapshot: $(du -h "$DEST/snapshots/init.snap" | cut -f1)"
else
  echo "   WARNING: snapshot bake failed; the site still works but starts slowly" >&2
fi

echo
echo "installed $(du -sh "$DEST" | cut -f1) into $DEST"
echo "verify with:  node --stack-size=60000 site/tools/check-all-exercises.cjs"
