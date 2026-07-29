#!/usr/bin/env bash
# Print the real Lean goal state at any point in a proof.
#
#   site/tools/goalstate.sh m1 snippet.lean
#
# Concatenates lean/prelude/<chapter>.lean (everything defined up to and
# including that chapter) with your snippet, runs Lean, and prints whatever
# Lean says. Put `trace_state` on its own line inside a proof wherever you
# want to see the goal.
#
#   theorem write_shadow ... := by
#     funext x
#     trace_state          <-- prints the goal here
#     by_cases hx : x = l <;> simp [Heap.write, hx]
#
# Silence (apart from your trace_state output) means it compiled.
set -euo pipefail

CH="${1:?usage: goalstate.sh <chapter-id> <snippet.lean>}"
SNIP="${2:?usage: goalstate.sh <chapter-id> <snippet.lean>}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PRELUDE="$HERE/../lean/prelude/$CH.lean"

[ -f "$PRELUDE" ] || { echo "no prelude for '$CH'; have: $(ls "$HERE/../lean/prelude" | sed 's/\.lean//' | tr '\n' ' ')" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cat "$PRELUDE" "$SNIP" > "$TMP/T.lean"

# Report line numbers relative to the snippet, not the concatenated file.
OFFSET=$(wc -l < "$PRELUDE")
lean "$TMP/T.lean" 2>&1 | sed -E "s#^$TMP/T\.lean:([0-9]+)#snippet:\$((\1-$OFFSET))#" || true
