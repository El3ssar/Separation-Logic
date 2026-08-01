#!/usr/bin/env bash
# Compile a Lean snippet against everything established BEFORE lecture NN.
#
#   site/tools/e2/check.sh 07 /tmp/snippet.lean
#   site/tools/e2/check.sh 07 /tmp/snippet.lean --incl     (include lecture 07's own fragment)
#
# Silence means it compiled. Line numbers are reported relative to YOUR snippet,
# not to the concatenated file.
#
# Put `trace_state` on its own line inside a proof to print the real goal there —
# that is how every goal state quoted in the course must be obtained. Never
# invent one.
set -euo pipefail

N="${1:?usage: check.sh <NN> <snippet.lean> [--incl]}"
SNIP="${2:?usage: check.sh <NN> <snippet.lean> [--incl]}"
INCL="${3:-}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

[ -f "$SNIP" ] || { echo "no such snippet: $SNIP" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

"$HERE/prelude.sh" "$N" ${INCL:+--incl} > "$TMP/P.lean"
cat "$TMP/P.lean" "$SNIP" > "$TMP/T.lean"
OFFSET=$(wc -l < "$TMP/P.lean")

# Rewrite "<tmp>/T.lean:123:4:" into "snippet:23:4:" — real arithmetic, so the
# line number points at the line you actually wrote. Anything reported at or
# before the prelude boundary is flagged, because it means your snippet broke
# something that was already established.
lean "$TMP/T.lean" 2>&1 | awk -v pfx="$TMP/T.lean:" -v off="$OFFSET" '
  index($0, pfx) == 1 {
    rest = substr($0, length(pfx) + 1)
    p = index(rest, ":")
    ln = substr(rest, 1, p - 1) + 0
    if (ln <= off) { print "PRELUDE:" rest; next }
    print "snippet:" (ln - off) substr(rest, p)
    next
  }
  { print }
' || true
