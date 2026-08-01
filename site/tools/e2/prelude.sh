#!/usr/bin/env bash
# Print the cumulative Lean context available BEFORE a given lecture.
#
#   site/tools/e2/prelude.sh 07          everything lectures 00..06 established
#   site/tools/e2/prelude.sh 07 --incl    ... including lecture 07's own fragment
#
# The second edition keeps its Lean in one fragment per lecture, under
# site/lean/e2/NN-<id>.lean, concatenated in lecture order. The concatenation of
# fragments 00..N-1 is exactly what a reader arrives at lecture N knowing, so it
# is both the prelude for testing snippets and the context the browser checks a
# reader's proof against.
set -euo pipefail

N="${1:?usage: prelude.sh <NN> [--incl]}"
INCL="${2:-}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FRAG="$HERE/../../lean/e2"

[ -d "$FRAG" ] || { echo "no fragments yet: $FRAG" >&2; exit 1; }

for f in "$FRAG"/*.lean; do
  [ -e "$f" ] || continue
  num="$(basename "$f" | cut -d- -f1)"
  # numeric compare, so 07 < 10
  if [ "$INCL" = "--incl" ]; then
    [ "$((10#$num))" -le "$((10#$N))" ] && cat "$f" && echo
  else
    [ "$((10#$num))" -lt "$((10#$N))" ] && cat "$f" && echo
  fi
done
true
