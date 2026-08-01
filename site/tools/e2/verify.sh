#!/usr/bin/env bash
# Verify the second-edition Lean corpus, cumulatively.
#
#   site/tools/e2/verify.sh          every fragment, concatenated, as one file
#   site/tools/e2/verify.sh 07       fragments 00..07 only (what a lecture author wants)
#
# The whole corpus must compile as ONE file with no imports, no Mathlib and no
# sorry — that is the guarantee the course makes to its reader. Compiling the
# fragments cumulatively also proves the ordering is honest: nothing in lecture N
# may depend on anything proved after it.
set -euo pipefail

UPTO="${1:-9999}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

"$HERE/prelude.sh" "$UPTO" --incl > "$TMP/C.lean"
LINES=$(wc -l < "$TMP/C.lean")
DECLS=$(grep -cE '^(theorem|lemma|def|abbrev|inductive|structure)\b' "$TMP/C.lean" || true)

echo "corpus: $LINES lines, $DECLS top-level declarations"

if grep -n 'sorry' "$TMP/C.lean" | grep -vq '^\s*--'; then
  if grep -qE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' "$TMP/C.lean"; then
    echo "REFUSED: the corpus contains 'sorry'" >&2
    grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' "$TMP/C.lean" >&2
    exit 1
  fi
fi

OUT="$(lean "$TMP/C.lean" 2>&1 || true)"
if [ -z "$OUT" ]; then
  echo "OK — it all compiled."
  exit 0
fi

echo "$OUT" | sed "s#$TMP/C.lean#corpus#"
echo
echo "FAILED" >&2
exit 1
