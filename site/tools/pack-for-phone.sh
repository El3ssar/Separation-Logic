#!/usr/bin/env bash
# Pack the whole workbook — course, tools and Lean runtime — into one archive
# to copy onto a phone and serve there with Termux.
#
#   site/tools/pack-for-phone.sh [out.tar.gz]
#
# Serving it from the phone itself is the simplest setup there is: the address
# is then http://localhost:8123, and localhost is a secure context by
# definition, so there is no certificate, no CA to install, and no browser flag.
# It also means the PC does not have to be on.
#
# On the phone, once:
#   pkg install python
#   tar xzf workbook.tar.gz
#   python3 site/tools/serve.py --http --local
# then open http://localhost:8123 in Chrome.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE="$HERE/.."
OUT="${1:-$(cd "$SITE/.." && pwd)/workbook-for-phone.tar.gz}"

[ -f "$SITE/lean-wasm/lean.wasm" ] || {
  echo "the Lean runtime is missing — run site/tools/fetch-lean-wasm.sh first" >&2
  exit 1
}
[ -f "$SITE/lean-wasm/snapshots/init.snap" ] || {
  echo "warning: no startup snapshot; the phone will take minutes to start Lean" >&2
}

echo "→ packing (this is mostly the 222 MB Lean runtime, so it takes a minute)"
tar czf "$OUT" \
  -C "$(cd "$SITE/.." && pwd)" \
  --exclude='site/tools/.cert' \
  --exclude='site/tools/_src' \
  --exclude='site/lean-wasm/lean-lib' \
  --exclude='._*' \
  site

echo
echo "wrote $OUT  ($(du -h "$OUT" | cut -f1))"
cat <<'EOF'

Copy it to the phone (USB, syncthing, a share, whatever), then in Termux:

    pkg install python
    tar xzf workbook-for-phone.tar.gz
    python3 site/tools/serve.py --http --local

and open  http://localhost:8123  in Chrome.

localhost is a secure context, so SharedArrayBuffer and the service worker both
work with no certificate and no flags. Nothing is served to the network.

Note: lean-lib/ is deliberately left out. The startup snapshot already carries
the whole imported Init environment, so those 1256 .olean files are never read.
EOF
