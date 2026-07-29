#!/usr/bin/env python3
"""Static server for the workbook, with caching turned off.

    python3 site/tools/serve.py [port]        # default 8123

Plain `python3 -m http.server` lets the browser cache assets/app.js, so an edit
to the renderer appears not to take effect until a hard reload. This sends
Cache-Control: no-store on everything, which is what you want while editing and
costs nothing on localhost.
"""
import http.server
import functools
import io
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


ASSET_REF = re.compile(rb'(src|href)="((?:assets|content)/[^"?]+)"')


class Handler(http.server.SimpleHTTPRequestHandler):
    # Cache-Control alone does not reliably defeat every embedded browser view,
    # and a stale app.js silently invalidates whatever you were just testing.
    # So index.html is rewritten on the way out with a ?v=<mtime> on each local
    # asset: a changed file gets a changed URL, which no cache can confuse.
    def send_head(self):
        if self.path.split("?")[0] in ("/", "/index.html"):
            return self._send_index()
        return super().send_head()

    def _send_index(self):
        path = os.path.join(ROOT, "index.html")
        try:
            body = open(path, "rb").read()
        except OSError:
            self.send_error(404)
            return None

        def stamp(m):
            kind, rel = m.group(1), m.group(2)
            full = os.path.join(ROOT, rel.decode())
            try:
                v = str(int(os.path.getmtime(full))).encode()
            except OSError:
                return m.group(0)
            return b'%s="%s?v=%s"' % (kind, rel, v)

        body = ASSET_REF.sub(stamp, body)
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        return io.BytesIO(body)
    # The Lean runtime is a pthread build: it needs SharedArrayBuffer, which
    # browsers only hand out to a cross-origin-isolated page. That is what
    # these two headers buy. Without them the worker boots and then dies.
    def end_headers(self):
        self.send_header("Cross-Origin-Opener-Policy", "same-origin")
        self.send_header("Cross-Origin-Embedder-Policy", "require-corp")
        self.send_header("Cross-Origin-Resource-Policy", "same-origin")
        # The Lean binaries are 226 MB and never change within a build; caching
        # them is the difference between a 2-minute and a 3-second startup.
        if self.path.startswith("/lean-wasm/"):
            self.send_header("Cache-Control", "public, max-age=31536000, immutable")
        else:
            self.send_header("Cache-Control", "no-store, must-revalidate")
            self.send_header("Pragma", "no-cache")
            self.send_header("Expires", "0")
        super().end_headers()

    extensions_map = {
        **http.server.SimpleHTTPRequestHandler.extensions_map,
        ".wasm": "application/wasm",
        ".snap": "application/octet-stream",
        ".olean": "application/octet-stream",
    }

    def log_message(self, fmt, *args):
        # keep 200s quiet; surface anything that is not a success
        if args and str(args[1]).startswith(("4", "5")):
            super().log_message(fmt, *args)


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8123
    handler = functools.partial(Handler, directory=ROOT)
    with http.server.ThreadingHTTPServer(("127.0.0.1", port), handler) as httpd:
        print(f"workbook on http://localhost:{port}  (serving {os.path.realpath(ROOT)}, caching off)", flush=True)
        httpd.serve_forever()


if __name__ == "__main__":
    main()
