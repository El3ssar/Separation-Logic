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
import os
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


class Handler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store, must-revalidate")
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        super().end_headers()

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
