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
import ssl
import subprocess
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


def lan_address():
    """Best guess at this machine's address on the local network."""
    import socket
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))      # no packet is sent
        return s.getsockname()[0]
    except OSError:
        return None
    finally:
        s.close()


CERT_DIR = os.path.join(ROOT, "tools", ".cert")


def ensure_cert(ip):
    """Self-signed cert covering localhost and this machine's LAN address.

    Needed because the Lean runtime requires SharedArrayBuffer and the offline
    install requires a service worker, and browsers grant neither outside a
    *secure context*. localhost counts as secure; a plain-http LAN address does
    not. So reaching this from a phone means HTTPS, which means a certificate.
    """
    key = os.path.join(CERT_DIR, "key.pem")
    crt = os.path.join(CERT_DIR, "cert.pem")
    stamp = os.path.join(CERT_DIR, "for")

    want = ip or "localhost"
    if os.path.exists(key) and os.path.exists(crt):
        try:
            if open(stamp).read().strip() == want:
                return key, crt
        except OSError:
            pass

    os.makedirs(CERT_DIR, exist_ok=True)
    san = "DNS:localhost,IP:127.0.0.1" + (f",IP:{ip}" if ip else "")
    cmd = [
        "openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
        "-keyout", key, "-out", crt, "-days", "3650",
        "-subj", "/CN=Separation Logic workbook",
        "-addext", f"subjectAltName={san}",
    ]
    try:
        subprocess.run(cmd, check=True, capture_output=True)
    except (OSError, subprocess.CalledProcessError) as e:
        detail = getattr(e, "stderr", b"")
        print(f"could not create a certificate ({detail.decode(errors='replace').strip() or e})", file=sys.stderr)
        return None
    with open(stamp, "w") as f:
        f.write(want)
    return key, crt


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 8123
    # Bind on all interfaces so a phone on the same wi-fi can reach it — that is
    # how you install the offline copy. Pass --local to restrict to this machine.
    host = "127.0.0.1" if "--local" in sys.argv else "0.0.0.0"
    ip = lan_address() if host != "127.0.0.1" else None
    use_tls = "--http" not in sys.argv

    handler = functools.partial(Handler, directory=ROOT)
    httpd = http.server.ThreadingHTTPServer((host, port), handler)

    scheme = "http"
    if use_tls:
        pair = ensure_cert(ip)
        if pair:
            ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ctx.load_cert_chain(pair[1], pair[0])
            httpd.socket = ctx.wrap_socket(httpd.socket, server_side=True)
            scheme = "https"
        else:
            print("falling back to plain http — Lean will not start except on localhost", file=sys.stderr)

    print(f"workbook on {scheme}://localhost:{port}   ({os.path.realpath(ROOT)}, caching off)", flush=True)
    if ip:
        print(f"on this network:  {scheme}://{ip}:{port}   ← open this on your phone", flush=True)
        if scheme == "https":
            print("  the certificate is self-signed, so the phone will warn once;", flush=True)
            print("  choose Advanced → Proceed. Lean needs the secure origin.", flush=True)
    with httpd:
        httpd.serve_forever()


if __name__ == "__main__":
    main()
