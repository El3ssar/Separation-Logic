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


CA_KEY = os.path.join(CERT_DIR, "ca-key.pem")
CA_CRT = os.path.join(CERT_DIR, "ca.crt")
SRV_KEY = os.path.join(CERT_DIR, "key.pem")
SRV_CRT = os.path.join(CERT_DIR, "cert.pem")
STAMP = os.path.join(CERT_DIR, "for")


def _openssl(args):
    subprocess.run(["openssl"] + args, check=True, capture_output=True)


def ensure_ca():
    """A small certificate authority of your own, created once.

    A *self-signed server* certificate is not enough: browsers refuse to
    register a service worker over a connection with any certificate error,
    and clicking through the interstitial does not lift that. So instead we
    become a one-machine CA, install that CA on the phone once, and issue a
    properly-signed certificate for this server. Then there is no error to
    click through, and everything — service worker, SharedArrayBuffer, the
    offline install — simply works.

    The CA key never leaves this directory. Only ca.crt goes to the phone.
    """
    if os.path.exists(CA_KEY) and os.path.exists(CA_CRT):
        return True
    os.makedirs(CERT_DIR, exist_ok=True)
    try:
        _openssl([
            "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256",
            "-keyout", CA_KEY, "-out", CA_CRT, "-days", "3650",
            "-subj", "/CN=Separation Logic workbook local CA/O=Separation Logic workbook",
            "-addext", "basicConstraints=critical,CA:TRUE,pathlen:0",
            "-addext", "keyUsage=critical,keyCertSign,cRLSign",
        ])
    except (OSError, subprocess.CalledProcessError) as e:
        print(f"could not create the local CA: {_why(e)}", file=sys.stderr)
        return False
    os.chmod(CA_KEY, 0o600)
    return True


def _why(e):
    err = getattr(e, "stderr", b"") or b""
    return err.decode(errors="replace").strip() or str(e)


def ensure_cert(ip):
    """Server certificate for localhost + this machine's LAN address, signed
    by our own CA. Regenerated whenever the LAN address changes."""
    if not ensure_ca():
        return None

    want = ip or "localhost"
    if os.path.exists(SRV_KEY) and os.path.exists(SRV_CRT):
        try:
            if open(STAMP).read().strip() == want:
                return SRV_KEY, SRV_CRT
        except OSError:
            pass

    san = "DNS:localhost,IP:127.0.0.1" + (f",IP:{ip}" if ip else "")
    csr = os.path.join(CERT_DIR, "req.csr")
    ext = os.path.join(CERT_DIR, "ext.cnf")
    with open(ext, "w") as f:
        f.write(
            f"subjectAltName={san}\n"
            "basicConstraints=critical,CA:FALSE\n"
            "keyUsage=critical,digitalSignature,keyEncipherment\n"
            "extendedKeyUsage=serverAuth\n"
        )
    try:
        _openssl(["req", "-newkey", "rsa:2048", "-nodes", "-sha256",
                  "-keyout", SRV_KEY, "-out", csr, "-subj", f"/CN={want}"])
        # 397 days: browsers reject server certificates valid for much longer.
        _openssl(["x509", "-req", "-in", csr, "-CA", CA_CRT, "-CAkey", CA_KEY,
                  "-CAcreateserial", "-out", SRV_CRT, "-days", "397",
                  "-sha256", "-extfile", ext])
    except (OSError, subprocess.CalledProcessError) as e:
        print(f"could not create a server certificate: {_why(e)}", file=sys.stderr)
        return None
    finally:
        for p in (csr, ext):
            try:
                os.remove(p)
            except OSError:
                pass
    with open(STAMP, "w") as f:
        f.write(want)
    return SRV_KEY, SRV_CRT


class CAHandler(http.server.BaseHTTPRequestHandler):
    """Hands out ca.crt over plain http, so the phone can fetch and install it.

    It has to be plain http: the phone cannot trust the https server until it
    has this file, and it cannot get this file over a connection it does not
    trust. Only the public certificate is served — never the key.
    """
    def do_GET(self):
        if self.path.rstrip("/") not in ("", "/ca.crt", "/ca"):
            self.send_error(404)
            return
        body = open(CA_CRT, "rb").read()
        self.send_response(200)
        # application/x-x509-ca-cert makes Android offer the install dialog
        self.send_header("Content-Type", "application/x-x509-ca-cert")
        self.send_header("Content-Disposition", 'attachment; filename="workbook-ca.crt"')
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *a):
        pass


def start_ca_server(port):
    import threading
    try:
        srv = http.server.ThreadingHTTPServer(("0.0.0.0", port), CAHandler)
    except OSError:
        return None
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv


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

    if ip and scheme == "https":
        ca_port = port + 1
        started = start_ca_server(ca_port)
        print()
        print("  FIRST TIME ON A PHONE — install the certificate authority once:")
        if started:
            print(f"    1. open  http://{ip}:{ca_port}/ca.crt   (plain http, downloads the CA)")
        else:
            print(f"    1. copy  {CA_CRT}  to the phone")
        print("    2. Settings → Security → More security settings →")
        print("       Encryption & credentials → Install a certificate → CA certificate")
        print("       pick the downloaded file (Android warns; that is expected for your own CA)")
        print(f"    3. open  https://{ip}:{port}")
        print()
        print("  After that there is no certificate warning, and the offline install works.")
        print(f"  Already installed?  just open  https://{ip}:{port}", flush=True)
    elif ip:
        print(f"on this network:  {scheme}://{ip}:{port}", flush=True)

    with httpd:
        httpd.serve_forever()


if __name__ == "__main__":
    main()
