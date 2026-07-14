#!/usr/bin/env python3
"""Run the remote-stripe integration tests (cases.py) with fault injection.

Stands up a real `remote-stripe-server` serving a random image, puts a
[toxiproxy](https://github.com/Shopify/toxiproxy) MITM in front of it on a
loopback port, points the `remote-stripe-shell` client at the proxy, and runs
the cases -- which inject faults (latency, connection drops, resets) through the
toxiproxy admin API and assert the client/server behave. Everything is local, so
no credentials or external services are needed.

    cargo build --bin remote-stripe-server --bin remote-stripe-shell
    python3 tests/remote-stripe-integration/run_all.py

Optional overrides: TOXIPROXY_BIN (default "toxiproxy-server" on PATH), and
SERVER_BIN / SHELL_BIN if the ubiblk binaries are not in target/debug.
"""

import os
import pathlib
import shutil
import socket
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))

from util import http, toml_dump
from harness import free_port, install_exit_handler, wait_for

ROOT = pathlib.Path(__file__).resolve().parents[2]
BIN_DIR = ROOT / "target" / "debug"

DEVICE_MB = 4  # with 1 MiB default stripes -> 4 stripes
STRIPE_SIZE = 1 << 20  # DEFAULT_STRIPE_SECTOR_COUNT_SHIFT (11) * 512-byte sectors


def check_binaries(server_bin, shell_bin):
    missing = [p for p in (server_bin, shell_bin) if not os.path.exists(p)]
    if missing:
        sys.exit(
            "missing binaries: " + ", ".join(missing) + "\n"
            "build them first: cargo build --bin remote-stripe-server "
            "--bin remote-stripe-shell"
        )


def server_config():
    """A plain unencrypted device config. With no metadata path, the server
    treats every stripe as written, so it serves the raw image directly."""
    return toml_dump([
        ("device", {"data_path": "data.raw"}),
        ("danger_zone", {"enabled": True, "allow_unencrypted_disk": True}),
    ])


def connection_config(address):
    """A [server] config (shared by --listen-config and --server-config),
    pointing at ``address``, with PSK disabled."""
    return toml_dump([
        ("server", {"address": address}),
        ("danger_zone", {"enabled": True, "allow_unencrypted_connection": True}),
    ])


def main():
    server_bin = os.environ.get("SERVER_BIN", str(BIN_DIR / "remote-stripe-server"))
    shell_bin = os.environ.get("SHELL_BIN", str(BIN_DIR / "remote-stripe-shell"))
    toxiproxy_bin = os.environ.get("TOXIPROXY_BIN", "toxiproxy-server")
    check_binaries(server_bin, shell_bin)

    # Work on a real filesystem: the server opens the image with O_DIRECT, which
    # tmpfs (/tmp on many systems) rejects. target/ is on the repo's fs.
    work = pathlib.Path(tempfile.mkdtemp(prefix="rs-it-", dir=str(ROOT / "target")))
    server_port, proxy_port, admin_port = free_port(), free_port(), free_port()
    admin = f"http://127.0.0.1:{admin_port}"
    proxy_name = "remote-stripe"
    procs = []

    def cleanup():
        for proc in procs:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    proc.kill()
        shutil.rmtree(work, ignore_errors=True)

    install_exit_handler(cleanup)

    # Fixture: a random image plus the three configs (server device, server
    # listen address, client connect address). The client points at the proxy.
    (work / "data.raw").write_bytes(os.urandom(DEVICE_MB * 1024 * 1024))
    (work / "device.toml").write_text(server_config())
    (work / "listen.toml").write_text(connection_config(f"127.0.0.1:{server_port}"))
    (work / "shell.toml").write_text(connection_config(f"127.0.0.1:{proxy_port}"))
    for name in ("device.toml", "listen.toml", "shell.toml"):
        os.chmod(work / name, 0o600)  # silence the config-permission warning

    server_log = open(work / "server.log", "w")
    procs.append(subprocess.Popen(
        [server_bin, "-f", str(work / "device.toml"), "--listen-config", str(work / "listen.toml")],
        stdout=server_log, stderr=subprocess.STDOUT,
    ))
    toxi_log = open(work / "toxiproxy.log", "w")
    procs.append(subprocess.Popen(
        [toxiproxy_bin, "-host", "127.0.0.1", "-port", str(admin_port)],
        stdout=toxi_log, stderr=subprocess.STDOUT,
    ))

    wait_for(lambda: socket.create_connection(("127.0.0.1", server_port), timeout=0.5).close(),
             f"remote-stripe-server on port {server_port}")
    wait_for(lambda: http("GET", f"{admin}/version"), "toxiproxy admin API")
    http("POST", f"{admin}/proxies", body={
        "name": proxy_name,
        "listen": f"127.0.0.1:{proxy_port}",
        "upstream": f"127.0.0.1:{server_port}",
        "enabled": True,
    })

    os.environ.update({
        "REMOTE_STRIPE_TESTS_ADMIN": admin,
        "REMOTE_STRIPE_TESTS_PROXY": proxy_name,
        "REMOTE_STRIPE_TESTS_SHELL_CONFIG": str(work / "shell.toml"),
        "REMOTE_STRIPE_TESTS_DATA": str(work / "data.raw"),
        "REMOTE_STRIPE_TESTS_WORK": str(work),
        "REMOTE_STRIPE_TESTS_STRIPE_SIZE": str(STRIPE_SIZE),
    })

    from cases import Cases

    sys.exit(Cases().run())


if __name__ == "__main__":
    main()
