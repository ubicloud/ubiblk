"""Remote-stripe integration test cases, in Python.

Drives the `remote-stripe-shell` client against a real `remote-stripe-server`
through a toxiproxy MITM, injecting faults through the toxiproxy admin API and
asserting the protocol's robustness behaviour (correct reads, latency
tolerance, reconnect-with-backoff, server survival of broken sessions). Normally
run via run_all.py (the launcher), which stands up the server and proxy and sets
these variables (all set by that launcher):

    REMOTE_STRIPE_TESTS_ADMIN          toxiproxy admin API URL
    REMOTE_STRIPE_TESTS_PROXY          proxy name
    REMOTE_STRIPE_TESTS_PROXY_ADDR     proxy host:port (for custom client configs)
    REMOTE_STRIPE_TESTS_SHELL_CONFIG   client config pointing at the proxy
    REMOTE_STRIPE_TESTS_DATA           the served image, for byte verification
    REMOTE_STRIPE_TESTS_STRIPE_SIZE    stripe size in bytes
    REMOTE_STRIPE_TESTS_WORK           scratch dir (for client logs)

``Cases().run()`` returns a non-zero exit code if any case fails.
"""

import os
import pathlib
import select
import subprocess
import sys
import threading
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))

from util import http, toml_dump
from harness import Suite

SHELL = os.environ.get("SHELL_BIN", str(pathlib.Path(__file__).resolve().parents[2] / "target/debug/remote-stripe-shell"))


class Shell:
    """A running remote-stripe-shell, driven one command at a time.

    Because Rust's stdout is line-buffered, each command's single-line result
    can be read back before the next command is sent -- which lets a case inject
    a fault mid-session (between two fetches) at a deterministic point.
    """

    def __init__(self, config, log_path, reconnect=False):
        args = [SHELL, "--server-config", config]
        if reconnect:
            args.append("--reconnect")
        self.log = open(log_path, "w")
        self.p = subprocess.Popen(
            args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.log,
            text=True, bufsize=1, env={**os.environ, "RUST_LOG": "info"},
        )

    def send(self, command):
        self.p.stdin.write(command + "\n")
        self.p.stdin.flush()

    def read(self, timeout=15):
        """Return the next output line, or None if none arrives within timeout."""
        ready, _, _ = select.select([self.p.stdout], [], [], timeout)
        if not ready:
            return None
        line = self.p.stdout.readline()
        return line.rstrip("\n") if line else None

    def command(self, command, timeout=15):
        self.send(command)
        return self.read(timeout)

    def close(self):
        try:
            self.send("exit")
            self.p.wait(timeout=5)
        except (BrokenPipeError, subprocess.TimeoutExpired, OSError):
            self.p.kill()
        finally:
            self.log.close()


class Cases(Suite):
    def __init__(self):
        super().__init__()
        env = os.environ
        self.admin = env["REMOTE_STRIPE_TESTS_ADMIN"]
        self.proxy = env["REMOTE_STRIPE_TESTS_PROXY"]
        self.proxy_addr = env["REMOTE_STRIPE_TESTS_PROXY_ADDR"]
        self.config = env["REMOTE_STRIPE_TESTS_SHELL_CONFIG"]
        self.data = pathlib.Path(env["REMOTE_STRIPE_TESTS_DATA"]).read_bytes()
        self.stripe_size = int(env["REMOTE_STRIPE_TESTS_STRIPE_SIZE"])
        self.work = pathlib.Path(env["REMOTE_STRIPE_TESTS_WORK"])

    def shell(self, reconnect=False, config=None):
        self._n += 1
        return Shell(config or self.config, str(self.work / f"shell-{self._n}.log"), reconnect=reconnect)

    def shell_config(self, tag, **server_fields):
        """Write a client config pointing at the proxy with extra [server]
        fields (e.g. a short operation_attempt_timeout_ms) and return its path."""
        path = self.work / f"shell-{tag}.toml"
        path.write_text(toml_dump([
            ("server", {"address": self.proxy_addr, **server_fields}),
            ("danger_zone", {"enabled": True, "allow_unencrypted_connection": True}),
        ]))
        os.chmod(path, 0o600)
        return str(path)

    def expected_hex(self, stripe, offset, length):
        start = stripe * self.stripe_size + offset
        return self.data[start:start + length].hex()

    # --- toxiproxy fault injection -------------------------------------------

    def set_enabled(self, enabled):
        http("POST", f"{self.admin}/proxies/{self.proxy}", body={"enabled": enabled})

    def add_toxic(self, toxic):
        http("POST", f"{self.admin}/proxies/{self.proxy}/toxics", body=toxic)

    def reset(self):
        # Re-enable the proxy and drop every toxic, so each case starts clean.
        http("POST", f"{self.admin}/reset")

    # --- cases ---------------------------------------------------------------

    def case_baseline_fetch_matches_source(self):
        # With no faults, a fetched stripe's bytes match the served image.
        self.reset()
        sh = self.shell()
        try:
            for stripe in (0, 2, 3):
                if sh.command(f"fetch_stripe {stripe}") != "FETCHED":
                    self.notok("baseline_fetch_matches_source", f"fetch {stripe} failed")
                    return
                if sh.command(f"dump_stripe {stripe} 0 64") != self.expected_hex(stripe, 0, 64):
                    self.notok("baseline_fetch_matches_source", f"stripe {stripe} bytes differ")
                    return
            self.ok("baseline_fetch_matches_source")
        finally:
            sh.close()

    def case_fetch_tolerates_latency(self):
        # Latency well under the connection timeouts must not break a fetch.
        self.reset()
        self.add_toxic({"type": "latency", "stream": "downstream",
                        "attributes": {"latency": 100, "jitter": 20}})
        sh = self.shell()
        try:
            if sh.command("fetch_stripe 1", timeout=20) != "FETCHED":
                self.notok("fetch_tolerates_latency", "fetch failed under latency")
                return
            if sh.command("dump_stripe 1 0 64") != self.expected_hex(1, 0, 64):
                self.notok("fetch_tolerates_latency", "bytes differ under latency")
                return
            self.ok("fetch_tolerates_latency")
        finally:
            sh.close()
            self.reset()

    def case_reconnect_after_connection_drop(self):
        # The headline: with --reconnect, a fetch whose connection was dropped
        # reconnects (with backoff) once the server is reachable again and still
        # returns the right bytes.
        self.reset()
        sh = self.shell(reconnect=True)
        healer = None
        try:
            if sh.command("fetch_stripe 0") != "FETCHED":
                self.notok("reconnect_after_connection_drop", "initial fetch failed")
                return
            # Drop the connection, then heal it while the next fetch is retrying.
            self.set_enabled(False)
            healer = threading.Timer(1.5, self.set_enabled, args=(True,))
            healer.start()
            line = sh.command("fetch_stripe 2", timeout=30)
            if line != "FETCHED":
                self.notok("reconnect_after_connection_drop", f"fetch after drop returned {line!r}")
                return
            if sh.command("dump_stripe 2 0 64") != self.expected_hex(2, 0, 64):
                self.notok("reconnect_after_connection_drop", "bytes differ after reconnect")
                return
            self.ok("reconnect_after_connection_drop")
        finally:
            if healer is not None:
                healer.join()
            sh.close()
            self.reset()

    def case_no_reconnect_fails_after_drop(self):
        # Contrast: without --reconnect, a dropped connection is not recovered,
        # so the next fetch fails -- confirming the drop is real and that the
        # previous case's success came from the reconnect logic.
        self.reset()
        sh = self.shell(reconnect=False)
        try:
            if sh.command("fetch_stripe 0") != "FETCHED":
                self.notok("no_reconnect_fails_after_drop", "initial fetch failed")
                return
            self.set_enabled(False)
            line = sh.command("fetch_stripe 2", timeout=15)
            if line == "FETCHED":
                self.notok("no_reconnect_fails_after_drop", "fetch unexpectedly succeeded after drop")
                return
            self.ok("no_reconnect_fails_after_drop")
        finally:
            sh.close()
            self.reset()

    def case_server_survives_broken_sessions(self):
        # A peer that resets mid-protocol must not take the server down: the
        # session ends (terminate-on-error) and the server keeps serving. Reset
        # several client connections, then confirm a clean fetch still works.
        self.reset()
        self.add_toxic({"type": "reset_peer", "stream": "downstream", "attributes": {"timeout": 0}})
        for _ in range(3):
            sh = self.shell()
            sh.command("fetch_stripe 0", timeout=10)  # expected to error out
            sh.close()
        self.reset()  # remove the reset_peer toxic
        sh = self.shell()
        try:
            if sh.command("fetch_stripe 0") != "FETCHED":
                self.notok("server_survives_broken_sessions", "server did not recover after resets")
                return
            self.ok("server_survives_broken_sessions")
        finally:
            sh.close()

    def case_unreachable_server_fails_fast(self):
        # With the server unreachable, the client fails to start rather than
        # hanging, and exits non-zero within a bounded time.
        self.reset()
        self.set_enabled(False)
        try:
            start = time.monotonic()
            sh = self.shell()
            sh.p.stdin.close()
            code = sh.p.wait(timeout=20)
            elapsed = time.monotonic() - start
            sh.log.close()
            if code != 0 and elapsed < 15:
                self.ok("unreachable_server_fails_fast")
            else:
                self.notok("unreachable_server_fails_fast", f"exit={code}, elapsed={elapsed:.2f}s")
        except subprocess.TimeoutExpired:
            self.notok("unreachable_server_fails_fast", "client hung with server unreachable")
        finally:
            self.reset()

    def case_read_timeout_aborts_stalled_fetch(self):
        # A `timeout` toxic holds the connection open but stops forwarding data,
        # so a fetch's response never arrives. operation_attempt_timeout_ms bounds
        # each socket read, so a short value aborts the stalled read in about that
        # long instead of hanging; the default (20s) would exceed our read budget.
        # No --reconnect, so we observe the timeout itself rather than the backoff
        # retries after it.
        self.reset()
        cfg = self.shell_config("fast-timeout", operation_attempt_timeout_ms=2000)
        sh = self.shell(config=cfg)
        try:
            if sh.command("fetch_stripe 0") != "FETCHED":
                self.notok("read_timeout_aborts_stalled_fetch", "initial fetch failed")
                return
            self.add_toxic({"type": "timeout", "stream": "downstream", "attributes": {"timeout": 0}})
            start = time.monotonic()
            line = sh.command("fetch_stripe 2", timeout=15)
            elapsed = time.monotonic() - start
            if line == "FETCHED":
                self.notok("read_timeout_aborts_stalled_fetch", "fetch unexpectedly succeeded")
            elif line is None or elapsed > 10:
                self.notok("read_timeout_aborts_stalled_fetch",
                           f"read did not time out promptly ({elapsed:.1f}s, line={line!r})")
            else:
                self.ok("read_timeout_aborts_stalled_fetch")
        finally:
            sh.close()
            self.reset()

    CASES = [
        case_baseline_fetch_matches_source,
        case_fetch_tolerates_latency,
        case_reconnect_after_connection_drop,
        case_no_reconnect_fails_after_drop,
        case_server_survives_broken_sessions,
        case_unreachable_server_fails_fast,
        case_read_timeout_aborts_stalled_fetch,
    ]
