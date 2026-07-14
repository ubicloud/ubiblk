"""Remote-stripe integration test cases, in Python.

Drives the `remote-stripe-shell` client against a real `remote-stripe-server`
through a toxiproxy MITM, injecting faults through the toxiproxy admin API and
asserting the protocol's robustness behaviour (correct reads, latency
tolerance, reconnect-with-backoff, server survival of broken sessions). Normally
run via run_all.py (the launcher), which stands up the server and proxy and sets
these variables (all set by that launcher):

    REMOTE_STRIPE_TESTS_ADMIN          toxiproxy admin API URL
    REMOTE_STRIPE_TESTS_PROXY          proxy name
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

from util import http
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
        self.config = env["REMOTE_STRIPE_TESTS_SHELL_CONFIG"]
        self.data = pathlib.Path(env["REMOTE_STRIPE_TESTS_DATA"]).read_bytes()
        self.stripe_size = int(env["REMOTE_STRIPE_TESTS_STRIPE_SIZE"])
        self.work = pathlib.Path(env["REMOTE_STRIPE_TESTS_WORK"])

    def shell(self, reconnect=False):
        self._n += 1
        return Shell(self.config, str(self.work / f"shell-{self._n}.log"), reconnect=reconnect)

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

    CASES = [
        case_baseline_fetch_matches_source,
        case_fetch_tolerates_latency,
    ]
