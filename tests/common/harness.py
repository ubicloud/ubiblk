"""Shared scaffolding for the integration test suites (see tests/*-integration).

Holds the bits both the S3 (r2proxy) and remote-stripe (toxiproxy) suites would
otherwise duplicate: the launcher plumbing (a free port, a readiness poll, and
an exit handler that also fires on SIGTERM/SIGINT) and a ``Suite`` base class
with the ok/notok reporting and the case-runner loop.
"""

import atexit
import random
import signal
import socket
import sys
import time


def free_port():
    """Return a currently-free loopback TCP port."""
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


def install_exit_handler(cleanup):
    """Run ``cleanup`` on normal exit and on SIGTERM/SIGINT.

    The signal handlers turn a termination into a normal ``sys.exit`` so the
    atexit-registered cleanup still runs (stopping a proxy, deleting scratch
    state) even when a run is cancelled.
    """
    atexit.register(cleanup)
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    signal.signal(signal.SIGINT, lambda *_: sys.exit(130))


def wait_for(probe, what, attempts=100, delay=0.1):
    """Call ``probe`` repeatedly until it returns without raising, or give up.

    ``probe`` should raise while the dependency is not ready yet. After
    ``attempts`` tries it exits with an error naming ``what``.
    """
    for _ in range(attempts):
        try:
            probe()
            return
        except Exception:
            time.sleep(delay)
    sys.exit(f"{what} did not become ready in time")


class Suite:
    """Base class for a suite of test cases.

    Subclasses list their case methods in ``CASES`` and may override ``setup``
    (run once before the cases). ``run`` executes each case, treating a raised
    exception as a failure, and returns a process exit code.
    """

    CASES = []

    def __init__(self):
        self.results = []
        self._n = 0

    def ok(self, name):
        print(f"ok   - {name}")
        self.results.append(True)

    def notok(self, name, detail):
        print(f"FAIL - {name} ({detail})")
        self.results.append(False)

    def uid(self, tag):
        """Return a short unique id (a per-suite counter plus randomness)."""
        self._n += 1
        return f"{tag}-{self._n}-{random.randrange(1 << 24)}"

    def setup(self):
        pass

    def run(self):
        self.setup()
        for case in self.CASES:
            try:
                case(self)
            except Exception as e:  # a case that raises counts as a failure
                self.notok(case.__name__, f"raised {type(e).__name__}: {e}")
        passed = sum(self.results)
        failed = len(self.results) - passed
        print(f"\n# {passed} passed, {failed} failed")
        return 1 if failed else 0
