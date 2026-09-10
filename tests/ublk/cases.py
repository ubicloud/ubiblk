"""ublk test cases, in Python.

Brings up a real ublk device over a ubiblk backend and exercises it end to end.
Normally run via run_all.py, which checks the binaries and the driver first.
Each case gets its own device, so one that leaves the kernel unhappy cannot
quietly break the next.

Binaries default to target/debug; override with UBLK_BACKEND_BIN.
"""

import contextlib
import hashlib
import os
import pathlib
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))

from util import r
from harness import Suite

ROOT = pathlib.Path(__file__).resolve().parents[2]
BIN_DIR = ROOT / "target" / "debug"
BACKEND = os.environ.get("UBLK_BACKEND_BIN", str(BIN_DIR / "ublk-backend"))

DEVICE_MB = 64
DEVICE_TIMEOUT = 60
SHUTDOWN_TIMEOUT = 30


class Device:
    """A ubiblk-backed ublk device, for the lifetime of a `with` block."""

    def __init__(self, work):
        self.work = work
        self.log = work / "backend.log"
        self.symlink = work / "dev"
        self.node = None
        self.backend = None

    def __enter__(self):
        self.work.mkdir(parents=True, exist_ok=True)
        env = dict(os.environ, PATH=f"{BIN_DIR}:{os.environ['PATH']}")
        r(
            "python3",
            str(ROOT / "scripts" / "ubiblk-init"),
            "--size",
            f"{DEVICE_MB}M",
            "--dir",
            str(self.work),
            "--force",
            env=env,
        )
        self.backend = subprocess.Popen(
            ["sudo", BACKEND, "--config", str(self.work / "config.toml"),
             "--device-symlink", str(self.symlink)],
            stdout=self.log.open("w"),
            stderr=subprocess.STDOUT,
        )
        self.node = self._wait_for_node()
        return self

    def __exit__(self, *_):
        self.stop()
        return False

    def _wait_for_node(self):
        deadline = time.monotonic() + DEVICE_TIMEOUT
        while time.monotonic() < deadline:
            if self.symlink.exists():
                return self.symlink.resolve()
            if not self.alive():
                raise AssertionError(
                    f"the backend exited before the device appeared\n{self.tail()}"
                )
            time.sleep(0.2)
        raise AssertionError(f"no device after {DEVICE_TIMEOUT}s\n{self.tail()}")

    def alive(self):
        """True while the backend is running. It runs under sudo, so a plain
        kill -0 from this user reports "gone" rather than the truth."""
        if self.backend.poll() is not None:
            return False
        return subprocess.run(
            ["sudo", "kill", "-0", str(self.backend.pid)],
            capture_output=True,
        ).returncode == 0

    def interrupt(self):
        subprocess.run(["sudo", "kill", "-INT", str(self.backend.pid)], capture_output=True)

    def stop(self):
        if self.backend is None or self.backend.poll() is not None:
            return
        self.interrupt()
        deadline = time.monotonic() + SHUTDOWN_TIMEOUT
        while time.monotonic() < deadline and self.alive():
            time.sleep(0.2)
        if self.alive():
            subprocess.run(["sudo", "kill", "-9", str(self.backend.pid)], capture_output=True)
        with contextlib.suppress(Exception):
            self.backend.wait(timeout=5)

    def size(self):
        return int(r("sudo", "blockdev", "--getsize64", str(self.node)).strip())

    def write(self, path, megabytes):
        r("sudo", "dd", f"if={path}", f"of={self.node}", "bs=1M",
          f"count={megabytes}", "oflag=direct", "status=none")

    def read_digest(self, megabytes):
        out = subprocess.run(
            ["sudo", "dd", f"if={self.node}", "bs=1M", f"count={megabytes}",
             "iflag=direct", "status=none"],
            capture_output=True,
        )
        if out.returncode != 0:
            raise AssertionError(f"read failed: {out.stderr.decode(errors='replace')}")
        return hashlib.md5(out.stdout).hexdigest()

    def tail(self, lines=30):
        if not self.log.exists():
            return "(no backend log)"
        return "--- backend log ---\n" + "\n".join(
            self.log.read_text(errors="replace").splitlines()[-lines:]
        )


def case_device_appears_with_the_right_size(suite):
    name = "device_appears_with_the_right_size"
    expected = DEVICE_MB * 1024 * 1024
    with suite.device(name) as device:
        size = device.size()
    if size == expected:
        suite.ok(name)
    else:
        suite.notok(name, f"device is {size} bytes, expected {expected}")


def case_data_reads_back_as_written(suite):
    name = "data_reads_back_as_written"
    with suite.device(name) as device:
        pattern = device.work / "pattern"
        pattern.write_bytes(os.urandom(DEVICE_MB * 1024 * 1024))
        device.write(pattern, DEVICE_MB)
        want = hashlib.md5(pattern.read_bytes()).hexdigest()
        got = device.read_digest(DEVICE_MB)
    if want == got:
        suite.ok(name)
    else:
        suite.notok(name, "what came back is not what went in")


def case_shutdown_removes_the_device(suite):
    name = "shutdown_removes_the_device"
    with suite.device(name) as device:
        node, symlink = device.node, device.symlink
        device.interrupt()
        deadline = time.monotonic() + SHUTDOWN_TIMEOUT
        while time.monotonic() < deadline and device.alive():
            time.sleep(0.2)
        if device.alive():
            reason = "the backend did not exit on SIGINT"
        elif node.exists():
            reason = f"{node} is still there"
        elif symlink.exists():
            reason = "the device symlink was left behind"
        else:
            reason = None
    if reason is None:
        suite.ok(name)
    else:
        suite.notok(name, reason)


class Cases(Suite):
    def __init__(self):
        super().__init__()
        self.work = ROOT / "target" / "tests" / "ublk"

    def device(self, name):
        return Device(self.work / name)

    CASES = [
        case_device_appears_with_the_right_size,
        case_data_reads_back_as_written,
        case_shutdown_removes_the_device,
    ]


if __name__ == "__main__":
    sys.exit(Cases().run())
