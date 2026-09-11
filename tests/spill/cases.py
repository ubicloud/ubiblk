"""Spill layer tests, over a real ublk device.

Brings up a device far larger than the disk under it, writes more than the
cache can hold so chunks have to go to the object store, and checks what comes
back - before and after a restart. Normally run via run_all.py.

Binaries default to target/debug; override with UBLK_BACKEND_BIN.
"""

import contextlib
import os
import pathlib
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))

from harness import Suite
from util import r

ROOT = pathlib.Path(__file__).resolve().parents[2]
BIN_DIR = ROOT / "target" / "debug"
BACKEND = os.environ.get("UBLK_BACKEND_BIN", str(BIN_DIR / "ublk-backend"))

DEVICE_MB = 512
DISK_MB = 64
CHUNK_KB = 128
# More than the disk holds, so most of it has to spill.
WRITTEN_MB = 100
STRIDE_MB = 5
DEVICE_TIMEOUT = 60
SHUTDOWN_TIMEOUT = 30

CONFIG = """\
[device]
data_path = "disk.raw"
device_id = "spill-test"

[encryption]
xts_key.ref = "xts_key"

[secrets.xts_key]
source.file = "xts_key"
encoding = "base64"

[spill]
size_mb = {device_mb}
map_path = "map"
prefix = "dev1"
device_uuid = "0123456789abcdef0123456789abcdef"
chunk_kb = {chunk_kb}

[spill.store]
storage = "filesystem"
path = "store"

[danger_zone]
enabled = true
allow_secret_over_regular_file = true

[tuning]
queue_size = 64
num_queues = 1
seg_size_max = 131072
seg_count_max = 4
"""


def prepare(work):
    """Lay out a spill device's files: a small disk, a store, and a key."""
    (work / "store").mkdir(parents=True, exist_ok=True)
    with (work / "disk.raw").open("wb") as disk:
        disk.truncate(DISK_MB * 1024 * 1024)
    key = os.urandom(64)
    import base64

    (work / "xts_key").write_bytes(base64.b64encode(key))
    (work / "config.toml").write_text(
        CONFIG.format(device_mb=DEVICE_MB, chunk_kb=CHUNK_KB)
    )


class Device:
    """A spill-backed ublk device, for the lifetime of a `with` block."""

    def __init__(self, work, fresh=True):
        self.work = work
        self.log = work / "backend.log"
        self.symlink = work / "dev"
        self.node = None
        self.backend = None
        self.fresh = fresh

    def __enter__(self):
        if self.fresh:
            prepare(self.work)
        self.symlink.unlink(missing_ok=True)
        self.backend = subprocess.Popen(
            ["sudo", BACKEND, "--config", str(self.work / "config.toml"),
             "--device-symlink", str(self.symlink)],
            stdout=self.log.open("a"),
            stderr=subprocess.STDOUT,
            cwd=self.work,
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
        if self.backend.poll() is not None:
            return False
        return subprocess.run(
            ["sudo", "kill", "-0", str(self.backend.pid)], capture_output=True
        ).returncode == 0

    def stop(self):
        if self.backend is None or self.backend.poll() is not None:
            return
        subprocess.run(["sudo", "kill", "-INT", str(self.backend.pid)], capture_output=True)
        deadline = time.monotonic() + SHUTDOWN_TIMEOUT
        while time.monotonic() < deadline and self.alive():
            time.sleep(0.2)
        if self.alive():
            subprocess.run(["sudo", "kill", "-9", str(self.backend.pid)], capture_output=True)
        with contextlib.suppress(Exception):
            self.backend.wait(timeout=5)

    def size(self):
        return int(r("sudo", "blockdev", "--getsize64", str(self.node)).strip())

    def write_mb(self, pattern, at_mb):
        r("sudo", "dd", f"if={pattern}", f"of={self.node}", "bs=1M", f"seek={at_mb}",
          "count=1", "oflag=direct", "conv=notrunc", "status=none")

    def read_mb(self, at_mb):
        out = subprocess.run(
            ["sudo", "dd", f"if={self.node}", "bs=1M", f"skip={at_mb}", "count=1",
             "iflag=direct", "status=none"],
            capture_output=True,
        )
        if out.returncode != 0:
            raise AssertionError(f"read failed: {out.stderr.decode(errors='replace')}")
        return out.stdout

    def objects(self):
        return sum(1 for _ in (self.work / "store").rglob("*") if _.is_file())

    def tail(self, lines=30):
        if not self.log.exists():
            return "(no backend log)"
        return "--- backend log ---\n" + "\n".join(
            self.log.read_text(errors="replace").splitlines()[-lines:]
        )


def patterns(work):
    """Eight one-megabyte patterns, cycled over the writes."""
    made = []
    for i in range(8):
        path = work / f"pattern-{i}"
        if not path.exists():
            path.write_bytes(bytes([0x41 + i]) * 1024 * 1024)
        made.append(path)
    return made


def fill(device, pats):
    for n in range(WRITTEN_MB):
        device.write_mb(pats[n % len(pats)], n * STRIDE_MB)


def check(device, pats):
    """Where the device disagrees with what was written into it."""
    for n in range(WRITTEN_MB):
        expected = pats[n % len(pats)].read_bytes()
        if device.read_mb(n * STRIDE_MB) != expected:
            return f"{n * STRIDE_MB}M came back as something else"
    return None


def case_a_device_is_larger_than_the_disk_under_it(suite):
    name = "a_device_is_larger_than_the_disk_under_it"
    with suite.device(name) as device:
        size = device.size()
    expected = DEVICE_MB * 1024 * 1024
    if size == expected:
        suite.ok(name)
    else:
        suite.notok(name, f"device is {size} bytes, expected {expected}")


def case_what_does_not_fit_goes_to_the_store(suite):
    name = "what_does_not_fit_goes_to_the_store"
    with suite.device(name) as device:
        pats = patterns(device.work)
        fill(device, pats)
        reason = check(device, pats)
        objects = device.objects()
    if reason is None and objects == 0:
        reason = "nothing was uploaded, so the cold tier was never exercised"
    if reason is None:
        suite.ok(name)
    else:
        suite.notok(name, reason)


def case_everything_survives_a_restart(suite):
    name = "everything_survives_a_restart"
    work = suite.work / name
    with Device(work) as device:
        pats = patterns(work)
        fill(device, pats)
        reason = check(device, pats)

    if reason is None:
        with Device(work, fresh=False) as device:
            reason = check(device, pats)
            if reason is not None:
                reason = f"after a restart, {reason}"

    if reason is None:
        suite.ok(name)
    else:
        suite.notok(name, reason)


class Cases(Suite):
    def __init__(self):
        super().__init__()
        self.work = ROOT / "target" / "tests" / "spill"

    def device(self, name):
        return Device(self.work / name)

    CASES = [
        case_a_device_is_larger_than_the_disk_under_it,
        case_what_does_not_fit_goes_to_the_store,
        case_everything_survives_a_restart,
    ]


if __name__ == "__main__":
    sys.exit(Cases().run())
