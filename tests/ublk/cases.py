"""ublk test cases, in Python.

Brings up a real ublk device over a ubiblk backend and exercises it end to end.
Normally run via run_all.py, which checks the binaries and the driver first.
Each case gets its own device, so one that leaves the kernel unhappy cannot
quietly break the next.

Binaries default to target/debug; override with UBLK_BACKEND_BIN.
"""

import base64
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
# Longer than the backend's own wait on the kernel, so a wait that is no longer
# bounded shows up here as a failure.
CREATION_TIMEOUT = 60
# ubiblk accepts this depth; ublk does not.
REFUSED_QUEUE_DEPTH = 8192
# Our own wording, not libublk's, so the check does not ride on a dependency.
REPORTED_FAILURE = "Failed to serve ublk backend"

SPILL_DEVICE_MB = 512
SPILL_DISK_MB = 64
SPILL_STRIPE_SECTORS = 2048


def prepare(work, *extra):
    """Lay out a device's files; `extra` goes to ubiblk-init."""
    work.mkdir(parents=True, exist_ok=True)
    # ubiblk-init shells out to init-metadata
    env = dict(os.environ, PATH=f"{BIN_DIR}:{os.environ['PATH']}")
    r(
        "python3",
        str(ROOT / "scripts" / "ubiblk-init"),
        "--size",
        f"{DEVICE_MB}M",
        "--dir",
        str(work),
        "--force",
        *extra,
        env=env,
    )


def prepare_spill(work):
    """Lay out a spill device: 512 MiB over a 64 MiB disk, encrypted."""
    work.mkdir(parents=True, exist_ok=True)
    with open(work / "hot.raw", "wb") as disk:
        disk.truncate(SPILL_DISK_MB * 1024 * 1024)
    key = base64.b64encode(os.urandom(64)).decode()
    (work / "config.toml").write_text(f"""
[device]
data_path = "hot.raw"
device_id = "spill-test"
stripe_sector_count_shift = 11

[encryption]
xts_key.ref = "xts_key"

[secrets.xts_key]
source.inline = "{key}"
encoding = "base64"

[danger_zone]
enabled = true
allow_inline_plaintext_secrets = true

[spill]
size_mb = {SPILL_DEVICE_MB}
max_concurrent_transfers = 4

[spill.store]
storage = "filesystem"
path = "cold"

[tuning]
num_queues = 2
queue_size = 64
seg_size_max = 1048576
""")


class Device:
    """A ubiblk-backed ublk device, for the lifetime of a `with` block."""

    def __init__(self, work, prepare=prepare):
        self.prepare = prepare
        self.work = work
        self.log = work / "backend.log"
        self.symlink = work / "dev"
        self.node = None
        self.backend = None

    def __enter__(self):
        self.prepare(self.work)
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


def case_a_device_the_kernel_refuses_is_reported(suite):
    name = "a_device_the_kernel_refuses_is_reported"
    work = suite.work / name
    # Past the queue depth ublk allows, so the kernel refuses the device. The
    # backend has to say so and exit, rather than wait on one that will never
    # exist.
    prepare(work, "--queue-size", str(REFUSED_QUEUE_DEPTH))
    symlink = work / "dev"
    log = work / "backend.log"

    backend = subprocess.Popen(
        ["sudo", BACKEND, "--config", str(work / "config.toml"),
         "--device-symlink", str(symlink)],
        stdout=log.open("w"),
        stderr=subprocess.STDOUT,
    )
    try:
        status = backend.wait(timeout=CREATION_TIMEOUT)
    except subprocess.TimeoutExpired:
        subprocess.run(["sudo", "kill", "-9", str(backend.pid)], capture_output=True)
        reason = f"still running after {CREATION_TIMEOUT}s instead of giving up"
    else:
        reported = REPORTED_FAILURE in log.read_text(errors="replace")
        if status == 0:
            reason = "exited cleanly though no device was created"
        elif not reported:
            reason = "exited without saying why"
        elif symlink.exists():
            reason = "left a symlink to a device that was never created"
        else:
            reason = None

    if reason is None:
        suite.ok(name)
    else:
        tail = "\n".join(log.read_text(errors="replace").splitlines()[-10:])
        suite.notok(name, f"{reason}\n--- backend log ---\n{tail}")


def case_a_spill_device_is_larger_than_its_disk(suite):
    name = "a_spill_device_is_larger_than_its_disk"
    with suite.spill_device(name) as device:
        size = device.size()
        limit = r("cat", f"/sys/block/{device.node.name}/queue/chunk_sectors").strip()
    if size != SPILL_DEVICE_MB * 1024 * 1024:
        suite.notok(name, f"device is {size} bytes, expected {SPILL_DEVICE_MB} MiB")
    elif limit != str(SPILL_STRIPE_SECTORS):
        suite.notok(name, f"chunk_sectors is {limit}, expected {SPILL_STRIPE_SECTORS}")
    else:
        suite.ok(name)


def case_a_spill_device_keeps_more_than_its_disk_holds(suite):
    name = "a_spill_device_keeps_more_than_its_disk_holds"
    megabytes = 3 * SPILL_DISK_MB
    with suite.spill_device(name) as device:
        pattern = device.work / "pattern"
        pattern.write_bytes(os.urandom(megabytes * 1024 * 1024))
        device.write(pattern, megabytes)
        want = hashlib.md5(pattern.read_bytes()).hexdigest()
        got = device.read_digest(megabytes)
        uploaded = sum(1 for path in (device.work / "cold").rglob("*") if path.is_file())
    if want != got:
        suite.notok(name, "what came back is not what went in")
    elif uploaded < megabytes - SPILL_DISK_MB:
        suite.notok(name, f"only {uploaded} stripes reached the store")
    else:
        suite.ok(name)


def case_a_request_across_stripes_is_split_by_the_kernel(suite):
    name = "a_request_across_stripes_is_split_by_the_kernel"
    with suite.spill_device(name) as device:
        # Four sectors straddling the end of the first stripe.
        data = os.urandom(4 * 512)
        chunk = device.work / "chunk"
        chunk.write_bytes(data)
        seek = SPILL_STRIPE_SECTORS - 2
        r("sudo", "dd", f"if={chunk}", f"of={device.node}", "bs=512", f"seek={seek}",
          "count=4", "oflag=direct", "status=none")
        out = subprocess.run(
            ["sudo", "dd", f"if={device.node}", "bs=512", f"skip={seek}", "count=4",
             "iflag=direct", "status=none"],
            capture_output=True,
        )
    if out.returncode != 0:
        suite.notok(name, f"read failed: {out.stderr.decode(errors='replace')}")
    elif out.stdout != data:
        suite.notok(name, "what came back is not what went in")
    else:
        suite.ok(name)


class Cases(Suite):
    def __init__(self):
        super().__init__()
        self.work = ROOT / "target" / "tests" / "ublk"

    def device(self, name):
        return Device(self.work / name)

    def spill_device(self, name):
        return Device(self.work / name, prepare=prepare_spill)

    CASES = [
        case_device_appears_with_the_right_size,
        case_data_reads_back_as_written,
        case_shutdown_removes_the_device,
        case_a_device_the_kernel_refuses_is_reported,
        case_a_spill_device_is_larger_than_its_disk,
        case_a_spill_device_keeps_more_than_its_disk_holds,
        case_a_request_across_stripes_is_split_by_the_kernel,
    ]


if __name__ == "__main__":
    sys.exit(Cases().run())
