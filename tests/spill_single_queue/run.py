#!/usr/bin/env python3
"""Exercise encrypted spill through a real ublk queue (requires sudo and ublk_drv).

Build ublk-backend, then run with UBLK_BACKEND_BIN pointing to that binary.
The temporary device is nonpersistent; restarting it is not a recovery test.
"""
import base64
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time


def main():
    root = Path(__file__).resolve().parents[2]
    binary = Path(os.environ.get("UBLK_BACKEND_BIN", root / "target/debug/ublk-backend")).resolve()
    subprocess.run(["sudo", "-n", "modprobe", "ublk_drv"], check=True)
    with tempfile.TemporaryDirectory(prefix="ubiblk-single-queue-") as temporary:
        work = Path(temporary)
        (work / "hot.raw").write_bytes(bytes(64 * 1024))
        key = base64.b64encode(os.urandom(64)).decode()
        (work / "config.toml").write_text(f'''[device]
data_path = "hot.raw"
stripe_sector_count_shift = 6
[encryption]
xts_key.ref = "key"
[secrets.key]
source.inline = "{key}"
encoding = "base64"
[danger_zone]
enabled = true
allow_inline_plaintext_secrets = true
[tuning]
num_queues = 1
queue_size = 64
seg_size_max = 65536
[spill]
size_mb = 1
[spill.store]
storage = "filesystem"
path = "cold"
''')
        link = work / "device"
        with (work / "backend.log").open("w+") as log:
            process = subprocess.Popen(
                ["sudo", "-n", str(binary), "--config", str(work / "config.toml"),
                 "--device-symlink", str(link)], stdout=log, stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            try:
                deadline = time.monotonic() + 45
                while not link.exists():
                    if process.poll() is not None or time.monotonic() >= deadline:
                        raise RuntimeError("ublk device did not become ready")
                    time.sleep(0.1)
                node = link.resolve()
                queue = Path("/sys/block") / node.name / "queue"
                assert int((queue / "chunk_sectors").read_text()) == 64
                assert int((queue / "max_sectors_kb").read_text()) <= 32
                pattern = os.urandom(1024 * 1024)
                (work / "pattern").write_bytes(pattern)
                # A frontend request larger than a stripe must be split by the
                # kernel, never by SpillIoChannel.
                subprocess.run(["sudo", "-n", "dd", f"if={work / 'pattern'}", f"of={node}",
                                "bs=1M", "count=1", "oflag=direct", "status=none"], check=True, timeout=30)
                read = subprocess.run(["sudo", "-n", "dd", f"if={node}", "bs=1M", "count=1",
                                       "iflag=direct", "status=none"], check=True, capture_output=True, timeout=30)
                assert read.stdout == pattern
                assert any(p.is_file() for p in (work / "cold").rglob("*"))
                print("PASS: encrypted one-queue spill, kernel stripe splitting, eviction and refetch")
            finally:
                if process.poll() is None:
                    subprocess.run(["sudo", "-n", "kill", f"-{signal.SIGINT.value}", "--", f"-{process.pid}"], check=False)
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        subprocess.run(["sudo", "-n", "kill", "-9", "--", f"-{process.pid}"], check=False)
                        process.wait(timeout=5)
                log.flush()
                log.seek(0)
                print(log.read())
                # Store objects are created by the privileged backend.
                subprocess.run(["sudo", "-n", "rm", "-rf", "--", str(work / "cold")], check=True)


if __name__ == "__main__":
    main()
