#!/usr/bin/env python3
"""Run the ublk tests (cases.py) against a real ublk device.

Checks the ubiblk binaries are built and the ublk driver is loadable, then runs
the cases and removes the scratch directory afterwards, whether they pass, fail,
or the run is cancelled.

    cargo build --bin ublk-backend --bin init-metadata
    python3 tests/ublk/run_all.py

Needs root for the ublk control device (it uses sudo), and a kernel with
ublk_drv. Override the backend with UBLK_BACKEND_BIN.
"""

import os
import pathlib
import shutil
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "common"))

from harness import install_exit_handler

ROOT = pathlib.Path(__file__).resolve().parents[2]
WORK = ROOT / "target" / "tests" / "ublk"


def check_binaries():
    bin_dir = ROOT / "target" / "debug"
    required = [
        os.environ.get("UBLK_BACKEND_BIN", str(bin_dir / "ublk-backend")),
        str(bin_dir / "init-metadata"),
    ]
    missing = [path for path in required if not os.path.exists(path)]
    if missing:
        sys.exit(
            "missing binaries: " + ", ".join(missing) + "\n"
            "build them first: cargo build --bin ublk-backend --bin init-metadata"
        )


def check_driver():
    if subprocess.run(["sudo", "modprobe", "ublk_drv"], capture_output=True).returncode != 0:
        sys.exit("ublk_drv could not be loaded; these tests need a kernel with ublk")
    if not os.path.exists("/dev/ublk-control"):
        sys.exit("/dev/ublk-control is missing after loading ublk_drv")


def main():
    check_binaries()
    check_driver()

    shutil.rmtree(WORK, ignore_errors=True)
    install_exit_handler(lambda: shutil.rmtree(WORK, ignore_errors=True))

    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    from cases import Cases

    return Cases().run()


if __name__ == "__main__":
    sys.exit(main())
