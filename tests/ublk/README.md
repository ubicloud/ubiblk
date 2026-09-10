# ublk tests

End-to-end tests that bring up a **real** ublk device over a ubiblk backend and
move data through it. They are written in Python and drive the `ublk-backend`
and `init-metadata` binaries — nothing here is a Rust `cargo test`.

They exist because nothing else covers this path: the unit tests never reach a
kernel, and the blkbench suite drives the vhost-user backend. A change that
stops ublk devices being created at all is otherwise green everywhere.

## What is covered

| Case | What it checks |
|------|----------------|
| `device_appears_with_the_right_size` | A device is created and the kernel reports the size it was configured with. |
| `data_reads_back_as_written` | 64 MiB written through the device reads back unchanged. |
| `shutdown_removes_the_device` | SIGINT takes the device node and its symlink away rather than leaving a node nothing serves. |

## Files

- `run_all.py` — launcher. Checks the binaries and the driver, runs the cases,
  and removes the scratch directory on exit (pass, fail, or cancel).
- `cases.py` — the cases and their `Device` fixture (config via
  `scripts/ubiblk-init`, backend lifecycle, read/write helpers).

## Running locally

Needs root for the ublk control device (the tests use `sudo`) and a kernel with
`ublk_drv`.

```sh
cargo build --bin ublk-backend --bin init-metadata
python3 tests/ublk/run_all.py
```

Override the backend under test with `UBLK_BACKEND_BIN`.
