# Remote-stripe integration tests

End-to-end tests for the remote stripe protocol's robustness. They stand up a
real `remote-stripe-server` serving a random image, drive the
`remote-stripe-shell` client against it, and inject faults in between to check
the protocol behaves — reads stay correct, latency is tolerated, the client
reconnects after a dropped connection, and the server survives broken sessions.
They are written in Python and drive the `remote-stripe-server` and
`remote-stripe-shell` binaries — nothing here is a Rust `cargo test`.

Fault injection (latency, connection drops, resets) is done with
[toxiproxy](https://github.com/Shopify/toxiproxy), a TCP MITM proxy placed
between the client and the server: the launcher starts it on a loopback port,
points the client at it, and the cases toggle faults through its admin API.

Everything is local — the server, the proxy, and the client all run on
loopback — so unlike the S3 integration tests there are **no credentials or
external services**, and the suite always runs.

## What is covered

| Case | What it checks |
|------|----------------|
| `baseline_fetch_matches_source` | With no faults, fetched stripe bytes match the served image. |
| `fetch_tolerates_latency` | Injected latency (well under the timeouts) does not break a fetch. |
| `reconnect_after_connection_drop` | With `--reconnect`, a fetch whose connection was dropped reconnects (with backoff) once the server is reachable again and returns the right bytes. |
| `no_reconnect_fails_after_drop` | Without `--reconnect`, a dropped connection is not recovered — confirming the drop is real and that reconnect is what recovers it. |
| `server_survives_broken_sessions` | A peer resetting mid-protocol ends only its own session; the server keeps serving. |
| `unreachable_server_fails_fast` | With the server unreachable the client fails to start rather than hanging. |
| `read_timeout_aborts_stalled_fetch` | With a short `operation_attempt_timeout_ms`, a `timeout` toxic that stalls the response aborts the read promptly instead of hanging. |

## Files

- `run_all.py` — launcher. Builds the fixture (a random image and the server /
  client configs), starts `remote-stripe-server` and toxiproxy, puts the proxy
  in front of the server, points the cases at it, and tears everything down on
  exit (pass, fail, or cancel).
- `cases.py` — the test cases and their harness (the `Shell` driver and the
  toxiproxy fault-injection helpers).
- `util.py` — small command/HTTP helpers, notably `r` (run a command, raise on
  failure, return stdout), in the spirit of ubicloud's rhizome `util.rb`.

## Running locally

Build the two binaries once, then run the launcher; it takes care of the server,
the proxy, and cleanup:

```sh
cargo build --bin remote-stripe-server --bin remote-stripe-shell

python3 tests/remote-stripe-integration/run_all.py
```

The launcher does not build for you: it exits early if the binaries are missing.

### Requirements

- `toxiproxy-server` on `PATH` (or pointed to via `TOXIPROXY_BIN`) — download a
  release binary from <https://github.com/Shopify/toxiproxy/releases>.
- `cargo` and `python3`.

Optional: `SERVER_BIN` / `SHELL_BIN` if the ubiblk binaries are not in
`target/debug`.

## CI

`.github/workflows/remote-stripe-integration.yaml` runs the launcher on pushes
to `main`, pull requests, and manual dispatch. It needs no secrets, so it runs
on every PR, including from forks.
