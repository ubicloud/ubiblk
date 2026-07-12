"""Small command / HTTP helpers, in the spirit of ubicloud's rhizome util.rb."""

import json
import subprocess
import urllib.request


class CommandFail(RuntimeError):
    """Raised by ``r`` when a command exits with an unexpected status.

    Carries both output streams so the failure is easy to diagnose.
    """

    def __init__(self, message, stdout, stderr):
        super().__init__(message)
        self.stdout = stdout
        self.stderr = stderr

    def __str__(self):
        return "\n".join(
            [super().__str__(), "---STDOUT---", self.stdout or "", "---STDERR---", self.stderr or ""]
        )


def r(*command, stdin="", expect=(0,), env=None):
    """Run ``command`` (an argv list), returning its stdout.

    Mirrors ubicloud rhizome's ``r``: it raises :class:`CommandFail` (with both
    streams) when the exit code is not in ``expect``, so callers can stay linear
    and let failures surface loudly.
    """
    p = subprocess.run(command, input=stdin, capture_output=True, text=True, env=env)
    if p.returncode not in expect:
        joined = " ".join(command)
        raise CommandFail(f"command failed ({p.returncode}): {joined}", p.stdout, p.stderr)
    return p.stdout


def toml_dump(tables):
    """Render an ordered list of ``(header, {key: value})`` tables as TOML.

    Keys are emitted verbatim, so dotted keys like ``"source.env"`` work.
    Values may be str, int, or bool. Tables are separated by a blank line.
    """
    blocks = []
    for header, pairs in tables:
        lines = [f"[{header}]"]
        lines += [f"{key} = {_toml_value(value)}" for key, value in pairs.items()]
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks) + "\n"


def _toml_value(value):
    if isinstance(value, bool):  # bool before int: bool is a subclass of int
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value)  # TOML basic-string escaping matches JSON for our values
    raise TypeError(f"unsupported TOML value: {value!r}")


def http(method, url, token=None, body=None, timeout=15):
    """Make an HTTP request and return the response body as text.

    ``body`` (a dict) is sent as JSON. ``token`` is sent as a bearer token.
    """
    headers = {}
    data = None
    if token is not None:
        headers["Authorization"] = f"Bearer {token}"
    if body is not None:
        data = json.dumps(body).encode()
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read().decode()
