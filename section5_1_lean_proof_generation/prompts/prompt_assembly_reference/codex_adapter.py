#!/usr/bin/env python3
"""OpenRouter transport adapter: proxy lifecycle and post-run routing audit.

The scientific checker, audit and measurement code are untouched by this file.
Its only job is to make the author session reach `gpt-5.6-sol` through a local
pinning proxy instead of OpenAI directly, and to leave behind evidence of which
upstream actually served each call.

Why a proxy is required rather than plain configuration:

  * The Codex CLI cannot express OpenRouter's `provider` routing field, and this
    model is served by seven endpoints across OpenAI, Azure and Amazon Bedrock.
    Unpinned, a 90-minute session can drift between them mid-run.
  * Account-wide ignored-provider settings are organization-scoped and not
    available to this account, so pinning has to happen per request.
  * Keeping the credential here keeps it out of the author process environment.
"""
from __future__ import annotations

import json
import os
import secrets
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

CONTROL = Path(__file__).resolve().parent
PROXY = CONTROL / "openrouter_proxy.py"
VERIFIER = CONTROL / "verify_routing.py"
STARTUP_TIMEOUT = 20.0


class ProxyError(RuntimeError):
    pass


class OpenRouterProxy:
    """Context manager owning the local pinning proxy for one author session.

    Entering starts the proxy and blocks until its port accepts connections, so
    the author process never races a half-started transport. Exiting stops it.
    """

    def __init__(self, data: dict, logs: Path):
        self.port = int(data["proxy_port"])
        self.key_file = Path(data["openrouter_key_file"]).expanduser()
        self.logs = logs
        self.request_log = logs / "proxy_requests.jsonl"
        self.token_file = logs / "proxy_token"
        self.local_token = "local-" + secrets.token_hex(16)
        self._proc = None

    # -- pre-launch checks -------------------------------------------------
    @staticmethod
    def precheck(data: dict) -> None:
        """Validate transport prerequisites BEFORE the run commits any state.

        The controller refuses to reuse a packet once `logs/<run>` exists, so a
        transport fault discovered after that point would lock the run out
        permanently. Everything checkable without starting the author session is
        therefore checked here.
        """
        for script in (PROXY, VERIFIER):
            if not script.is_file():
                raise ProxyError("missing transport script: %s" % script)
        key_file = Path(data["openrouter_key_file"]).expanduser()
        if not key_file.is_file():
            raise ProxyError("missing OpenRouter key file: %s" % key_file)
        if not key_file.read_text().strip():
            raise ProxyError("empty OpenRouter key file: %s" % key_file)
        mode = key_file.stat().st_mode & 0o777
        if mode & 0o077:
            raise ProxyError("OpenRouter key file is group/world readable "
                             "(mode %o): %s" % (mode, key_file))
        port = int(data["proxy_port"])
        with socket.socket() as probe:
            probe.settimeout(0.3)
            if probe.connect_ex(("127.0.0.1", port)) == 0:
                raise ProxyError("port %d already in use" % port)
        expected = "http://127.0.0.1:%d/v1" % port
        if data["proxy_base_url"] != expected:
            raise ProxyError("proxy_base_url %r does not match proxy_port %d"
                             % (data["proxy_base_url"], port))

    # -- lifecycle ---------------------------------------------------------
    def __enter__(self):
        if not self.key_file.is_file() or not self.key_file.read_text().strip():
            raise ProxyError("missing OpenRouter key file: %s" % self.key_file)
        if self._listening():
            raise ProxyError("port %d already in use; refusing to attach to an "
                             "unknown proxy" % self.port)
        # 0600 before the token is written; the author process gets the value
        # through its environment, not by reading this file.
        fd = os.open(str(self.token_file), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w") as handle:
            handle.write(self.local_token)

        self._proc = subprocess.Popen(
            [sys.executable, "-B", str(PROXY),
             "--key-file", str(self.key_file),
             "--token-file", str(self.token_file),
             "--log", str(self.request_log),
             "--port", str(self.port)],
            stdin=subprocess.DEVNULL,
            stdout=(self.logs / "proxy.out").open("w"),
            stderr=subprocess.STDOUT,
            start_new_session=True)

        deadline = time.monotonic() + STARTUP_TIMEOUT
        while time.monotonic() < deadline:
            if self._proc.poll() is not None:
                raise ProxyError("proxy exited during startup; see proxy.out")
            if self._listening():
                return self
            time.sleep(0.2)
        self._stop()
        raise ProxyError("proxy did not accept connections within %.0fs" % STARTUP_TIMEOUT)

    def __exit__(self, *_exc):
        self._stop()
        return False  # never swallow an author-session exception

    def _stop(self):
        if self._proc is None or self._proc.poll() is not None:
            return
        try:
            os.killpg(self._proc.pid, signal.SIGTERM)
            self._proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(self._proc.pid, signal.SIGKILL)
            self._proc.wait()
        except ProcessLookupError:
            pass

    def _listening(self) -> bool:
        with socket.socket() as probe:
            probe.settimeout(0.3)
            return probe.connect_ex(("127.0.0.1", self.port)) == 0

    # -- evidence ----------------------------------------------------------
    def audit(self, logs: Path) -> dict:
        """Resolve every author model call to the upstream that served it.

        A failure here is recorded, never raised: the author session has already
        finished and its result must not be discarded because an audit lookup
        failed. `pass` is false unless every call was verifiably OpenAI.
        """
        out = logs / "ROUTING_AUDIT.json"
        if not self.request_log.is_file():
            return {"pass": False, "error": "no proxy request log"}
        try:
            proc = subprocess.run(
                [sys.executable, "-B", str(VERIFIER),
                 "--log", str(self.request_log),
                 "--key-file", str(self.key_file),
                 "--out", str(out)],
                stdin=subprocess.DEVNULL, text=True, capture_output=True, timeout=600)
        except subprocess.TimeoutExpired:
            return {"pass": False, "error": "routing audit timed out"}
        summary = {"exit_code": proc.returncode, "stdout": proc.stdout[-4000:]}
        if out.is_file():
            try:
                record = json.loads(out.read_text())
                summary.update({"pass": bool(record.get("pass")),
                                "calls": record.get("calls"),
                                "providers": record.get("providers"),
                                "unverifiable": record.get("unverifiable"),
                                "total_upstream_usd": record.get("total_upstream_usd")})
            except ValueError:
                summary["pass"] = False
        else:
            summary["pass"] = False
        return summary
