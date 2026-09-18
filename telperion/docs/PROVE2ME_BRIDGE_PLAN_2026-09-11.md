# Prove2Me Solver Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Telperion an autonomous, certificate-first solver agent for prove2.me — triage open milestones against the emitter registry, prove the certificate-shaped ones, and submit them through a hard local-verification gate.

**Architecture:** A new `telperion/src/telperion/prove2me/` subpackage (api client / workspace / triage / attempt), surfaced as `telperion p2m …` CLI subcommands and `p2m_*` MCP tools, orchestrated by a new `prove2me-solver` claude-plugin skill. All network writes flow through one audited client with a version gate, throttle, and circuit breaker.

**Tech Stack:** Python 3 stdlib only for HTTP (`urllib.request` — repo has no requests/httpx dependency and we add none), sympy via the existing Telperion pipeline, Lean 4 + Mathlib pinned to the platform's toolchain, pytest.

**Spec:** `telperion/docs/PROVE2ME_BRIDGE_DESIGN_2026-09-11.md` (read it first; this plan implements it section by section).

## Global Constraints

- **No new runtime dependencies.** HTTP via stdlib `urllib.request`. (`pyproject.toml` dependencies stay `["sympy>=1.12"]`.)
- **No floats in certificate paths** — `fractions.Fraction` / exact sympy only (repo-wide rule).
- **Platform toolchains:** Lean `4.33.1`, `4.30.0`, `4.29.0-rc3` only; we target **4.33.1**. Telperion's own examples stay on `v4.32.0`; the two pins never mix.
- **Platform submission rules:** submitted theorem is named `solution`, matches `formal_statement` binders exactly, contains no `sorry`, never imports its own target theorem.
- **Circuit breaker default: 5** consecutive server errors halts the loop. Client-side throttle: ≥1.0s between requests.
- **Credentials/tokens live in `$HOME/prove2me_workspace/`**, never in this repo. Nothing under `telperion/` may contain a key.
- Commit messages follow repo style: `feat(prove2me): …`, `test(prove2me): …`, `docs(prove2me): …`.
- Run tests from `telperion/`: `python3 -m pytest tests/test_prove2me_*.py -v`. Tests never touch the network (transport injection only).

## File Structure

```
telperion/src/telperion/prove2me/
├── __init__.py          # public re-exports
├── api.py               # Prove2MeClient, transport, errors, throttle, breaker, version gate
├── workspace.py         # $HOME/prove2me_workspace mgmt, tokens, scratch Lean projects, lift scaffold
├── triage.py            # statement features, SHAPE_RULES, registry cross-check, ranking, queue
├── attempt.py           # invariants I1–I5, solution rendering, lake build gate, submit/poll/annotate
└── ledger.py            # AttemptLedger (append-only jsonl), win rates, no-repeat
telperion/src/telperion/cli.py        # + p2m subcommand tree
telperion/src/telperion/mcp_server.py # + p2m_* tools
telperion/claude-plugin/skills/prove2me-solver/SKILL.md
telperion/examples/prove2me_compat/   # Task 1 compat smoke (4.33.1)
telperion/tests/test_prove2me_api.py
telperion/tests/test_prove2me_workspace.py
telperion/tests/test_prove2me_triage.py
telperion/tests/test_prove2me_attempt.py
telperion/tests/test_prove2me_ledger.py
telperion/tests/fixtures/prove2me/    # recorded API fixtures + golden statement corpus
telperion/docs/vendor/prove2me_skill.md          # vendored platform skill (SKILL_VERSION source)
telperion/docs/vendor/prove2me_mission_solver.md # vendored solver reference
```

All commands below run from `telperion/` inside the repo unless stated.

---

### Task 1: Lean 4.33.1 compat smoke test

De-risks the toolchain assumption before any API work (spec: Implementation order #1). Live-network dev task (not CI).

**Files:**
- Create: `examples/prove2me_compat/README.md`
- Create: `examples/prove2me_compat/generate.py`
- Create: `examples/prove2me_compat/lean/lakefile.toml`
- Create: `examples/prove2me_compat/lean/lean-toolchain`
- Create: `examples/prove2me_compat/lean/Prove2MeCompat.lean`

**Interfaces:**
- Consumes: `examples/bernoulli/generate.py` family (reused verbatim as the known-good family).
- Produces: a green `lake build` under 4.33.1, and the discovered platform Mathlib rev recorded in the README for Task 4.

- [ ] **Step 1: Discover the platform's exact pins.** Fetch their onboarding and workspace to learn the official Mathlib revisions:

```bash
curl -sL https://prove2.me/start.md | tee /tmp/p2m_start.md
# Find the official workspace repo URL in the output, then:
git clone <workspace-repo-url> /tmp/p2m_workspace_probe
cat /tmp/p2m_workspace_probe/lean-toolchain 2>/dev/null || grep -r "lean-toolchain\|mathlib" /tmp/p2m_workspace_probe --include="*.toml" -l | head
```

Record the exact `lean-toolchain` content and mathlib `rev` for 4.33.1 in `examples/prove2me_compat/README.md`. If the workspace repo is not discoverable from start.md, fall back to `leanprover/lean4:v4.33.1` + mathlib tag `v4.33.1` and note the fallback in the README.

- [ ] **Step 2: Write the scratch project.** `lean/lean-toolchain`:

```
leanprover/lean4:v4.33.1
```

`lean/lakefile.toml` (substitute the rev discovered in Step 1):

```toml
name = "Prove2MeCompat"
defaultTargets = ["Prove2MeCompat"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.33.1"

[[lean_lib]]
name = "Prove2MeCompat"
```

`generate.py` — reuse the Bernoulli family under the new pin:

```python
"""Compat smoke: emit the known-good Bernoulli family, build under Lean 4.33.1.

The bridge submits proofs to prove2.me, which accepts only Lean 4.33.1 /
4.30.0 / 4.29.0-rc3.  Telperion examples pin v4.32.0.  This example proves the
emitted tactic cores (ring/positivity/norm_num/linarith) survive the newer pin.
Run:  python3 generate.py && cd lean && lake exe cache get && lake build
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "src"))
sys.path.insert(0, str(HERE.parents[0] / "bernoulli"))

from generate import bernoulli_family, bernoulli_profile, _exact_spot_checks  # noqa: E402
from telperion import DirectPolyaEmitter, certify, emit  # noqa: E402


def main() -> int:
    res = emit(
        certify(bernoulli_family()),
        bernoulli_profile(),
        [DirectPolyaEmitter()],
        _exact_spot_checks(),
        file_name="Prove2MeCompat.lean",
    )
    out = HERE / "lean" / "Prove2MeCompat" / "Prove2MeCompat.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(res.text)
    print(f"emitted {res.n_theorems} theorems -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
```

`lean/Prove2MeCompat.lean`:

```lean
import Prove2MeCompat.Prove2MeCompat
```

(If `examples/bernoulli/generate.py` names its profile/spot-check helpers differently, mirror the actual names — read that file first; do not rename anything in it.)

- [ ] **Step 3: Run the smoke test.**

```bash
cd examples/prove2me_compat && python3 generate.py
cd lean && lake exe cache get && lake build
```

Expected: `lake build` exits 0. If tactic cores break under 4.33.1, STOP — this invalidates a spec assumption; report before continuing (the fix belongs in emitters, not here).

- [ ] **Step 4: Write README** with: purpose, the discovered platform pins (Step 1), the exact commands, and the result. Add `lean/.lake/` to the example's `.gitignore`.

- [ ] **Step 5: Commit** (do NOT commit `.lake/` or emitted build artifacts):

```bash
git add examples/prove2me_compat
git commit -m "feat(prove2me): Lean 4.33.1 compat smoke test (platform pin)"
```

---

### Task 2: Vendor platform docs + `api.py` core (transport, errors, throttle, breaker, version gate)

**Files:**
- Create: `docs/vendor/prove2me_skill.md`, `docs/vendor/prove2me_mission_solver.md`
- Create: `src/telperion/prove2me/__init__.py`, `src/telperion/prove2me/api.py`
- Test: `tests/test_prove2me_api.py`

**Interfaces:**
- Produces (used by every later task):
  - `Prove2MeClient(workspace: Path, base_url: str = DEFAULT_BASE_URL, transport=None, min_interval_s: float = 1.0, breaker_threshold: int = 5, _sleep=time.sleep, _now=time.monotonic)`
  - `client.request(method: str, path: str, json_body: dict | None = None, auth: bool = True) -> dict`
  - Errors: `Prove2MeError`, `AuthError`, `ProtocolDrift`, `RateLimited`, `PlatformDown`
  - `HttpResponse(status: int, body: str)` with `.json()`
  - `SKILL_VERSION: str` module constant
  - transport signature: `transport(method: str, url: str, headers: dict, body: bytes | None) -> HttpResponse`

- [ ] **Step 1: Vendor the platform docs.**

```bash
mkdir -p docs/vendor
curl -sL https://prove2.me/skill.md -o docs/vendor/prove2me_skill.md
curl -sL https://prove2.me/references/mission_solver.md -o docs/vendor/prove2me_mission_solver.md
```

Read `docs/vendor/prove2me_skill.md` and note (a) the `metadata.version` value — this becomes `SKILL_VERSION`; (b) the actual API base URL and exact endpoint paths/payload field names. **The vendored file is the authority for request/response shapes; where this plan's field names differ, follow the vendored doc and keep the plan's function names.**

- [ ] **Step 2: Write the failing tests** (`tests/test_prove2me_api.py`):

```python
"""Prove2MeClient core: transport injection, auth gate, throttle, breaker."""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.api import (  # noqa: E402
    SKILL_VERSION,
    AuthError,
    HttpResponse,
    PlatformDown,
    ProtocolDrift,
    Prove2MeClient,
    RateLimited,
)


def make_client(tmp_path, responses, **kw):
    """Client with a scripted transport; records every request it makes."""
    calls = []

    def transport(method, url, headers, body):
        calls.append((method, url, headers, body))
        r = responses.pop(0)
        return r if isinstance(r, HttpResponse) else HttpResponse(*r)

    slept = []
    c = Prove2MeClient(
        workspace=tmp_path,
        transport=transport,
        _sleep=slept.append,
        _now=lambda: 0.0,
        **kw,
    )
    return c, calls, slept


def ok(payload):
    return HttpResponse(200, json.dumps(payload))


def test_request_returns_parsed_json(tmp_path):
    c, calls, _ = make_client(tmp_path, [ok({"hello": "world"})])
    out = c.request("GET", "/missions", auth=False)
    assert out == {"hello": "world"}
    assert calls[0][0] == "GET" and calls[0][1].endswith("/missions")


def test_version_gate_raises_protocol_drift(tmp_path):
    bad = ok({"version": SKILL_VERSION + "-newer", "access_token": "t"})
    c, _, _ = make_client(tmp_path, [bad])
    with pytest.raises(ProtocolDrift):
        c._check_version(bad.json())


def test_401_raises_auth_error(tmp_path):
    c, _, _ = make_client(tmp_path, [HttpResponse(401, "{}")])
    with pytest.raises(AuthError):
        c.request("GET", "/missions", auth=False)


def test_429_raises_rate_limited_after_retries(tmp_path):
    c, calls, slept = make_client(
        tmp_path, [HttpResponse(429, "{}")] * 4
    )
    with pytest.raises(RateLimited):
        c.request("GET", "/missions", auth=False)
    assert len(calls) == 4          # initial + 3 backoff retries
    assert len(slept) >= 3          # backoff sleeps happened


def test_breaker_halts_after_5_consecutive_5xx(tmp_path):
    c, _, _ = make_client(tmp_path, [HttpResponse(500, "{}")] * 40)
    for _ in range(5):
        with pytest.raises(PlatformDown):
            c.request("GET", "/missions", auth=False)
    with pytest.raises(PlatformDown, match="circuit breaker"):
        c.request("GET", "/missions", auth=False)


def test_breaker_resets_on_success(tmp_path):
    seq = [HttpResponse(500, "{}")] * 4 + [ok({}), HttpResponse(500, "{}")]
    c, _, _ = make_client(tmp_path, list(seq))
    for _ in range(4):
        with pytest.raises(PlatformDown):
            c.request("GET", "/missions", auth=False)
    c.request("GET", "/missions", auth=False)   # success resets counter
    with pytest.raises(PlatformDown):
        c.request("GET", "/missions", auth=False)  # count restarts at 1, no halt
```

- [ ] **Step 3: Run to verify failure.** `python3 -m pytest tests/test_prove2me_api.py -v` — Expected: FAIL, `ModuleNotFoundError: telperion.prove2me`.

- [ ] **Step 4: Implement.** `src/telperion/prove2me/__init__.py`:

```python
"""Prove2Me solver bridge: Telperion as a certificate-first agent for prove2.me.

Design: docs/PROVE2ME_BRIDGE_DESIGN_2026-09-11.md.  All network writes flow
through api.Prove2MeClient — one audited module with a version gate, throttle,
and circuit breaker.  Credentials/tokens live in $HOME/prove2me_workspace,
never in this repo.
"""
from .api import (  # noqa: F401
    AuthError,
    HttpResponse,
    PlatformDown,
    ProtocolDrift,
    Prove2MeClient,
    Prove2MeError,
    RateLimited,
    SKILL_VERSION,
)
```

`src/telperion/prove2me/api.py`:

```python
"""HTTP client for prove2.me.  stdlib urllib only — no new dependencies.

Safety properties of an AUTONOMOUS agent live here, not in callers:
  * version gate  — server `version` != SKILL_VERSION => ProtocolDrift
  * throttle      — >= min_interval_s between any two requests
  * backoff       — 429/5xx retried with exponential backoff (3 retries)
  * breaker       — breaker_threshold consecutive 5xx halts ALL further calls
"""
from __future__ import annotations

import json
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path

# Update whenever docs/vendor/prove2me_skill.md is re-vendored (spec §api.py).
# Value comes from that file's metadata.version.
SKILL_VERSION = "SET-FROM-VENDORED-SKILL-MD"

DEFAULT_BASE_URL = "https://prove2.me/api"  # confirm against vendored skill.md
_RETRIES = 3


class Prove2MeError(Exception):
    """Base class for all bridge errors."""


class AuthError(Prove2MeError):
    """401/403, or auth chain not established."""


class ProtocolDrift(Prove2MeError):
    """Server skill version != ours: refetch https://prove2.me/skill.md."""


class RateLimited(Prove2MeError):
    """429 persisted through backoff."""


class PlatformDown(Prove2MeError):
    """5xx (single) or circuit breaker open (repeated)."""


@dataclass(frozen=True)
class HttpResponse:
    status: int
    body: str

    def json(self) -> dict:
        return json.loads(self.body) if self.body else {}


def _urllib_transport(method: str, url: str, headers: dict, body: bytes | None) -> HttpResponse:
    req = urllib.request.Request(url, data=body, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            return HttpResponse(resp.status, resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        return HttpResponse(e.code, e.read().decode("utf-8", errors="replace"))


class Prove2MeClient:
    def __init__(
        self,
        workspace: Path,
        base_url: str = DEFAULT_BASE_URL,
        transport=None,
        min_interval_s: float = 1.0,
        breaker_threshold: int = 5,
        _sleep=time.sleep,
        _now=time.monotonic,
    ):
        self.workspace = Path(workspace)
        self.base_url = base_url.rstrip("/")
        self._transport = transport or _urllib_transport
        self._min_interval = min_interval_s
        self._breaker_threshold = breaker_threshold
        self._consecutive_5xx = 0
        self._last_request_at: float | None = None
        self._sleep = _sleep
        self._now = _now
        self.access_token: str | None = None

    # -- core ---------------------------------------------------------------

    def request(self, method: str, path: str, json_body: dict | None = None, auth: bool = True) -> dict:
        if self._consecutive_5xx >= self._breaker_threshold:
            raise PlatformDown(
                f"circuit breaker open after {self._consecutive_5xx} consecutive "
                f"server errors; halt the loop and investigate before resetting"
            )
        headers = {"Content-Type": "application/json", "User-Agent": "telperion-p2m"}
        if auth:
            if not self.access_token:
                raise AuthError("no access token: run the auth chain first")
            headers["Authorization"] = f"Bearer {self.access_token}"
        body = json.dumps(json_body).encode() if json_body is not None else None

        resp: HttpResponse | None = None
        for attempt in range(_RETRIES + 1):
            self._throttle()
            resp = self._transport(method, self.base_url + path, headers, body)
            if resp.status not in (429,) and resp.status < 500:
                break
            if attempt < _RETRIES:
                self._sleep(2.0 * 2 ** attempt)
        assert resp is not None

        if resp.status == 429:
            raise RateLimited(f"{method} {path}: still 429 after {_RETRIES} retries")
        if resp.status >= 500:
            self._consecutive_5xx += 1
            raise PlatformDown(f"{method} {path}: HTTP {resp.status}")
        self._consecutive_5xx = 0
        if resp.status in (401, 403):
            raise AuthError(f"{method} {path}: HTTP {resp.status}: {resp.body[:200]}")
        if resp.status >= 400:
            raise Prove2MeError(f"{method} {path}: HTTP {resp.status}: {resp.body[:500]}")
        return resp.json()

    def _throttle(self) -> None:
        now = self._now()
        if self._last_request_at is not None:
            wait = self._min_interval - (now - self._last_request_at)
            if wait > 0:
                self._sleep(wait)
        self._last_request_at = self._now()

    def _check_version(self, payload: dict) -> None:
        v = payload.get("version")
        if v is not None and v != SKILL_VERSION:
            raise ProtocolDrift(
                f"platform skill version {v!r} != ours {SKILL_VERSION!r}: "
                f"re-vendor https://prove2.me/skill.md and update SKILL_VERSION"
            )
```

Set `SKILL_VERSION` to the actual value from Step 1's vendored file.

- [ ] **Step 5: Run to verify pass.** `python3 -m pytest tests/test_prove2me_api.py -v` — Expected: all PASS.

- [ ] **Step 6: Commit.**

```bash
git add docs/vendor src/telperion/prove2me tests/test_prove2me_api.py
git commit -m "feat(prove2me): api client core -- transport, throttle, breaker, version gate"
```

---

### Task 3: `api.py` auth chain + endpoint wrappers

**Files:**
- Modify: `src/telperion/prove2me/api.py`
- Test: `tests/test_prove2me_api.py` (extend)

**Interfaces:**
- Consumes: Task 2's `Prove2MeClient.request`, `_check_version`.
- Produces (used by triage/attempt/CLI):
  - `client.login(email: str, password: str) -> None` (stores session token on self)
  - `client.mint_api_key() -> str` (POST /agent/api-key; persists to tokens file; returns key)
  - `client.refresh() -> None` (POST /agent/refresh with api key; sets `self.access_token`; persists)
  - `client.ensure_auth() -> None` (loads persisted key, refreshes if token missing/expired)
  - `client.missions() -> list[dict]`, `client.milestones(mission_id: str) -> list[dict]`
  - `client.theorem(theorem_id: str) -> dict`, `client.theorem_graph(theorem_id: str) -> dict`
  - `client.theorem_submissions(theorem_id: str) -> list[dict]`
  - `client.milestone_history(milestone_id: str) -> list[dict]`
  - `client.verify(lean_source: str, target_id: str, private: bool = False) -> str` (returns submission_id)
  - `client.verdict(submission_id: str) -> dict`
  - `client.annotate(submission_id: str, explanation: str) -> None`
  - `client.comment(mission_id: str, text: str) -> None`, `client.rate(target_id: str, payload: dict) -> None`
  - `client.submit_problem(payload: dict) -> dict`, `client.submit_definition(payload: dict) -> dict`
  - Token persistence file: `<workspace>/telperion_tokens.json` (`{"api_key": ..., "api_key_expires": iso, "access_token": ..., "access_expires": iso}`)

- [ ] **Step 1: Write the failing tests** (append to `tests/test_prove2me_api.py`):

```python
def test_auth_chain_persists_key_and_token(tmp_path):
    responses = [
        ok({"version": SKILL_VERSION, "session_token": "sess"}),          # /login
        ok({"api_key": "KEY30", "expires_at": "2026-10-11T00:00:00Z"}),   # /agent/api-key
        ok({"version": SKILL_VERSION, "access_token": "HOURLY",
            "expires_at": "2026-09-11T13:00:00Z"}),                        # /agent/refresh
    ]
    c, calls, _ = make_client(tmp_path, responses)
    c.login("me@example.com", "pw")
    c.mint_api_key()
    c.refresh()
    assert c.access_token == "HOURLY"
    saved = json.loads((tmp_path / "telperion_tokens.json").read_text())
    assert saved["api_key"] == "KEY30"
    # every auth response was version-gated: drift in any would have raised


def test_login_version_drift_refuses(tmp_path):
    c, _, _ = make_client(
        tmp_path, [ok({"version": "other", "session_token": "s"})]
    )
    with pytest.raises(ProtocolDrift):
        c.login("me@example.com", "pw")


def test_verify_returns_submission_id_and_verdict_polls(tmp_path):
    c, calls, _ = make_client(
        tmp_path,
        [ok({"submission_id": "sub1"}), ok({"status": "Proved"})],
    )
    c.access_token = "t"
    sid = c.verify("theorem solution : 1 = 1 := rfl", target_id="thm9")
    assert sid == "sub1"
    assert c.verdict("sub1")["status"] == "Proved"
    assert calls[0][0] == "POST" and "/verify" in calls[0][1]
    assert calls[1][0] == "GET" and "submission_id=sub1" in calls[1][1]


def test_ensure_auth_uses_persisted_key(tmp_path):
    (tmp_path / "telperion_tokens.json").write_text(json.dumps(
        {"api_key": "KEY30", "api_key_expires": "2099-01-01T00:00:00Z"}
    ))
    c, calls, _ = make_client(
        tmp_path,
        [ok({"version": SKILL_VERSION, "access_token": "T2",
             "expires_at": "2099-01-01T01:00:00Z"})],
    )
    c.ensure_auth()
    assert c.access_token == "T2"
```

- [ ] **Step 2: Run to verify failure.** Expected: FAIL, `AttributeError: 'Prove2MeClient' object has no attribute 'login'`.

- [ ] **Step 3: Implement** (append to the class in `api.py`; adjust endpoint paths/payload field names to the vendored `docs/vendor/prove2me_skill.md` where they differ — function names stay as below):

```python
    # -- auth chain (credentials -> 30-day key -> hourly token) -------------

    @property
    def _tokens_path(self) -> Path:
        return self.workspace / "telperion_tokens.json"

    def _load_tokens(self) -> dict:
        if self._tokens_path.exists():
            return json.loads(self._tokens_path.read_text())
        return {}

    def _save_tokens(self, updates: dict) -> None:
        doc = self._load_tokens()
        doc.update(updates)
        self.workspace.mkdir(parents=True, exist_ok=True)
        self._tokens_path.write_text(json.dumps(doc, indent=1) + "\n")

    def login(self, email: str, password: str) -> None:
        out = self.request("POST", "/login",
                           {"email": email, "password": password}, auth=False)
        self._check_version(out)
        self._session_token = out.get("session_token") or out.get("token")

    def mint_api_key(self) -> str:
        headers_token = getattr(self, "_session_token", None)
        if not headers_token:
            raise AuthError("login first: mint_api_key needs a session token")
        self.access_token = headers_token          # session token authorizes minting
        out = self.request("POST", "/agent/api-key", {})
        self.access_token = None
        self._save_tokens({"api_key": out["api_key"],
                           "api_key_expires": out.get("expires_at", "")})
        return out["api_key"]

    def refresh(self) -> None:
        key = self._load_tokens().get("api_key")
        if not key:
            raise AuthError("no api key: run login + mint_api_key (or paste one "
                            "from account settings into telperion_tokens.json)")
        out = self.request("POST", "/agent/refresh", {"api_key": key}, auth=False)
        self._check_version(out)
        self.access_token = out["access_token"]
        self._save_tokens({"access_token": self.access_token,
                           "access_expires": out.get("expires_at", "")})

    def ensure_auth(self) -> None:
        if self.access_token:
            return
        saved = self._load_tokens()
        self.access_token = saved.get("access_token") or None
        if not self.access_token:
            self.refresh()

    # -- endpoints ----------------------------------------------------------

    def missions(self) -> list:
        out = self.request("GET", "/missions")
        return out if isinstance(out, list) else out.get("missions", [])

    def milestones(self, mission_id: str) -> list:
        out = self.request("GET", f"/missions/{mission_id}/milestones")
        return out if isinstance(out, list) else out.get("milestones", [])

    def theorem(self, theorem_id: str) -> dict:
        return self.request("GET", f"/theorems/{theorem_id}")

    def theorem_graph(self, theorem_id: str) -> dict:
        return self.request("GET", f"/theorems/{theorem_id}/graph")

    def theorem_submissions(self, theorem_id: str) -> list:
        out = self.request("GET", f"/theorems/{theorem_id}/submissions")
        return out if isinstance(out, list) else out.get("submissions", [])

    def milestone_history(self, milestone_id: str) -> list:
        out = self.request("GET", f"/milestones/{milestone_id}/history")
        return out if isinstance(out, list) else out.get("history", [])

    def verify(self, lean_source: str, target_id: str, private: bool = False) -> str:
        payload = {"target_id": target_id, "source": lean_source}
        if private:
            payload["private"] = True
        out = self.request("POST", "/verify", payload)
        return out["submission_id"]

    def verdict(self, submission_id: str) -> dict:
        return self.request("GET", f"/verify?submission_id={submission_id}")

    def annotate(self, submission_id: str, explanation: str) -> None:
        self.request("PATCH", f"/submissions/{submission_id}",
                     {"explanation": explanation})

    def comment(self, mission_id: str, text: str) -> None:
        self.request("POST", f"/missions/{mission_id}/comments", {"text": text})

    def rate(self, target_id: str, payload: dict) -> None:
        self.request("POST", "/rate", {"target_id": target_id, **payload})

    def submit_problem(self, payload: dict) -> dict:
        return self.request("POST", "/submit-problem", payload)

    def submit_definition(self, payload: dict) -> dict:
        return self.request("POST", "/submit-definition", payload)

    def publish_jobs(self) -> list:
        out = self.request("GET", "/publish-jobs")
        return out if isinstance(out, list) else out.get("jobs", [])
```

- [ ] **Step 4: Run to verify pass.** `python3 -m pytest tests/test_prove2me_api.py -v` — all PASS.

- [ ] **Step 5: Commit.** `git add -A src/telperion/prove2me tests/test_prove2me_api.py && git commit -m "feat(prove2me): auth chain and typed endpoint wrappers"`

---

### Task 4: `workspace.py` — workspace sync, toolchain pin, scratch projects, lift scaffold

**Files:**
- Create: `src/telperion/prove2me/workspace.py`
- Test: `tests/test_prove2me_workspace.py`

**Interfaces:**
- Consumes: nothing from other bridge modules (pure filesystem + subprocess).
- Produces:
  - `Workspace(root: Path = Path.home() / "prove2me_workspace")`
  - `ws.ensure_layout() -> None` (creates `Definitions/ Theorems/ Solutions/ attempts/`, writes `.gitignore` covering `credentials.json`, `telperion_tokens.json`, `.lake/`)
  - `ws.scratch_project(name: str, toolchain: str, mathlib_rev: str) -> Path` (materializes `attempts/<name>/lean/{lakefile.toml,lean-toolchain,<Name>.lean}`; returns project dir)
  - `ws.scaffold_lift(milestone_id: str, formal_statement: str, name: str) -> Path` (writes `attempts/<name>/family.py` lift stub with the verbatim statement embedded)
  - `PLATFORM_TOOLCHAIN = "leanprover/lean4:v4.33.1"`, `PLATFORM_MATHLIB_REV` (from Task 1's discovery)

- [ ] **Step 1: Write the failing tests** (`tests/test_prove2me_workspace.py`):

```python
"""Workspace layout, scratch Lean projects, lift scaffolding."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.workspace import (  # noqa: E402
    PLATFORM_TOOLCHAIN,
    Workspace,
)


def test_ensure_layout_creates_dirs_and_gitignores_secrets(tmp_path):
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    for d in ("Definitions", "Theorems", "Solutions", "attempts"):
        assert (tmp_path / "wsp" / d).is_dir()
    gi = (tmp_path / "wsp" / ".gitignore").read_text()
    assert "credentials.json" in gi and "telperion_tokens.json" in gi


def test_scratch_project_pins_platform_toolchain(tmp_path):
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    proj = ws.scratch_project("M123", toolchain=PLATFORM_TOOLCHAIN,
                              mathlib_rev="v4.33.1")
    assert (proj / "lean-toolchain").read_text().strip() == PLATFORM_TOOLCHAIN
    lakefile = (proj / "lakefile.toml").read_text()
    assert 'rev = "v4.33.1"' in lakefile and "mathlib" in lakefile


def test_scaffold_lift_embeds_verbatim_statement(tmp_path):
    ws = Workspace(root=tmp_path / "wsp")
    ws.ensure_layout()
    stmt = "theorem solution : ∀ x : ℚ, 0 ≤ x^2 := by sorry"
    fam = ws.scaffold_lift("mile42", stmt, name="M42")
    text = fam.read_text()
    assert stmt in text                       # verbatim, for faithfulness review
    assert "InequalityFamily" in text
    assert "mile42" in text
```

- [ ] **Step 2: Run to verify failure.** Expected: FAIL, module not found.

- [ ] **Step 3: Implement** (`src/telperion/prove2me/workspace.py`):

```python
"""$HOME/prove2me_workspace management: layout, scratch Lean projects pinned
to the PLATFORM toolchain (never Telperion's own v4.32.0), and lift stubs.

The scratch project is where an attempt's emitted Lean is compiled BEFORE any
submission (invariant I1).  The lift stub embeds the milestone's
formal_statement VERBATIM so faithfulness is reviewable at a glance.
"""
from __future__ import annotations

import subprocess
from pathlib import Path

# From the platform workspace probe (examples/prove2me_compat/README.md).
PLATFORM_TOOLCHAIN = "leanprover/lean4:v4.33.1"
PLATFORM_MATHLIB_REV = "v4.33.1"   # update from Task 1 discovery if different

_LAKEFILE = """name = "{name}"
defaultTargets = ["{name}"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{mathlib_rev}"

[[lean_lib]]
name = "{name}"
"""

_LIFT_STUB = '''"""Lift of prove2.me milestone {milestone_id} -> Telperion family.

FORMAL STATEMENT (verbatim from the platform -- the kernel checks our theorem
against THIS; keep it untouched for faithfulness review):

{statement_block}

Fill in: symbols, grid (often a single point), target/equation, validation().
A wrong lift fails certify() or the local build -- it cannot reach the platform.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "src"))

import sympy as sp  # noqa: E402

from telperion import GridSpec, InequalityFamily  # noqa: E402
from telperion.workflow import ValidationReport  # noqa: E402

MILESTONE_ID = "{milestone_id}"
FORMAL_STATEMENT = {statement_literal}


def family() -> InequalityFamily:
    x = sp.Symbol("x", nonnegative=True)
    return InequalityFamily(
        name="{name}",
        symbols=(x,),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "solution",
        target=lambda pt: x - x,   # REPLACE with the lifted inequality
    )


def validation() -> ValidationReport:
    return ValidationReport.from_asserts([
        ("replace-with-exact-rational-spot-checks", lambda: None),
    ])
'''


class Workspace:
    def __init__(self, root: Path | None = None):
        self.root = Path(root) if root else Path.home() / "prove2me_workspace"

    def ensure_layout(self) -> None:
        for d in ("Definitions", "Theorems", "Solutions", "attempts"):
            (self.root / d).mkdir(parents=True, exist_ok=True)
        gi = self.root / ".gitignore"
        wanted = "credentials.json\ntelperion_tokens.json\n.lake/\n__pycache__/\n"
        if not gi.exists() or wanted not in gi.read_text():
            gi.write_text((gi.read_text() if gi.exists() else "") + wanted)

    def sync_official(self, repo_url: str) -> None:
        """Clone or pull the official platform workspace repo into root."""
        if (self.root / ".git").exists():
            subprocess.run(["git", "-C", str(self.root), "pull", "--ff-only"],
                           check=True)
        else:
            self.root.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "clone", repo_url, str(self.root)], check=True)
        self.ensure_layout()

    def scratch_project(self, name: str, toolchain: str = PLATFORM_TOOLCHAIN,
                        mathlib_rev: str = PLATFORM_MATHLIB_REV) -> Path:
        if not name.isidentifier():
            raise ValueError(f"scratch project name must be an identifier: {name!r}")
        proj = self.root / "attempts" / name / "lean"
        (proj / name).mkdir(parents=True, exist_ok=True)
        (proj / "lean-toolchain").write_text(toolchain + "\n")
        (proj / "lakefile.toml").write_text(
            _LAKEFILE.format(name=name, mathlib_rev=mathlib_rev))
        (proj / f"{name}.lean").write_text(f"import {name}.{name}\n")
        return proj

    def scaffold_lift(self, milestone_id: str, formal_statement: str,
                      name: str) -> Path:
        d = self.root / "attempts" / name
        d.mkdir(parents=True, exist_ok=True)
        fam = d / "family.py"
        fam.write_text(_LIFT_STUB.format(
            milestone_id=milestone_id,
            name=name,
            statement_block="\n".join("    " + ln for ln in
                                      formal_statement.splitlines()),
            statement_literal=repr(formal_statement),
        ))
        return fam
```

- [ ] **Step 4: Run to verify pass.** `python3 -m pytest tests/test_prove2me_workspace.py -v` — all PASS.

- [ ] **Step 5: Update `PLATFORM_MATHLIB_REV`** with the actual rev recorded in `examples/prove2me_compat/README.md` (Task 1 Step 1). If Task 1 used the fallback, leave `v4.33.1` and note it.

- [ ] **Step 6: Commit.** `git add src/telperion/prove2me/workspace.py tests/test_prove2me_workspace.py && git commit -m "feat(prove2me): workspace layout, platform-pinned scratch projects, lift scaffold"`

---

### Task 5: `ledger.py` — append-only attempt ledger

Built before triage so triage can consume it (spec §5).

**Files:**
- Create: `src/telperion/prove2me/ledger.py`
- Test: `tests/test_prove2me_ledger.py`

**Interfaces:**
- Produces:
  - `AttemptRecord(milestone_id: str, mission_id: str, emitters: tuple[str, ...], lift_hash: str, verdict: str, server_output: str, wall_s: float, submission_id: str, date: str)` (frozen dataclass; `verdict` one of `"Proved" | "Disproved" | "Rejected" | "BuildFailed" | "CertifyRefused" | "DryRun"`)
  - `AttemptLedger(path: Path)` with `.append(rec: AttemptRecord) -> None`, `.records() -> list[AttemptRecord]`, `.attempted(milestone_id: str) -> bool`, `.rejected(milestone_id: str) -> list[AttemptRecord]`, `.win_rate(emitter: str) -> float | None`, `.render_status() -> str`

- [ ] **Step 1: Write the failing tests** (`tests/test_prove2me_ledger.py`):

```python
"""Append-only jsonl attempt ledger: no-repeat rule + emitter win rates."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.ledger import AttemptLedger, AttemptRecord  # noqa: E402


def rec(milestone="m1", verdict="Proved", emitters=("SOSEmitter",)):
    return AttemptRecord(
        milestone_id=milestone, mission_id="mi1", emitters=tuple(emitters),
        lift_hash="abc123", verdict=verdict, server_output="", wall_s=1.5,
        submission_id="s1", date="2026-09-11",
    )


def test_append_and_reload_roundtrip(tmp_path):
    p = tmp_path / "ledger.jsonl"
    led = AttemptLedger(p)
    led.append(rec())
    led2 = AttemptLedger(p)          # fresh read from disk
    assert led2.records() == [rec()]
    assert led2.attempted("m1") and not led2.attempted("m2")


def test_win_rate_per_emitter(tmp_path):
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="Proved"))
    led.append(rec(milestone="m2", verdict="Rejected"))
    led.append(rec(milestone="m3", verdict="Proved", emitters=("WZEmitter",)))
    assert led.win_rate("SOSEmitter") == 0.5
    assert led.win_rate("WZEmitter") == 1.0
    assert led.win_rate("NeverUsedEmitter") is None


def test_rejected_paths_listed_for_no_repeat(tmp_path):
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="Rejected"))
    assert [r.verdict for r in led.rejected("m1")] == ["Rejected"]


def test_dry_runs_do_not_count_as_attempted(tmp_path):
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(rec(verdict="DryRun"))
    assert not led.attempted("m1")
    assert led.win_rate("SOSEmitter") is None
```

- [ ] **Step 2: Run to verify failure.** Expected: FAIL, module not found.

- [ ] **Step 3: Implement** (`src/telperion/prove2me/ledger.py`):

```python
"""Append-only jsonl record of every prove2.me attempt (spec section 5).

Same convention as telperion.ledger.RouteLedger (dead ends as durable data),
but jsonl and keyed for the bridge's three consumers: triage ranking
(win_rate), the no-repeat rule (attempted/rejected), and `p2m status`.
This record shape deliberately seeds sub-project A's mission registry.
"""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path

_WINS = ("Proved", "Disproved")
_LOSSES = ("Rejected", "BuildFailed", "CertifyRefused")


@dataclass(frozen=True)
class AttemptRecord:
    milestone_id: str
    mission_id: str
    emitters: tuple[str, ...]
    lift_hash: str
    verdict: str          # Proved | Disproved | Rejected | BuildFailed | CertifyRefused | DryRun
    server_output: str
    wall_s: float
    submission_id: str
    date: str


class AttemptLedger:
    def __init__(self, path: Path):
        self.path = Path(path)
        self._records: list[AttemptRecord] = []
        if self.path.exists():
            for line in self.path.read_text().splitlines():
                if line.strip():
                    d = json.loads(line)
                    d["emitters"] = tuple(d["emitters"])
                    self._records.append(AttemptRecord(**d))

    def append(self, rec: AttemptRecord) -> None:
        self._records.append(rec)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open("a") as f:
            f.write(json.dumps(asdict(rec)) + "\n")

    def records(self) -> list[AttemptRecord]:
        return list(self._records)

    def attempted(self, milestone_id: str) -> bool:
        return any(r.milestone_id == milestone_id and r.verdict != "DryRun"
                   for r in self._records)

    def rejected(self, milestone_id: str) -> list[AttemptRecord]:
        return [r for r in self._records
                if r.milestone_id == milestone_id and r.verdict in _LOSSES]

    def win_rate(self, emitter: str) -> float | None:
        outcomes = [r.verdict in _WINS for r in self._records
                    if emitter in r.emitters and r.verdict != "DryRun"]
        if not outcomes:
            return None
        return sum(outcomes) / len(outcomes)

    def render_status(self) -> str:
        wins = [r for r in self._records if r.verdict in _WINS]
        lines = [f"attempts: {len(self._records)}  proved: {len(wins)}"]
        for r in self._records[-10:]:
            lines.append(f"  {r.date}  {r.milestone_id:<16} {r.verdict:<14} "
                         f"{','.join(r.emitters)}")
        return "\n".join(lines)
```

- [ ] **Step 4: Run to verify pass.** `python3 -m pytest tests/test_prove2me_ledger.py -v` — all PASS.

- [ ] **Step 5: Commit.** `git add src/telperion/prove2me/ledger.py tests/test_prove2me_ledger.py && git commit -m "feat(prove2me): append-only attempt ledger with win rates and no-repeat"`

---

### Task 6: `triage.py` — statement features, shape rules, registry cross-check, ranking

**Files:**
- Create: `src/telperion/prove2me/triage.py`
- Create: `tests/fixtures/prove2me/golden_statements.json`
- Test: `tests/test_prove2me_triage.py`

**Interfaces:**
- Consumes: `AttemptLedger` (Task 5), `telperion.workflow.Emitter` subclass enumeration.
- Produces:
  - `ShapeRule(feature: str, emitter_classes: tuple[str, ...], pattern: str, weight: float)` — `pattern` is a regex matched against the normalized statement
  - `SHAPE_RULES: tuple[ShapeRule, ...]`
  - `registry_class_names() -> set[str]` (imports every `telperion.emit*` module, walks `Emitter.__subclasses__()` recursively, returns class names)
  - `coverage_report() -> dict` with keys `unknown_rule_classes: list[str]` (rule references a class not in registry — an ERROR) and `unmatched_registry_classes: list[str]` (emitters no rule can select — a NAMED GAP, per repo honesty patterns)
  - `match_statement(formal_statement: str) -> tuple[float, tuple[str, ...]]` — (confidence 0..1, matched emitter class names)
  - `QueueItem(milestone_id: str, mission_id: str, statement: str, emitter_classes: tuple[str, ...], score: float)`
  - `triage(milestones: list[dict], ledger: AttemptLedger | None = None) -> list[QueueItem]` (sorted best-first; skips `ledger.attempted()` ids; milestone dicts use keys `id`, `mission_id`, `formal_statement`, `status` — adjust to vendored field names)
  - `save_queue(items, path) / load_queue(path)` (JSON)

- [ ] **Step 1: Write the golden corpus fixture** (`tests/fixtures/prove2me/golden_statements.json`) — hand-labeled now; extended with real platform statements in Task 10:

```json
{
  "format": "telperion-p2m-golden-v1",
  "note": "Hand-labeled seed corpus. Task 10 appends real statements fetched from completed missions. match=true means stage-1 triage SHOULD select it.",
  "statements": [
    {"id": "g1", "match": true,  "expect_any": ["SOSEmitter", "DirectPolyaEmitter", "PSDFormEmitter"],
     "text": "theorem solution : ∀ x : ℝ, 0 ≤ x^2 - 2*x + 1"},
    {"id": "g2", "match": true,  "expect_any": ["IdentityEmitter", "ExactFactEmitter", "RationalIdentityEmitter"],
     "text": "theorem solution : (3 : ℚ)/4 + 1/4 = 1"},
    {"id": "g3", "match": true,  "expect_any": ["PadicValuationEmitter"],
     "text": "theorem solution : padicValNat 3 405 = 4"},
    {"id": "g4", "match": true,  "expect_any": ["TailNatEmitter", "MonotoneRatioTailEmitter"],
     "text": "theorem solution : ∀ n : ℕ, 5 ≤ n → n^2 ≤ 2^n"},
    {"id": "g5", "match": true,  "expect_any": ["CauchySchwarzEmitter", "TangentSumEmitter", "SOSEmitter"],
     "text": "theorem solution (x y z : ℝ) : (x + y + z)^2 ≤ 3 * (x^2 + y^2 + z^2)"},
    {"id": "g6", "match": true,  "expect_any": ["InfeasibilityEmitter", "SOSRefutationEmitter"],
     "text": "theorem solution : ¬ ∃ x y : ℚ, x^2 + y^2 = -1"},
    {"id": "g7", "match": true,  "expect_any": ["FiniteDecideEmitter", "CaseDispatchAssemblyEmitter"],
     "text": "theorem solution : ∀ n : ℕ, n ≤ 6 → n * (n + 1) % 2 = 0"},
    {"id": "g8", "match": false, "expect_any": [],
     "text": "theorem solution (G : Type*) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹"},
    {"id": "g9", "match": false, "expect_any": [],
     "text": "theorem solution (f : ℝ → ℝ) (hf : Continuous f) : Continuous (fun x => f x + 1)"},
    {"id": "g10", "match": false, "expect_any": [],
     "text": "theorem solution (α : Type*) [MeasurableSpace α] (μ : Measure α) : μ ∅ = 0"},
    {"id": "g11", "match": true,  "expect_any": ["WZEmitter", "IdentityEmitter"],
     "text": "theorem solution (n : ℕ) : ∑ k in Finset.range (n + 1), (n.choose k) = 2^n"},
    {"id": "g12", "match": false, "expect_any": [],
     "text": "theorem solution (V : Type*) (G : SimpleGraph V) : G.chromaticNumber ≤ 0 ∨ True"}
  ]
}
```

- [ ] **Step 2: Write the failing tests** (`tests/test_prove2me_triage.py`):

```python
"""Stage-1 triage: golden-corpus precision/recall, registry coverage, ranking."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.ledger import AttemptLedger, AttemptRecord  # noqa: E402
from telperion.prove2me.triage import (  # noqa: E402
    coverage_report,
    match_statement,
    registry_class_names,
    save_queue,
    load_queue,
    triage,
)

GOLDEN = json.loads(
    (Path(__file__).parent / "fixtures" / "prove2me" / "golden_statements.json")
    .read_text()
)["statements"]


def test_golden_corpus_matches_labels():
    misses = []
    for g in GOLDEN:
        conf, classes = match_statement(g["text"])
        matched = conf > 0
        if matched != g["match"]:
            misses.append((g["id"], "matched" if matched else "missed"))
        elif g["match"] and g["expect_any"]:
            if not set(classes) & set(g["expect_any"]):
                misses.append((g["id"], f"wrong classes {classes}"))
    assert not misses, f"golden corpus failures: {misses}"


def test_every_rule_class_exists_in_registry():
    rep = coverage_report()
    assert rep["unknown_rule_classes"] == [], (
        "SHAPE_RULES references emitters not in the registry"
    )


def test_unmatched_registry_classes_is_a_named_list():
    rep = coverage_report()
    assert isinstance(rep["unmatched_registry_classes"], list)  # named gap, not hidden


def test_registry_enumeration_is_nonempty_and_large():
    names = registry_class_names()
    assert "SOSEmitter" in names and len(names) >= 100   # 133 on main


def test_triage_ranks_skips_attempted_and_roundtrips(tmp_path):
    milestones = [
        {"id": "m1", "mission_id": "A", "status": "open",
         "formal_statement": "theorem solution : (1 : ℚ) + 1 = 2"},
        {"id": "m2", "mission_id": "A", "status": "open",
         "formal_statement": "theorem solution (G : Type*) [Group G] : True"},
        {"id": "m3", "mission_id": "B", "status": "open",
         "formal_statement": "theorem solution : ∀ x : ℝ, 0 ≤ x^2"},
    ]
    led = AttemptLedger(tmp_path / "l.jsonl")
    led.append(AttemptRecord("m3", "B", ("SOSEmitter",), "h", "Rejected",
                             "", 1.0, "s", "2026-09-11"))
    q = triage(milestones, ledger=led)
    ids = [i.milestone_id for i in q]
    assert "m1" in ids          # identity-shaped: selected
    assert "m2" not in ids      # group theory: filtered
    assert "m3" not in ids      # already attempted: no-repeat
    save_queue(q, tmp_path / "queue.json")
    assert [i.milestone_id for i in load_queue(tmp_path / "queue.json")] == ids
```

- [ ] **Step 3: Run to verify failure.** Expected: FAIL, module not found.

- [ ] **Step 4: Implement** (`src/telperion/prove2me/triage.py`):

```python
"""Stage-1 certificate-first triage (spec section 3).

Deterministic and cheap: normalize the Lean formal_statement, match SHAPE_RULES
(regex features -> candidate emitter CLASS NAMES), veto on structure-keyword
blocklist.  Registry-driven honesty: every rule class must exist among the
enumerated Emitter subclasses (unknown_rule_classes == error), and emitters no
rule can select are NAMED in unmatched_registry_classes rather than hidden.
Stage 2 (scouting + the actual lift) is the driving session's job.
"""
from __future__ import annotations

import importlib
import json
import pkgutil
import re
from dataclasses import asdict, dataclass
from pathlib import Path

from .ledger import AttemptLedger

_NUMERIC = r"(ℕ|ℤ|ℚ|ℝ|Nat|Int|Rat|Real)"  # N Z Q R

# Structure keywords that mark a statement OUTSIDE certificate shapes.
BLOCKLIST = re.compile(
    r"\b(Group|Ring\b|Field\b|Module|Category|Continuous|Measure|Measurable|"
    r"Topolog|SimpleGraph|Homeomorph|Isometry|Filter\.|Deriv|integral|"
    r"Polynomial\.Galois|Matrix\.det)\w*"
)


@dataclass(frozen=True)
class ShapeRule:
    feature: str
    emitter_classes: tuple[str, ...]
    pattern: str
    weight: float

    def hits(self, text: str) -> bool:
        return re.search(self.pattern, text) is not None


SHAPE_RULES: tuple[ShapeRule, ...] = (
    ShapeRule("nonneg-or-le-inequality",
              ("DirectPolyaEmitter", "SOSEmitter", "RationalSOSEmitter",
               "PSDFormEmitter", "CauchySchwarzEmitter", "TangentSumEmitter"),
              rf"(≤|<).*", 0.4),
    ShapeRule("polynomial-content",
              ("SOSEmitter", "DirectPolyaEmitter"),
              rf"\^\s*\d|\*", 0.2),
    ShapeRule("exact-identity",
              ("IdentityEmitter", "ExactFactEmitter", "RationalIdentityEmitter"),
              rf"=\s*[-\d(]", 0.5),
    ShapeRule("padic-valuation",
              ("PadicValuationEmitter",),
              r"padicValNat|padicValRat|multiplicity", 1.0),
    ShapeRule("nat-tail",
              ("TailNatEmitter", "MonotoneRatioTailEmitter"),
              rf"∀\s*\w+\s*:\s*ℕ.*(≤|<).*→", 0.6),
    ShapeRule("bounded-nat-dispatch",
              ("FiniteDecideEmitter", "CaseDispatchAssemblyEmitter"),
              rf"∀\s*\w+\s*:\s*ℕ.*\w\s*(≤|<)\s*\d+\s*→", 0.7),
    ShapeRule("infeasibility",
              ("InfeasibilityEmitter", "SOSRefutationEmitter",
               "RealNullstellensatzEmitter"),
              rf"¬\s*∃", 0.8),
    ShapeRule("finite-sum-identity",
              ("WZEmitter", "IdentityEmitter"),
              r"∑|Finset\.(sum|range)|choose", 0.6),
    ShapeRule("interval-enclosure",
              ("IntervalBracketEmitter", "BernsteinEmitter",
               "SturmPositiveEmitter"),
              r"Real\.exp|Real\.log|Real\.sqrt", 0.3),
)


def _load_all_emitters() -> None:
    import telperion
    for m in pkgutil.iter_modules(telperion.__path__):
        if m.name.startswith("emit"):
            try:
                importlib.import_module(f"telperion.{m.name}")
            except ImportError:
                pass    # optional-extra emitters (sdp/bg) may be uninstallable


def registry_class_names() -> set[str]:
    _load_all_emitters()
    from telperion.workflow import Emitter
    names: set[str] = set()
    stack = list(Emitter.__subclasses__())
    while stack:
        cls = stack.pop()
        names.add(cls.__name__)
        stack.extend(cls.__subclasses__())
    return names


def coverage_report() -> dict:
    registry = registry_class_names()
    ruled = {c for r in SHAPE_RULES for c in r.emitter_classes}
    return {
        "unknown_rule_classes": sorted(ruled - registry),
        "unmatched_registry_classes": sorted(registry - ruled),
    }


def match_statement(formal_statement: str) -> tuple[float, tuple[str, ...]]:
    text = " ".join(formal_statement.split())
    has_numeric = re.search(_NUMERIC, text) is not None
    if BLOCKLIST.search(text) or not has_numeric:
        return 0.0, ()
    conf, classes = 0.0, []
    for rule in SHAPE_RULES:
        if rule.hits(text):
            conf += rule.weight
            classes.extend(c for c in rule.emitter_classes if c not in classes)
    return min(conf, 1.0), tuple(classes)


@dataclass(frozen=True)
class QueueItem:
    milestone_id: str
    mission_id: str
    statement: str
    emitter_classes: tuple[str, ...]
    score: float


def triage(milestones: list[dict], ledger: AttemptLedger | None = None) -> list[QueueItem]:
    items: list[QueueItem] = []
    for m in milestones:
        if m.get("status", "open") != "open":
            continue
        mid = str(m["id"])
        if ledger is not None and ledger.attempted(mid):
            continue
        stmt = m.get("formal_statement", "")
        conf, classes = match_statement(stmt)
        if conf <= 0:
            continue
        prior = 1.0
        if ledger is not None:
            rates = [ledger.win_rate(c) for c in classes]
            known = [r for r in rates if r is not None]
            if known:
                prior = 0.5 + 0.5 * max(known)
        items.append(QueueItem(mid, str(m.get("mission_id", "")), stmt,
                               classes, round(conf * prior, 4)))
    return sorted(items, key=lambda i: -i.score)


def save_queue(items: list[QueueItem], path: Path) -> None:
    Path(path).write_text(json.dumps(
        {"format": "telperion-p2m-queue-v1",
         "items": [asdict(i) for i in items]}, indent=1) + "\n")


def load_queue(path: Path) -> list[QueueItem]:
    doc = json.loads(Path(path).read_text())
    return [QueueItem(**{**d, "emitter_classes": tuple(d["emitter_classes"])})
            for d in doc["items"]]
```

- [ ] **Step 5: Run to verify pass.** `python3 -m pytest tests/test_prove2me_triage.py -v`. Iterate on `SHAPE_RULES` regexes until the golden corpus passes — tune rules, never labels. All PASS.

- [ ] **Step 6: Commit.** `git add src/telperion/prove2me/triage.py tests/test_prove2me_triage.py tests/fixtures/prove2me && git commit -m "feat(prove2me): registry-driven stage-1 triage with golden corpus"`

---

### Task 7: `attempt.py` — invariants I1–I5, solution rendering, build gate, submit/poll

**Files:**
- Create: `src/telperion/prove2me/attempt.py`
- Test: `tests/test_prove2me_attempt.py`

**Interfaces:**
- Consumes: `Prove2MeClient` (verify/verdict/annotate), `Workspace.scratch_project`, `AttemptLedger`/`AttemptRecord`, `QueueItem`.
- Produces:
  - `InvariantViolation(Prove2MeError)` and `BuildFailed(Prove2MeError)` (import `Prove2MeError` from `.api`)
  - `render_solution(formal_statement: str, proof_body: str, imports: tuple[str, ...] = ("Mathlib",)) -> str`
  - `check_no_sorry(src: str) -> None` (I3), `check_solution_theorem(src: str, formal_statement: str) -> None` (I3), `check_no_self_import(src: str, target_module: str) -> None` (I2)
  - `lake_build(project_dir: Path, runner=subprocess.run) -> None` (I1; raises `BuildFailed` with captured output)
  - `run_attempt(client, workspace, item: QueueItem, lean_source: str, emitters: tuple[str, ...], lift_hash: str, ledger: AttemptLedger, no_submit: bool = False, explanation: str = "", poll_interval_s: float = 10.0, max_polls: int = 90, _sleep=time.sleep, target_module: str = "") -> AttemptRecord` — runs I1–I3 then submits (unless `no_submit`), polls, annotates on success (I4), ledgers everything (I5: rejection recorded, never auto-resubmitted)

- [ ] **Step 1: Write the failing tests** (`tests/test_prove2me_attempt.py`):

```python
"""Invariants I1-I5 each have a violating case that must refuse; dry-run e2e."""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.prove2me.api import HttpResponse, Prove2MeClient  # noqa: E402
from telperion.prove2me.attempt import (  # noqa: E402
    BuildFailed,
    InvariantViolation,
    check_no_self_import,
    check_no_sorry,
    check_solution_theorem,
    lake_build,
    render_solution,
    run_attempt,
)
from telperion.prove2me.ledger import AttemptLedger  # noqa: E402
from telperion.prove2me.triage import QueueItem  # noqa: E402
from telperion.prove2me.workspace import Workspace  # noqa: E402

STMT = "theorem solution : (1 : ℚ) + 1 = 2"
GOOD = "import Mathlib\n\ntheorem solution : (1 : ℚ) + 1 = 2 := by norm_num\n"


def test_render_solution_contains_statement_and_imports():
    src = render_solution(STMT, "by norm_num")
    assert "import Mathlib" in src and "theorem solution" in src


def test_i3_no_sorry_refuses():
    with pytest.raises(InvariantViolation, match="sorry"):
        check_no_sorry(GOOD.replace("by norm_num", "by sorry"))
    check_no_sorry(GOOD)   # clean source passes


def test_i3_solution_name_and_statement_must_match():
    with pytest.raises(InvariantViolation):
        check_solution_theorem(GOOD.replace("solution", "myThm"), STMT)
    with pytest.raises(InvariantViolation):
        check_solution_theorem(GOOD, "theorem solution : (2 : ℚ) = 2")
    check_solution_theorem(GOOD, STMT)


def test_i2_no_self_import_refuses():
    src = "import Theorems.M42\n" + GOOD
    with pytest.raises(InvariantViolation, match="own target"):
        check_no_self_import(src, "Theorems.M42")
    check_no_self_import(GOOD, "Theorems.M42")


def test_i1_lake_build_gate(tmp_path):
    calls = {}

    def fake_run(cmd, **kw):
        calls["cmd"] = cmd
        class R: returncode, stdout, stderr = 1, b"", b"error: unsolved goals"
        return R()

    with pytest.raises(BuildFailed, match="unsolved goals"):
        lake_build(tmp_path, runner=fake_run)
    assert calls["cmd"][:2] == ["lake", "build"]


def _scripted_client(tmp_path, responses):
    def transport(method, url, headers, body):
        r = responses.pop(0)
        return r if isinstance(r, HttpResponse) else HttpResponse(*r)
    c = Prove2MeClient(workspace=tmp_path, transport=transport,
                       _sleep=lambda s: None, _now=lambda: 0.0)
    c.access_token = "t"
    return c


def test_run_attempt_dry_run_never_touches_network(tmp_path):
    c = _scripted_client(tmp_path, [])          # any request would IndexError
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash",
                      led, no_submit=True, _sleep=lambda s: None)
    assert rec.verdict == "DryRun" and led.records()[0].verdict == "DryRun"


def test_run_attempt_submits_polls_annotates_and_ledgers(tmp_path, monkeypatch):
    responses = [
        HttpResponse(200, json.dumps({"submission_id": "s7"})),      # POST /verify
        HttpResponse(200, json.dumps({"status": "PENDING"})),
        HttpResponse(200, json.dumps({"status": "Proved"})),
        HttpResponse(200, "{}"),                                      # PATCH annotate (I4)
    ]
    c = _scripted_client(tmp_path, responses)
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)   # I1 assumed green here
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash", led,
                      explanation="norm_num identity; source: arithmetic",
                      _sleep=lambda s: None)
    assert rec.verdict == "Proved" and rec.submission_id == "s7"
    assert not responses        # all four calls consumed, including annotate


def test_run_attempt_rejection_is_ledgered_not_retried(tmp_path, monkeypatch):
    responses = [
        HttpResponse(200, json.dumps({"submission_id": "s8"})),
        HttpResponse(200, json.dumps({"status": "Rejected",
                                      "output": "type mismatch"})),
    ]
    c = _scripted_client(tmp_path, responses)
    ws = Workspace(root=tmp_path / "wsp"); ws.ensure_layout()
    led = AttemptLedger(tmp_path / "l.jsonl")
    item = QueueItem("m1", "A", STMT, ("IdentityEmitter",), 0.9)
    monkeypatch.setattr("telperion.prove2me.attempt.lake_build",
                        lambda project_dir, runner=None: None)
    rec = run_attempt(c, ws, item, GOOD, ("IdentityEmitter",), "hash", led,
                      _sleep=lambda s: None)
    assert rec.verdict == "Rejected" and "type mismatch" in rec.server_output
    assert led.rejected("m1")           # I5: recorded; caller re-triages, never blind-resubmits
```

- [ ] **Step 2: Run to verify failure.** Expected: FAIL, module not found.

- [ ] **Step 3: Implement** (`src/telperion/prove2me/attempt.py`):

```python
"""Attempt pipeline (spec section 4): invariants I1-I5 as named, tested checks.

    probe -> certify -> emit   (existing Telperion pipeline, done by caller)
    -> I2/I3 source checks -> I1 local lake build -> POST /verify
    -> poll -> I4 annotate -> ledger (I5)

Every check raises rather than warns: an autonomous agent must refuse, not
proceed with a caveat.
"""
from __future__ import annotations

import datetime
import re
import subprocess
import time
from pathlib import Path

from .api import Prove2MeClient, Prove2MeError
from .ledger import AttemptLedger, AttemptRecord
from .triage import QueueItem
from .workspace import Workspace


class InvariantViolation(Prove2MeError):
    """A hard submission invariant (I1-I5) would be violated; refused."""


class BuildFailed(Prove2MeError):
    """I1: local lake build failed; nothing was submitted."""


def render_solution(formal_statement: str, proof_body: str,
                    imports: tuple[str, ...] = ("Mathlib",)) -> str:
    stmt = formal_statement.strip()
    stmt = re.sub(r":=\s*by\s+sorry\s*$", "", stmt).rstrip()
    lines = [f"import {i}" for i in imports]
    lines += ["", f"{stmt} := {proof_body}", ""]
    return "\n".join(lines)


def check_no_sorry(src: str) -> None:
    if re.search(r"\bsorry\b", src):
        raise InvariantViolation("I3: submission contains `sorry`")


def check_solution_theorem(src: str, formal_statement: str) -> None:
    if not re.search(r"\btheorem solution\b", src):
        raise InvariantViolation("I3: submitted theorem must be named `solution`")
    want = " ".join(
        re.sub(r":=\s*by\s+sorry\s*$", "", formal_statement.strip()).split()
    )
    have = " ".join(src.split())
    if want not in have:
        raise InvariantViolation(
            "I3: submission does not contain the formal_statement verbatim "
            "(binders/conclusion must match the captain's statement exactly)"
        )


def check_no_self_import(src: str, target_module: str) -> None:
    if target_module and re.search(
            rf"^import\s+{re.escape(target_module)}\s*$", src, re.M):
        raise InvariantViolation(
            f"I2: submission imports its own target ({target_module})")


def lake_build(project_dir: Path, runner=subprocess.run) -> None:
    r = runner(["lake", "build"], cwd=str(project_dir),
               capture_output=True, timeout=3600)
    if r.returncode != 0:
        tail = (r.stdout + r.stderr).decode(errors="replace")[-2000:]
        raise BuildFailed(f"I1: lake build failed in {project_dir}:\n{tail}")


def run_attempt(
    client: Prove2MeClient,
    workspace: Workspace,
    item: QueueItem,
    lean_source: str,
    emitters: tuple[str, ...],
    lift_hash: str,
    ledger: AttemptLedger,
    no_submit: bool = False,
    explanation: str = "",
    poll_interval_s: float = 10.0,
    max_polls: int = 90,
    _sleep=time.sleep,
    target_module: str = "",
) -> AttemptRecord:
    t0 = time.monotonic()
    today = datetime.date.today().isoformat()

    def record(verdict: str, server_output: str = "", submission_id: str = "") -> AttemptRecord:
        rec = AttemptRecord(item.milestone_id, item.mission_id, tuple(emitters),
                            lift_hash, verdict, server_output,
                            round(time.monotonic() - t0, 2), submission_id, today)
        ledger.append(rec)
        return rec

    # I2 + I3: source checks before anything expensive
    check_no_sorry(lean_source)
    check_solution_theorem(lean_source, item.statement)
    check_no_self_import(lean_source, target_module)

    # I1: green local build against the platform pin
    name = f"M{re.sub(r'[^A-Za-z0-9]', '', item.milestone_id)}"
    proj = workspace.scratch_project(name)
    (proj / name / f"{name}.lean").write_text(lean_source)
    lake_build(proj)

    if no_submit:
        return record("DryRun")

    submission_id = client.verify(lean_source, target_id=item.milestone_id)
    for _ in range(max_polls):
        v = client.verdict(submission_id)
        status = v.get("status", "PENDING")
        if status != "PENDING":
            break
        _sleep(poll_interval_s)
    else:
        return record("Rejected", "poll timeout", submission_id)

    output = v.get("output", "")
    if status in ("Proved", "Disproved"):
        if explanation:
            client.annotate(submission_id, explanation)      # I4
        return record(status, output, submission_id)
    # I5: ledger the rejection; the CALLER re-triages -- never resubmit here.
    return record("Rejected", output, submission_id)
```

- [ ] **Step 4: Run to verify pass.** `python3 -m pytest tests/test_prove2me_attempt.py -v` — all PASS.

- [ ] **Step 5: Run the whole bridge suite.** `python3 -m pytest tests/test_prove2me_*.py -v` — all PASS.

- [ ] **Step 6: Commit.** `git add src/telperion/prove2me/attempt.py tests/test_prove2me_attempt.py && git commit -m "feat(prove2me): attempt pipeline with hard invariants I1-I5"`

---

### Task 8: CLI subcommands (`telperion p2m …`)

**Files:**
- Modify: `src/telperion/cli.py` (add the `p2m` parser tree + `cmd_p2m_*` functions, following the existing `sub.add_parser` / `set_defaults(fn=...)` pattern)
- Test: `tests/test_prove2me_cli.py` (create)

**Interfaces:**
- Consumes: everything from Tasks 2–7.
- Produces: `telperion p2m login | missions | triage | lift <id> | attempt <id> | status | coverage`, each `cmd_p2m_*(args) -> int`. `--no-submit` on `attempt`. `--workspace` on all (default `$HOME/prove2me_workspace`). (`submit` is folded into `attempt`; a separate re-submit command would invite I5 violations.)

- [ ] **Step 1: Write the failing tests** (`tests/test_prove2me_cli.py`):

```python
"""CLI wiring: p2m subcommands parse and dispatch; no network in tests."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.cli import main  # noqa: E402


def test_p2m_coverage_runs_offline(capsys):
    assert main(["p2m", "coverage"]) == 0
    out = capsys.readouterr().out
    assert "unmatched_registry_classes" in out


def test_p2m_status_empty_ledger(tmp_path, capsys):
    assert main(["p2m", "status", "--workspace", str(tmp_path)]) == 0
    assert "attempts: 0" in capsys.readouterr().out


def test_p2m_lift_scaffolds_from_args(tmp_path, capsys):
    rc = main(["p2m", "lift", "mile9", "--statement",
               "theorem solution : (1 : ℚ) = 1",
               "--name", "M9", "--workspace", str(tmp_path)])
    assert rc == 0
    fam = tmp_path / "attempts" / "M9" / "family.py"
    assert fam.exists() and "mile9" in fam.read_text()
```

- [ ] **Step 2: Run to verify failure.** Expected: FAIL (argparse: invalid choice 'p2m').

- [ ] **Step 3: Implement.** In `cli.py`, add the command functions (near the other `cmd_*`):

```python
def _p2m_workspace(args):
    from pathlib import Path as _P
    from .prove2me.workspace import Workspace
    ws = Workspace(root=_P(args.workspace) if args.workspace else None)
    ws.ensure_layout()
    return ws


def cmd_p2m_login(args) -> int:
    """Establish the auth chain: credentials -> 30-day key -> hourly token."""
    import getpass
    from .prove2me.api import Prove2MeClient
    ws = _p2m_workspace(args)
    c = Prove2MeClient(workspace=ws.root)
    email = args.email or input("prove2.me email: ")
    c.login(email, getpass.getpass("password: "))
    c.mint_api_key()
    c.refresh()
    print(f"authenticated; tokens in {c._tokens_path}")
    return 0


def cmd_p2m_missions(args) -> int:
    from .prove2me.api import Prove2MeClient
    ws = _p2m_workspace(args)
    c = Prove2MeClient(workspace=ws.root)
    c.ensure_auth()
    for m in c.missions():
        print(f"{m.get('id')}  {m.get('status', '?'):<10} {m.get('title', '')[:70]}")
    return 0


def cmd_p2m_triage(args) -> int:
    from .prove2me.api import Prove2MeClient
    from .prove2me.ledger import AttemptLedger
    from .prove2me.triage import save_queue, triage
    ws = _p2m_workspace(args)
    c = Prove2MeClient(workspace=ws.root)
    c.ensure_auth()
    milestones = []
    for m in c.missions():
        milestones.extend(c.milestones(str(m["id"])))
    led = AttemptLedger(ws.root / "telperion_ledger.jsonl")
    q = triage(milestones, ledger=led)
    save_queue(q, ws.root / "queue.json")
    for item in q[:20]:
        print(f"{item.score:5.2f}  {item.milestone_id:<16} "
              f"{','.join(item.emitter_classes[:3])}")
    print(f"{len(q)} certificate-shaped milestones -> {ws.root / 'queue.json'}")
    return 0


def cmd_p2m_lift(args) -> int:
    """Scaffold a lift family for one milestone (statement fetched or passed)."""
    ws = _p2m_workspace(args)
    stmt = args.statement
    if not stmt:
        from .prove2me.api import Prove2MeClient
        c = Prove2MeClient(workspace=ws.root)
        c.ensure_auth()
        stmt = c.theorem(args.milestone_id).get("formal_statement", "")
        if not stmt:
            print("no formal_statement on that milestone")
            return 1
    name = args.name or f"M{args.milestone_id}"
    fam = ws.scaffold_lift(args.milestone_id, stmt, name=name)
    print(f"lift stub: {fam}\nedit family()/validation(), then: "
          f"telperion p2m attempt {args.milestone_id} --name {name}")
    return 0


def cmd_p2m_attempt(args) -> int:
    """Certify+emit the lift, run invariants, build locally, submit (unless --no-submit)."""
    import hashlib
    import importlib.util
    from .prove2me.api import Prove2MeClient
    from .prove2me.attempt import run_attempt
    from .prove2me.ledger import AttemptLedger
    from .prove2me.triage import load_queue
    ws = _p2m_workspace(args)
    name = args.name or f"M{args.milestone_id}"
    fam_path = ws.root / "attempts" / name / "family.py"
    if not fam_path.exists():
        print(f"no lift at {fam_path}: run `telperion p2m lift` first")
        return 1
    spec = importlib.util.spec_from_file_location(f"p2m_lift_{name}", fam_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    from .lean import LeanProfile
    from .workflow import certify, emit
    from .emit_facts import IdentityEmitter
    emitters = getattr(mod, "EMITTERS", None) or [IdentityEmitter()]
    res = emit(certify(mod.family()), LeanProfile(), emitters, mod.validation(),
               file_name=f"{name}.lean")
    lean_source = res.text

    items = [i for i in load_queue(ws.root / "queue.json")
             if i.milestone_id == args.milestone_id] \
        if (ws.root / "queue.json").exists() else []
    if not items:
        from .prove2me.triage import QueueItem
        items = [QueueItem(args.milestone_id, "", mod.FORMAL_STATEMENT,
                           tuple(type(e).__name__ for e in emitters), 0.0)]

    c = Prove2MeClient(workspace=ws.root)
    if not args.no_submit:
        c.ensure_auth()
    led = AttemptLedger(ws.root / "telperion_ledger.jsonl")
    rec = run_attempt(
        c, ws, items[0], lean_source,
        tuple(type(e).__name__ for e in emitters),
        hashlib.sha256(fam_path.read_bytes()).hexdigest()[:16],
        led, no_submit=args.no_submit, explanation=args.explanation or "",
    )
    print(f"{rec.verdict}  milestone={rec.milestone_id} "
          f"submission={rec.submission_id or '-'}")
    return 0 if rec.verdict in ("Proved", "Disproved", "DryRun") else 1


def cmd_p2m_status(args) -> int:
    from .prove2me.ledger import AttemptLedger
    ws = _p2m_workspace(args)
    print(AttemptLedger(ws.root / "telperion_ledger.jsonl").render_status())
    return 0


def cmd_p2m_coverage(args) -> int:
    import json as _json
    from .prove2me.triage import coverage_report
    rep = coverage_report()
    print(_json.dumps(rep, indent=1))
    return 0 if not rep["unknown_rule_classes"] else 1
```

And in `main()`, alongside the other parsers:

```python
    p2m = sub.add_parser("p2m", help="prove2.me solver bridge (see docs/PROVE2ME_BRIDGE_DESIGN_2026-09-11.md)")
    p2m_sub = p2m.add_subparsers(dest="p2m_cmd", required=True)

    def _wsopt(p):
        p.add_argument("--workspace", default=None,
                       help="workspace root (default $HOME/prove2me_workspace)")

    q = p2m_sub.add_parser("login", help="auth chain: credentials -> key -> token")
    q.add_argument("--email", default=None); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_login)
    q = p2m_sub.add_parser("missions", help="list platform missions"); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_missions)
    q = p2m_sub.add_parser("triage", help="rank open milestones vs emitter registry"); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_triage)
    q = p2m_sub.add_parser("lift", help="scaffold a lift family for one milestone")
    q.add_argument("milestone_id"); q.add_argument("--statement", default=None)
    q.add_argument("--name", default=None); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_lift)
    q = p2m_sub.add_parser("attempt", help="certify, emit, gate, and submit one milestone")
    q.add_argument("milestone_id"); q.add_argument("--name", default=None)
    q.add_argument("--no-submit", action="store_true")
    q.add_argument("--explanation", default=None); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_attempt)
    q = p2m_sub.add_parser("status", help="attempt ledger summary"); _wsopt(q)
    q.set_defaults(fn=cmd_p2m_status)
    q = p2m_sub.add_parser("coverage", help="shape-rule vs registry coverage report")
    q.set_defaults(fn=cmd_p2m_coverage)
```

(Read `cli.py` first and mirror its exact local idioms — import placement, help-string style. If `emit()`'s signature differs from `emit(certified, profile, emitters, validation, file_name=)`, follow the real signature as used by `examples/bernoulli/generate.py`.)

- [ ] **Step 4: Run to verify pass.** `python3 -m pytest tests/test_prove2me_cli.py -v` — all PASS. Also run the full suite: `python3 -m pytest tests/ -v -x -k "prove2me"`.

- [ ] **Step 5: Commit.** `git add src/telperion/cli.py tests/test_prove2me_cli.py && git commit -m "feat(prove2me): telperion p2m CLI subcommands"`

---

### Task 9: MCP tools + `prove2me-solver` skill

**Files:**
- Modify: `src/telperion/mcp_server.py`
- Create: `claude-plugin/skills/prove2me-solver/SKILL.md`
- Modify: `claude-plugin/.claude-plugin/plugin.json` (description mention only; version bump)

**Interfaces:**
- Consumes: the `p2m` CLI (MCP tools delegate via the existing `_cli()` helper).
- Produces: MCP tools `p2m_triage`, `p2m_lift`, `p2m_attempt`, `p2m_status`, `p2m_coverage`; the orchestration skill.

- [ ] **Step 1: Add MCP tools** (append to `mcp_server.py`, mirroring the existing `@mcp.tool()` + `_cli` pattern):

```python
@mcp.tool()
def p2m_triage() -> str:
    """Rank prove2.me open milestones against Telperion's emitter registry
    (certificate-first triage). Writes queue.json in the workspace; returns
    the top of the ranked queue. Requires prior `telperion p2m login`."""
    code, out = _cli(["p2m", "triage"])
    return out.strip() or f"exit {code}"


@mcp.tool()
def p2m_lift(milestone_id: str, name: str = "") -> str:
    """Scaffold a lift family (Lean formal_statement embedded verbatim) for one
    prove2.me milestone. Edit family()/validation() before attempting."""
    args = ["p2m", "lift", milestone_id]
    if name:
        args += ["--name", name]
    code, out = _cli(args)
    return out.strip() or f"exit {code}"


@mcp.tool()
def p2m_attempt(milestone_id: str, name: str = "", no_submit: bool = False,
                explanation: str = "") -> str:
    """Certify+emit the lift, enforce invariants I1-I5 (local lake build gate),
    submit to prove2.me unless no_submit, poll the verdict, ledger the result."""
    args = ["p2m", "attempt", milestone_id]
    if name:
        args += ["--name", name]
    if no_submit:
        args += ["--no-submit"]
    if explanation:
        args += ["--explanation", explanation]
    code, out = _cli(args)
    return out.strip() or f"exit {code}"


@mcp.tool()
def p2m_status() -> str:
    """Attempt-ledger summary: attempts, proved count, recent verdicts."""
    code, out = _cli(["p2m", "status"])
    return out.strip() or f"exit {code}"


@mcp.tool()
def p2m_coverage() -> str:
    """Shape-rule vs emitter-registry coverage: unknown rule classes (error)
    and registry emitters no rule can select (named gap)."""
    code, out = _cli(["p2m", "coverage"])
    return out.strip() or f"exit {code}"
```

- [ ] **Step 2: Write the skill** (`claude-plugin/skills/prove2me-solver/SKILL.md`):

```markdown
---
name: prove2me-solver
description: Use when solving prove2.me formalization missions with Telperion — autonomous certificate-first loop: triage open milestones against the emitter registry, scout rejection history, lift the Lean statement to a Telperion family, certify/emit/build locally, submit, annotate. Use when the user mentions prove2me, prove2.me, formalization missions, or asks to earn/solve missions with Telperion.
---

# Prove2Me solver: certificate-first autonomous loop

Design + invariants: `telperion/docs/PROVE2ME_BRIDGE_DESIGN_2026-09-11.md`.
Platform reference (vendored): `telperion/docs/vendor/prove2me_skill.md`,
`telperion/docs/vendor/prove2me_mission_solver.md`.

## Non-negotiables (enforced in code; do not work around a refusal)

- I1 no submission without a green LOCAL `lake build` under the platform pin.
- I2 never import the target theorem itself. Importing OTHER platform theorems
  is encouraged (reuse is scored).
- I3 theorem named `solution`, formal_statement verbatim, zero `sorry`.
- I4 every accepted proof gets an explanation + exact source citation.
- I5 a rejection is ledgered and RE-TRIAGED, never blind-resubmitted.
- Circuit breaker open => STOP the loop entirely; report, do not reset.

## The loop

1. `p2m_triage` — ranked queue of certificate-shaped open milestones.
2. For the top item, SCOUT before lifting (platform etiquette, mandatory):
   milestone rejection history, prior submissions, audit flags, mission
   comments. A captain-rejected path is dead: do not re-walk it.
3. `p2m_lift <id>` — scaffold, then EDIT the family: translate the embedded
   formal_statement FAITHFULLY into sympy (exact rationals only). Translate
   the source's actual claim, never your impression of it. If the statement
   resists every emitter shape, drop it and re-triage — do not force a lift.
4. `p2m_attempt <id> --no-submit` first if the lift is at all uncertain;
   then `p2m_attempt <id> --explanation "<2-4 factual sentences + source>"`.
5. On Proved: move on. On Rejected: read the server output, ledger already
   has it; re-triage. On repeated CertifyRefused: run `telperion diagnose` —
   FALSE means consider the DISPROOF path (negate and resubmit deliberately).
6. `p2m_status` at the end of every session; report the tally to the user.

## Explanation style (reputational surface — keep it factual)

2-4 sentences: what is proved, the certificate shape used (e.g. "exact
rational SOS decomposition, kernel-checked"), and the exact source citation.
No flourish, no claims beyond the theorem.
```

- [ ] **Step 3: Bump plugin version + description** in `claude-plugin/.claude-plugin/plugin.json`: version `0.1.6` → `0.2.0`; append to description: `" Includes the prove2me-solver skill (autonomous certificate-first mission solving on prove2.me)."`

- [ ] **Step 4: Smoke the MCP tools offline.** `python3 -c "import sys; sys.path.insert(0,'src'); from telperion.cli import main; main(['p2m','coverage'])"` — prints the coverage report, exit 0.

- [ ] **Step 5: Commit.** `git add src/telperion/mcp_server.py claude-plugin && git commit -m "feat(prove2me): p2m MCP tools and prove2me-solver skill"`

---

### Task 10: Live acceptance — registration, real corpus, first autonomous attempt

Live-network operator-adjacent task; everything before this was offline. Run from a session with the user reachable (account creation may require email verification — that step is the user's).

**Files:**
- Modify: `tests/fixtures/prove2me/golden_statements.json` (append real statements)
- Modify: `docs/PROVE2ME_BRIDGE_DESIGN_2026-09-11.md` (record acceptance result)

**Interfaces:**
- Consumes: everything.
- Produces: the spec's acceptance criterion — one real open milestone → autonomous "Proved" verdict, ledgered, with explanation + citation attached.

- [ ] **Step 1: Registration.** Re-read `docs/vendor/prove2me_skill.md`. If credentials don't exist yet: ask the user to create the account (email verification is theirs), then `telperion p2m login`. Verify: `telperion p2m missions` lists missions.

- [ ] **Step 2: Reconcile API reality.** Compare live responses against the field names assumed in `api.py`/`triage.py` (`id`, `mission_id`, `formal_statement`, `status`, `submission_id`, `status` in verdicts). Fix any mismatches, update the recorded fixtures in `tests/fixtures/prove2me/` to the real shapes, re-run the offline suite green. Commit: `fix(prove2me): reconcile field names with live API`.

- [ ] **Step 3: Extend the golden corpus.** Fetch ~30 formal statements from completed missions across fields, hand-label match/expect_any, append to `golden_statements.json`. Re-run `tests/test_prove2me_triage.py`; tune `SHAPE_RULES` until green. Record stage-1 precision/recall in the fixture's `note`. Commit: `test(prove2me): real-statement golden corpus`.

- [ ] **Step 4: First autonomous attempt.** Run the skill loop: `p2m triage` → scout → lift → `attempt --no-submit` → `attempt` with explanation. Target: "Proved" on one real open milestone. If the queue is empty (low stage-1 yield), that is a REPORTABLE finding per the spec's risk section — report it with the coverage numbers; the answer is more emitters, not doctrine dilution.

- [ ] **Step 5: Record acceptance.** Append an "Acceptance (2026-MM-DD)" section to the design doc: milestone id, theorem page link, emitter(s) used, wall time, ledger line. Commit: `docs(prove2me): acceptance record -- first autonomous Proved verdict`.

- [ ] **Step 6: Full suite + wrap.** `python3 -m pytest tests/ -k prove2me -v` all green; push the branch; open the PR per repo convention.

**Live-run risk list (from final review, 2026-09-11)**

- Clone the official workspace BEFORE any other `p2m` command (or run
  `telperion p2m sync <repo-url>` first); otherwise `ensure_layout` creates
  empty directories and `sync_official` may refuse to clone into a non-empty
  path.
- Reconcile verdict-status vocabulary (platform may use `PENDING` / `Proved` /
  `Disproved` / `FAILED` / `CE` / `WA`) and response field names before first
  submission; the bridge assumes the shapes in the vendored skill.md — update
  `api.py` fixtures if the live shapes differ.
- First build needs `lake exe cache get` and may be slow (multi-GB Mathlib
  download if no cache); budget extra time. `PollTimeout` records count as
  attempted — re-enable for a milestone requires a manual ledger edit (delete
  the `PollTimeout` line) since the no-repeat rule fires on them.
- Poll budget of 90 × 10 s = 15 min may undercount slow server compiles;
  increase `max_polls` or `poll_interval_s` if the platform's compilation
  queue is deep.
- Confirm `/agent/api-key` Bearer-session auth and the exact login response
  key (`session_token` vs `token`) against a live login before the first
  autonomous run.
- Confirm `Theorems.Thm_<id>` module naming for the I2 self-import check;
  the actual module path may differ (e.g. `Prove2Me.Thm_<id>`) — adjust
  `target_module` in `cmd_p2m_attempt` after inspecting the official workspace
  layout.

---

## Self-Review Notes

- **Spec coverage:** api client incl. version gate/throttle/breaker (T2–T3), workspace/toolchain (T1, T4), registry-driven triage + golden corpus (T6), attempt pipeline I1–I5 (T7), ledger + win rates + no-repeat (T5), CLI/MCP/skill (T8–T9), compat smoke first (T1), acceptance (T10). Disproof path: surfaced in the skill loop (step 5) via `diagnose`; deliberate rather than automated — matches spec ("consider the disproof path").
- **Known unknowns, handled explicitly:** exact endpoint paths/payload field names come from the vendored skill.md (T2 Step 1) and live reconciliation (T10 Step 2); the plan's names are the contract between our own modules, which is what the offline tests pin.
- **Deliberate scope cuts (consistent with spec):** no `p2m submit` separate from `attempt` (I5), reduction-sketch submission deferred until a real case demands it (spec allows but does not require it in v1; `submit_problem` client method exists), no daemon.
