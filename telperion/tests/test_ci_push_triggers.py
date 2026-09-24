"""Every workflow with a `push:` trigger restricts it to main.

A push to a pull-request branch already runs the workflow through the pull_request event;
running it a second time on the push event doubled the per-push runner load on an account
with a 20-job concurrency ceiling (2026-09-24). Required checks come from the pull_request run.
"""
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

_WF = Path(__file__).resolve().parents[2] / ".github" / "workflows"


@pytest.mark.parametrize("wf", sorted(p.name for p in _WF.glob("*.yml")))
def test_push_trigger_is_main_only(wf):
    d = yaml.safe_load((_WF / wf).read_text())
    on = d.get("on", d.get(True))
    if not isinstance(on, dict) or "push" not in on:
        pytest.skip("no push trigger")
    push = on["push"] or {}
    assert push.get("branches") == ["main"], f"{wf}: push trigger must be restricted to main"
