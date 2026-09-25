"""Push triggers: restricted to main, and required unless a workflow is explicitly exempted.

A push to a pull-request branch already runs the workflow through the pull_request event;
running it a second time on the push event doubled the per-push runner load on an account
with a 20-job concurrency ceiling (2026-09-24). Required checks come from the pull_request run.

Post-merge verification of main needs a push trigger (2026-09-25). telperion-zeta-reflection had
none, so main was re-verified only by its weekly cron, and that cron never fired: GitHub dropped the
2026-09-23 slot. A cron can silently not run at all, which is worse than failing because it leaves
no red mark. So every workflow must have `push: branches: [main]` unless it is listed in
NO_PUSH_ALLOWED with the reason. That way a trigger cannot quietly disappear.
"""
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

_WF = Path(__file__).resolve().parents[2] / ".github" / "workflows"

#: Workflows allowed to have no push trigger, with the reason. Keep this list short and justified.
NO_PUSH_ALLOWED = {
    "telperion-legacy-boxes.yml": (
        "669 legacy box certificates at ~5.3 core-hours; nothing imports them. Cron + dispatch "
        "only, by cost decision (governance 2026-09-25). Mitigation: the weekly scheduled run "
        "and the telperion-audit schedule-only watch."
    ),
}


def _on(wf):
    d = yaml.safe_load((_WF / wf).read_text())
    return d.get("on", d.get(True))


@pytest.mark.parametrize("wf", sorted(p.name for p in _WF.glob("*.yml")))
def test_push_trigger_is_main_only(wf):
    on = _on(wf)
    if not isinstance(on, dict) or "push" not in on:
        pytest.skip("no push trigger (presence is checked by test_push_trigger_present)")
    push = on["push"] or {}
    assert push.get("branches") == ["main"], f"{wf}: push trigger must be restricted to main"


@pytest.mark.parametrize("wf", sorted(p.name for p in _WF.glob("*.yml")))
def test_push_trigger_present(wf):
    on = _on(wf)
    has_push = isinstance(on, dict) and "push" in on
    if wf in NO_PUSH_ALLOWED:
        assert not has_push, f"{wf}: listed in NO_PUSH_ALLOWED but now has a push trigger; drop the exemption"
        return
    assert has_push, (f"{wf}: no push trigger on main, so main is never re-verified after a merge "
                      "(a cron is not enough: it can silently not fire). Add `push: branches: [main]` "
                      "(with a paths filter if the workflow is costly) or justify it in NO_PUSH_ALLOWED.")


def test_exemptions_exist():
    names = {p.name for p in _WF.glob("*.yml")}
    stale = sorted(set(NO_PUSH_ALLOWED) - names)
    assert not stale, f"NO_PUSH_ALLOWED lists workflows that no longer exist: {stale}"


def test_zeta_reflection_push_covers_the_island():
    """Pin the paths filter to the island's sources, so a filter edit cannot silently narrow coverage."""
    push = _on("telperion-zeta-reflection.yml")["push"]
    paths = set(push.get("paths", []))
    for need in ("telperion/examples/zeta_reflection/**", ".github/workflows/telperion-zeta-reflection.yml"):
        assert need in paths, f"zeta-reflection push filter must include {need}"
