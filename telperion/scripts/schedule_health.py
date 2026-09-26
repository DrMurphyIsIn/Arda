#!/usr/bin/env python3
"""Report the health of workflows GitHub can only start on a schedule.

Two failures on 2026-09-25 were invisible for days because nothing watches a cron:

* `telperion-legacy-boxes` had been red since its 2026-09-21 scheduled run (all four
  shards), on a bug in the workflow's own axiom gate.  It runs weekly and on demand, so
  no pull request ever showed the red.
* `telperion-zeta-reflection`'s weekly cron had NEVER fired, although the cron was on
  main before its slot.  GitHub runs schedules on a best-effort basis and may drop one.
  A dropped run leaves no mark at all, so it looks exactly like success.

A workflow is CRON-ONLY when it has a `schedule` trigger and no `push` trigger for the
default branch: nothing automatic re-verifies the default branch after a merge, so its
cron is the only automatic path and its silence means nothing.

Verdicts, given the run history (fetched by the workflow, or a JSON file for tests):

* FAIL   -- a cron-only workflow's most recent run FAILED.  Warnings get ignored; this is
            meant to leave a red mark that someone sees.
* WARN   -- a cron-only workflow has no scheduled run at all, or none since its cron
            reached the default branch.  The cron may simply be younger than its first
            slot, which is why this is not a failure.
* OK     -- otherwise.

Usage:

    python telperion/scripts/schedule_health.py --workflows .github/workflows [--runs runs.json]
    python telperion/scripts/schedule_health.py --workflows <dir> --list
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

try:
    import yaml
except ModuleNotFoundError:  # pragma: no cover - the workflow installs it
    yaml = None

OK, WARN, FAIL = "OK", "WARN", "FAIL"


def _on_block(doc: dict) -> dict:
    """The `on:` mapping.  PyYAML parses a bare `on` key as the boolean True."""
    on = doc.get("on", doc.get(True))
    if on is None:
        return {}
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list):
        return {k: None for k in on}
    return on


def _push_covers_default_branch(on: dict, default_branch: str) -> bool:
    if "push" not in on:
        return False
    push = on["push"]
    if not isinstance(push, dict):
        return True  # `push:` with no filter fires on every branch
    branches = push.get("branches")
    if branches is None:
        return True
    return default_branch in branches


def classify(text: str, default_branch: str = "main") -> Tuple[bool, bool]:
    """(has_schedule, cron_only) for one workflow file's text."""
    if yaml is None:  # pragma: no cover
        raise RuntimeError("pyyaml is required")
    on = _on_block(yaml.safe_load(text) or {})
    has_schedule = "schedule" in on
    return has_schedule, has_schedule and not _push_covers_default_branch(on, default_branch)


def cron_only_workflows(workflows_dir: Path, default_branch: str = "main") -> List[str]:
    out = []
    for p in sorted(workflows_dir.glob("*.yml")) + sorted(workflows_dir.glob("*.yaml")):
        has_schedule, cron_only = classify(p.read_text(), default_branch)
        if cron_only:
            out.append(p.name)
    return out


def verdict(name: str, runs: dict) -> Tuple[str, str]:
    """Judge one cron-only workflow.  `runs` is {last: {...}|None, last_scheduled: {...}|None}."""
    last = runs.get("last")
    last_sched = runs.get("last_scheduled")
    if last and last.get("conclusion") == "failure":
        url = last.get("html_url", "")
        return FAIL, (f"{name}: its most recent run FAILED "
                      f"({last.get('created_at', '?')}) and no pull request would show it. {url}")
    if not last_sched:
        return WARN, (f"{name}: no scheduled run has ever happened.  Either the cron is younger "
                      f"than its first slot, or GitHub dropped the firing -- a dropped schedule "
                      f"leaves no trace, so silence here is not success.")
    if last_sched.get("conclusion") not in (None, "success", "skipped"):
        return WARN, (f"{name}: its last SCHEDULED run ended "
                      f"{last_sched.get('conclusion')} ({last_sched.get('created_at', '?')}).")
    return OK, f"{name}: last scheduled run {last_sched.get('conclusion')} " \
               f"({last_sched.get('created_at', '?')})."


def report(workflows_dir: Path, runs_by_workflow: Dict[str, dict],
           default_branch: str = "main") -> Tuple[int, List[str]]:
    """(exit code, lines).  Exit 1 when any cron-only workflow's latest run failed."""
    names = cron_only_workflows(workflows_dir, default_branch)
    lines: List[str] = []
    if not names:
        return 0, ["No cron-only workflows: every scheduled workflow also runs on a push to "
                   f"{default_branch}, so a dropped or failing schedule cannot hide."]
    worst = 0
    lines.append(f"Cron-only workflows (schedule but no push to {default_branch}): {len(names)}")
    for n in names:
        v, msg = verdict(n, runs_by_workflow.get(n, {}))
        lines.append(f"  [{v}] {msg}")
        if v == FAIL:
            worst = 1
    return worst, lines


def _parse(argv: Optional[Sequence[str]]) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--workflows", type=Path, required=True)
    ap.add_argument("--runs", type=Path, help="JSON: {workflow.yml: {last: {...}, last_scheduled: {...}}}")
    ap.add_argument("--default-branch", default="main")
    ap.add_argument("--list", action="store_true", help="print the cron-only workflows and exit")
    return ap.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    a = _parse(argv)
    if a.list:
        for n in cron_only_workflows(a.workflows, a.default_branch):
            print(n)
        return 0
    runs = json.loads(a.runs.read_text()) if a.runs else {}
    code, lines = report(a.workflows, runs, a.default_branch)
    for ln in lines:
        print(ln)
        if ln.strip().startswith(f"[{FAIL}]"):
            print(f"::error::{ln.strip()[len(FAIL) + 3:]}")
        elif ln.strip().startswith(f"[{WARN}]"):
            print(f"::warning::{ln.strip()[len(WARN) + 3:]}")
    return code


if __name__ == "__main__":
    sys.exit(main())
