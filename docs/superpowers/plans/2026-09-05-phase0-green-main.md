# Phase 0 — Green Main Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `origin/main` CI green so a visiting mathematician sees passing checks, by fixing the real regressions introduced by today's dVP/RH merges.

**Architecture:** Five independent fixes to the `telperion/` package and its CI manifest. Three are tractable and concrete (manifest registration, emitter-sensitivity classification, lake-absent test skips). Two are sympy-version-specific regressions that only fail under the pinned `sympy==1.12` CI matrix leg and MUST be reproduced in a sympy-1.12 virtualenv before fixing.

**Tech Stack:** Python 3.11/3.12, sympy (multi-version matrix: current + pinned 1.12), pytest, TOML manifest (`telperion/telperion.toml`), GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-09-05-public-release-prep-design.md`

## Global Constraints

- Work on branch `docs/public-release-prep` (worktree `~/arda-repo-prep`), off verified `origin/main`. Land via a CI-gated PR. No force-push to `main`.
- Run all Python via `python3` with `PYTHONPATH=src` from `~/arda-repo-prep/telperion`.
- The two version-specific fixes MUST be validated under a `sympy==1.12` venv, not just the ambient sympy — they pass under current sympy and fail only under 1.12.
- No test may be silently downgraded: a skip must be an explicit `pytest.mark.skipif` with a human-readable reason, never a silent pass or a broadened tolerance that hides a real regression.
- The emitter-sensitivity stance is a load-bearing trust-model statement. Classify each emitter honestly by reading its emit body; a wrong stance undermines the whole non-vacuity guarantee. Flag the three classifications for maintainer confirmation in the PR description.
- Verify with the same commands CI uses: `python -m telperion.cli verify --group heavy` (casestudy) and `pytest tests/ ...` under both sympy versions.

---

### Task 1: Register `dvp_atoms` in the manifest (fixes `telperion-casestudy`)

**Files:**
- Modify: `telperion/telperion.toml` (add one `[[check]]` block)
- Reference: `telperion/examples/dvp_atoms/generate.py` (the unlisted script)

**Interfaces:**
- Consumes: the manifest `[[check]]` schema — `name` (str), `script` (path from `telperion/`), `group` (one of `quick`/`heavy`/`audit`/`sdp`).
- Produces: a green `telperion.cli verify` manifest-completeness check.

- [ ] **Step 1: Reproduce the failure**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src python3 -m telperion.cli verify --group heavy`
Expected: `MANIFEST INCOMPLETE — unlisted generate scripts: .../examples/dvp_atoms/generate.py`, exit 1.

- [ ] **Step 2: Determine the correct group**

Run: `cd ~/arda-repo-prep/telperion && time PYTHONPATH=src python3 examples/dvp_atoms/generate.py >/dev/null`
Decision rule: regeneration under a few seconds → `group = "quick"`; multi-minute re-certification → `heavy`; adversarial/large sweep → `audit`. (dVP atoms is a small RH atom family; expect `quick`.)

- [ ] **Step 3: Add the `[[check]]` block**

Append to `telperion/telperion.toml` (keeping the existing block style), using the group from Step 2:

```toml
[[check]]
name = "dvp_atoms"
script = "examples/dvp_atoms/generate.py"
group = "quick"    # dVP RH atom family (log-derivative building blocks); regen ~seconds
```

- [ ] **Step 4: Verify manifest completeness**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src python3 -m telperion.cli verify --group quick`
Expected: no `MANIFEST INCOMPLETE`; the `dvp_atoms` regen-diff runs and passes (byte-stable).

- [ ] **Step 5: Commit**

```bash
cd ~/arda-repo-prep && git add telperion/telperion.toml
git commit -m "fix(telperion): register dvp_atoms family in manifest

Greens telperion-casestudy: the new dVP atom example was unlisted, which
the manifest-completeness gate correctly rejected."
```

---

### Task 2: Classify the three new RH emitters (fixes `test_every_emitter_is_classified`)

**Files:**
- Modify: `telperion/src/telperion/emitter_sensitivity.py` (add 3 entries to `REGISTRY`)
- Read: `telperion/src/telperion/emit_bc_split.py`, `emit_jensen_zero_count.py`, `emit_sphere_bound.py`
- Test: `telperion/tests/test_certificate_sensitivity.py::test_every_emitter_is_classified`

**Interfaces:**
- Consumes: `REGISTRY: dict[str, SensitivityStance]`, the `_S(stance, note, checked_in=...)` constructor, and the two stance constants `CERTIFICATE_SENSITIVE` / `STRUCTURALLY_NONVACUOUS` (all defined in `emitter_sensitivity.py`).
- Produces: `REGISTRY` entries for `BCSplitEmitter`, `JensenZeroCountEmitter`, `SphereBoundEmitter`.

- [ ] **Step 1: Reproduce the failure**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src python3 -m pytest tests/test_certificate_sensitivity.py::test_every_emitter_is_classified -q`
Expected: FAIL — `emitters missing a sensitivity stance: ['BCSplitEmitter', 'JensenZeroCountEmitter', 'SphereBoundEmitter']`.

- [ ] **Step 2: Read each emit body and decide the stance (honesty judgment)**

For each of the three modules, read the emitter class's `emit_body`/certificate construction and apply the registry's own definitions (top-of-file docstring):
- `CERTIFICATE_SENSITIVE` — carries a corruptible identity/numeric witness whose corruption should break the claim; requires a negative-control adapter (`checked_in` names it, or leave `None` and note the adapter is TODO).
- `STRUCTURALLY_NONVACUOUS` — positivity / decidable / finite-cover / glue / hypothesis-gated assembly with no corruptible witness; the built-in structural non-vacuity check suffices.

Working hypothesis from the docstrings (CONFIRM against the emit bodies): all three take the hard analytic bounds *as hypotheses* and perform structural combine/order/uniformization → `STRUCTURALLY_NONVACUOUS`. Do not assume — verify each ships no corruptible numeric certificate.

- [ ] **Step 3: Add the REGISTRY entries**

In `emitter_sensitivity.py`, add to `REGISTRY` (adjust stance/notes per Step 2; example shown for the confirmed structural case):

```python
    "BCSplitEmitter": _S(STRUCTURALLY_NONVACUOUS,
                         "log-derivative split + entire-bound combine; analytic bounds "
                         "enter as hypotheses, assembly is structural — no corruptible witness"),
    "JensenZeroCountEmitter": _S(STRUCTURALLY_NONVACUOUS,
                                 "Jensen zero-count from boundary growth; side goals are "
                                 "positivity/order (0<r<R), bounds are hypotheses"),
    "SphereBoundEmitter": _S(STRUCTURALLY_NONVACUOUS,
                             "strip growth -> uniform sphere bound; fully general, "
                             "bounds taken as hypotheses (self-contained import Mathlib)"),
```

If any is CERTIFICATE_SENSITIVE instead, use `_S(CERTIFICATE_SENSITIVE, "...", checked_in=None)` and add a follow-up note that its negative-control adapter is owed (Task 2b, out of Phase-0 scope, tracked in the PR).

- [ ] **Step 4: Verify the gate passes**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src python3 -m pytest tests/test_certificate_sensitivity.py -q`
Expected: PASS (all emitters classified).

- [ ] **Step 5: Commit**

```bash
cd ~/arda-repo-prep && git add telperion/src/telperion/emitter_sensitivity.py
git commit -m "fix(telperion): classify the 3 new RH emitters' sensitivity stance

BCSplit/JensenZeroCount/SphereBound were added without a stance, tripping
the emitter-sensitivity gate. Each takes analytic bounds as hypotheses and
does structural assembly -> STRUCTURALLY_NONVACUOUS. (Flag for review.)"
```

---

### Task 3: Skip Lean-toolchain tests cleanly when `lake` is absent

**Files:**
- Modify: `telperion/tests/test_statement_match.py`, `test_verify.py`, `test_simplify.py`, `test_negative_control.py`
- Reference (good pattern): `telperion/tests/lean_env.py` (`lean_env_ready()`, uses `shutil.which("lake")`); `telperion/tests/test_lean_server.py:20` (`_HAVE_LEAN = shutil.which("lake") is not None or (~/.elan/bin/lake).exists()`)

**Interfaces:**
- Consumes: `shutil.which("lake")` and/or `tests.lean_env.lean_env_ready(env_dir)`.
- Produces: the four test modules skip (not fail) when no Lean toolchain is present.

- [ ] **Step 1: Reproduce**

Run: `cd ~/arda-repo-prep/telperion && PATH=/usr/bin:/bin PYTHONPATH=src python3 -m pytest tests/test_statement_match.py tests/test_verify.py tests/test_simplify.py tests/test_negative_control.py -q`
Expected: FAILs with `FileNotFoundError: [Errno 2] No such file or directory: 'lake'` (and one `LeanServer.start()` assertion). This mirrors the CI `unit` job, which has no `lake`.

- [ ] **Step 2: Diagnose each failure's guard gap**

Identify why each currently-failing test does not skip. Known: `test_statement_match.py:24` guards on `(_ENV / "lake-manifest.json").exists()` — the checked-in env has the manifest file but the runner has no `lake` binary, so the guard is True yet the test shells out to `lake`. The guard must ALSO require the `lake` binary. Confirm the analogous gap in the other three (they guard on `lean_env_ready` against a specific example dir, or not at all for the `lake`-invoking cases).

- [ ] **Step 3: Strengthen the guards**

For `test_statement_match.py`, tighten the module-level guard:

```python
import shutil
_HAS_ENV = (_ENV / "lake-manifest.json").exists() and shutil.which("lake") is not None
pytestmark = pytest.mark.skipif(not _HAS_ENV, reason="needs a built Lean env + lake on PATH")
```

For the specific `lake`-invoking tests in `test_verify.py`, `test_simplify.py`, and `test_negative_control.py` (`test_false_monotone_negative_control_both_layers`, `test_assert_kernel_rejects_no_false_positive_on_true_theorem`, and the `LeanServer.start()` test), add a decorator using the existing readiness helper:

```python
import shutil
import pytest

requires_lake = pytest.mark.skipif(
    shutil.which("lake") is None and not (Path.home() / ".elan" / "bin" / "lake").exists(),
    reason="requires a Lean/lake toolchain",
)
```

Apply `@requires_lake` to exactly the tests that invoke `lake`/`LeanServer`; leave the pure-Python tests in those files unguarded so coverage is preserved.

- [ ] **Step 4: Verify skip (no lake) and pass (with lake, if available)**

Run (no lake): `cd ~/arda-repo-prep/telperion && PATH=/usr/bin:/bin PYTHONPATH=src python3 -m pytest tests/test_statement_match.py tests/test_verify.py tests/test_simplify.py tests/test_negative_control.py -q`
Expected: the `lake`-requiring tests report `s` (skipped) with the reason; pure-Python tests PASS; 0 failures.

- [ ] **Step 5: Commit**

```bash
cd ~/arda-repo-prep && git add telperion/tests/test_statement_match.py telperion/tests/test_verify.py telperion/tests/test_simplify.py telperion/tests/test_negative_control.py
git commit -m "test(telperion): skip lake-requiring tests cleanly when toolchain absent

The unit CI job has no Lean toolchain; these tests shelled out to 'lake'
and errored instead of skipping. Guard on shutil.which('lake') so they
skip explicitly (with reason), never silently pass."
```

---

### Task 4: Fix the sympy==1.12 `mt_optimize` int-parse regression

**Files:**
- Modify: `telperion/src/telperion/mt_optimize.py` (root cause near line 93: `lo = [int(sp.floor(v * denom)) for v in b]`)
- Test: `telperion/tests/test_mt_optimize.py` (`test_optimize_deg4_beats_vp_and_is_admissible`, `test_optimizer_output_feeds_exact_sos_cert`, `test_finer_denom_recovers_flagship_quality`)

**Interfaces:**
- Consumes: `sympy` 1.12 API. Produces: version-robust integer flooring that works on 1.12 and current sympy.

- [ ] **Step 1: Create a sympy-1.12 venv (the failure is version-specific)**

```bash
python3 -m venv /tmp/telp-sympy112 && /tmp/telp-sympy112/bin/pip install -q "sympy==1.12" scipy numpy pytest
```

- [ ] **Step 2: Reproduce under sympy 1.12**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src /tmp/telp-sympy112/bin/python -m pytest tests/test_mt_optimize.py -q`
Expected: FAIL — `ValueError: invalid literal for int() with base 10: '-06)'`. (Passes under current sympy — confirmed 2026-09-05.)

- [ ] **Step 3: Root-cause with systematic-debugging**

Use the `superpowers:systematic-debugging` skill. The `int(...)` receiving a string like `'-06)'` under 1.12 indicates `sp.floor(v * denom)` (or `v`/`denom`) stringifies to scientific notation that `int()` then fails to parse — likely a numpy/sympy Float interaction that changed between 1.12 and current. Add a printout of `type(v)`, `type(v*denom)`, `repr(sp.floor(v*denom))` at line 93 under 1.12 to pin the exact object.

- [ ] **Step 4: Fix version-robustly**

Replace the fragile flooring with an explicit rational/int path that does not depend on Float str formatting, e.g. coerce through `sympy.Rational`/`sympy.Integer` or `math.floor(float(v) * denom)` as appropriate to the values in `b`. Choose the form that keeps the deg-4 admissibility/exactness assertions intact (do NOT change the math — only the integer extraction).

- [ ] **Step 5: Verify under BOTH sympy versions**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src /tmp/telp-sympy112/bin/python -m pytest tests/test_mt_optimize.py -q` → PASS
Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src python3 -m pytest tests/test_mt_optimize.py -q` → PASS

- [ ] **Step 6: Commit**

```bash
cd ~/arda-repo-prep && git add telperion/src/telperion/mt_optimize.py
git commit -m "fix(telperion): version-robust integer flooring in mt_optimize (sympy 1.12)

Under sympy 1.12 the int(sp.floor(...)) path parsed a scientific-notation
string and raised ValueError; current sympy masked it. Coerce through
exact int extraction so both matrix legs pass. Math unchanged."
```

---

### Task 5: Fix the sympy==1.12 spectral-factorization tolerance regression

**Files:**
- Modify: `telperion/src/telperion/emit_spectral_factorization.py` and/or `telperion/tests/test_emit_spectral_factorization.py:32` (`assert max(abs(ar[k] - float(a[k])) ...) < 1e-6`)

**Interfaces:**
- Consumes: sympy 1.12 numeric roots. Produces: a roundtrip that passes under both sympy versions without hiding a real regression.

- [ ] **Step 1: Reproduce under sympy 1.12**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src /tmp/telp-sympy112/bin/python -m pytest tests/test_emit_spectral_factorization.py -q`
Expected: FAIL — `assert 1.16e-4 < 1e-6` (passes under current sympy — confirmed 2026-09-05).

- [ ] **Step 2: Determine whether this is precision or a real regression**

Inspect `ar` (approximate/numeric coefficients) vs `a` (exact) in `test_spectral_factor_roundtrips`. Decide: is the 1.16e-4 gap an inherent float-precision difference in sympy 1.12's root solver (acceptable → adjust tolerance to a principled bound, e.g. `1e-3`, with a comment), or does the emitted certificate actually diverge (real regression → fix the emitter, keep the tight tolerance)? The `test_spectral_factor_roundtrips` also has an EXACT SOS identity assertion (line 47, `sp.expand(p - (A**2 + (1-x**2)*B**2)) == 0`) — if that exact check still passes under 1.12, the float roundtrip gap is precision, not a math error.

- [ ] **Step 3: Apply the justified fix**

If precision: loosen the numeric tolerance to a documented bound that still catches a genuine break, e.g.:

```python
    # sympy 1.12's numeric root solver is ~1e-4 accurate here; the EXACT SOS
    # identity below (sp.expand(...) == 0) is the real correctness gate.
    assert max(abs(ar[k] - float(a[k])) for k in range(len(a))) < 1e-3
```

If real regression: fix the emitter's coefficient computation; keep `1e-6`.

- [ ] **Step 4: Verify under BOTH sympy versions**

Run under sympy 1.12 and current sympy: both PASS, and the exact SOS-identity assertion still holds.

- [ ] **Step 5: Commit**

```bash
cd ~/arda-repo-prep && git add -A telperion/tests/test_emit_spectral_factorization.py
git commit -m "test(telperion): principled tolerance for spectral roundtrip under sympy 1.12

The numeric-coefficient roundtrip is ~1e-4 accurate under sympy 1.12; the
exact SOS identity (sp.expand==0) remains the correctness gate. Loosen the
numeric tolerance to 1e-3 so both matrix legs pass without hiding a break."
```

---

### Task 6: Full local CI-parity run + open the PR

**Files:** none (verification + PR)

- [ ] **Step 1: Run the unit suite under both sympy versions**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src python3 -m pytest tests/ -q` → expect only intentional skips, 0 failures.
Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src /tmp/telp-sympy112/bin/python -m pytest tests/ -q` → 0 failures.

- [ ] **Step 2: Run the manifest verify groups CI uses**

Run: `cd ~/arda-repo-prep/telperion && PYTHONPATH=src python3 -m telperion.cli verify --group quick` and `--group heavy` → both clean, no `MANIFEST INCOMPLETE`.

- [ ] **Step 3: Push and open the PR**

```bash
cd ~/arda-repo-prep && git push -u origin docs/public-release-prep
gh pr create --repo DrMurphyIsIn/Arda --base main --head docs/public-release-prep \
  --title "fix(ci): green main — register dvp_atoms, classify RH emitters, sympy-1.12 + lake-skip fixes" \
  --body "Phase 0 of the public-release-prep spec. Fixes the real regressions from today's dVP/RH merges: dvp_atoms manifest registration (casestudy), sensitivity stances for BCSplit/JensenZeroCount/SphereBound (flag for review), lake-absent test skips, and two sympy==1.12-only regressions (mt_optimize int-parse, spectral tolerance). No mathematics changed.

🤖 Generated with [Claude Code](https://claude.com/claude-code)"
```

- [ ] **Step 4: Watch CI to green**

Run: `gh run watch --repo DrMurphyIsIn/Arda` (or `gh run list --repo DrMurphyIsIn/Arda --branch docs/public-release-prep`). Confirm `proof-lean`, `proof-verify`, `telperion-test`, `telperion-casestudy`, `telperion-lean-e2e` all green before requesting merge.

---

## Self-Review

**Spec coverage:** This plan implements Phase 0 of the spec (green main) in full — all five failing-CI items (manifest, emitter sensitivity, lake-skip, mt_optimize, spectral) plus a CI-parity gate and PR. Phases 1–4 are explicitly out of scope for this plan (separate plan).

**Placeholder scan:** No "TBD"/"handle edge cases" placeholders. The two version-specific tasks (4, 5) intentionally route through reproduction-under-sympy-1.12 + systematic-debugging because the fix form depends on the 1.12 object behavior, which cannot be pinned without that environment; the entry point, exact failing assertion, and decision rule are concrete.

**Type consistency:** `_S`, `REGISTRY`, `CERTIFICATE_SENSITIVE`, `STRUCTURALLY_NONVACUOUS` match `emitter_sensitivity.py`. `lean_env_ready`/`shutil.which("lake")` match `tests/lean_env.py` and `tests/test_lean_server.py`. Manifest `[[check]]` schema matches existing blocks.

**Known judgment calls flagged for the PR:** (1) the three emitter stances are a trust-model statement — call them out for maintainer confirmation; (2) Task 5's precision-vs-regression decision must be justified in the commit, not assumed.
