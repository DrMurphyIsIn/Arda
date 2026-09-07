# Parameterized RH-in-a-Box + Scale-to-Height-T Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize the merged fixed-box RH-in-a-box capstone (PR #285) to a single generic-corner Lean theorem instantiable on any finite rational box, driven by a `--box`/`--height` pipeline, and deliver a kernel-certified milestone at height T=100 with a best-effort probe higher.

**Architecture:** One reusable theorem `rh_in_box_of_certificate` over arbitrary rational corners `(sigma0,sigma1,T0,T1)` and a Blaschke ball `(c,R)`, with the geometry (`box subset ball`, `s=1 notin ball`) as `norm_num`-discharged hypotheses and the winding integer / on-line zeros / edge non-vanishing as documented Arb non-kernel hypotheses. A Python driver computes the per-box Arb data and emits a small instantiation file. The winding stays Arb-carried (Task-9 ceiling from PR #285), so Lean grows only with the on-line zero count `~N(T)`.

**Tech Stack:** Python 3.14 (Telperion emitters, sympy, python-flint/Arb, mpmath), Lean 4 + Mathlib, first-class Telperion emitter pattern.

**Spec:** `telperion/docs/superpowers/specs/2026-09-07-parameterized-rh-box-scale-to-height.md`

## Global Constraints

- Object: `riemannZeta` (nontrivial zeros = zeros in the critical strip; pole at `s=1` excluded from every box). `completedRiemannZeta` bridge via `BoxLocalization.zeta_zero_iff_completed_zero` (needs `0 < re`).
- Box corners rational; box must satisfy `0 < sigma0 < 1/2 < sigma1 < 1`, `0 <= T0 < T1`, and exclude `s=1`.
- Winding integer `N`, edge non-vanishing, and value enclosures are documented NON-KERNEL Arb input, carried as Lean hypotheses. Kernel proves the implication. `conjecture1_proved = False` in every artifact. No finite box/height is a proof of RH.
- No emoji anywhere. No `set_option linter.unusedVariables false`. Acceptance for every Lean deliverable: sorry-free, `#print axioms` = `{propext, Classical.choice, Quot.sound}` (no `sorryAx`), and a built lakefile target.
- Winding remains Arb-carried (do NOT attempt an in-kernel discrete-winding proof over segments — the PR #285 Task-9 ceiling stands).
- Python: `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3` (3.14.6; flint 0.9.0). Run from `.../telperion`.
- Lean: `/Users/peterwmurphy/.elan/bin/lake`; local builds SAFE; ALWAYS `lake exe cache get` before `lake build`; NEVER a cold Mathlib compile.
- Optional-dependency hygiene (per the PR #285 CI fix): every new flint-requiring test carries `@requires_flint` (skipif `not _ae._FLINT_AVAILABLE`); every Lean-build test carries `@requires_lake` (skipif `shutil.which("lake", path=~/.elan/bin:PATH) is None`). Keep `test_every_emitter_is_classified` green for any new emitter.
- Merged predecessor files on `main` (templates to generalize): `examples/zeta_zero_localization/lean/BoxLocalization.lean` (`exhaustion_by_count`, `box_localization_core`, `zeta_zero_iff_completed_zero`, `all_nontrivial_zeros_in_box_on_critical_line`), `BlaschkeBox.lean` (`zeta_blaschke_split_box` over `ball cB 13`), `BoxArgPrinciple.lean`, `BoxArgPrincipleZeta.lean` (`box_arg_principle_zeta'`).

---

### Task 1: Corner- and count-generic counting core

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/RHInBoxCore.lean`
- Modify: `telperion/examples/zeta_zero_localization/lean/lakefile.toml` (add `RHInBoxCore` lib + defaultTarget)
- Test: `telperion/tests/test_rhinbox.py` (build assertion, `@requires_lake`)

**Interfaces:**
- Consumes: `BoxLocalization.exhaustion_by_count` (already generic: `{s T : Finset C} {d : C -> Z} {n : N}`, `T subset s`, `T.card = n`, `1 <= d` on `s`, `sum d = n` => `s = T and forall d = 1`).
- Produces: `RHInBoxCore.rh_in_box_core` (signature below).

- [ ] **Step 1: Write the failing build test.**
```python
import os, shutil, subprocess
from pathlib import Path
import pytest
_LAKE_PATH = os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", "")
requires_lake = pytest.mark.skipif(shutil.which("lake", path=_LAKE_PATH) is None, reason="requires lake/Lean")

@requires_lake
def test_rh_in_box_core_builds():
    env = {**os.environ, "PATH": _LAKE_PATH}
    d = str(Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "lean")
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(["lake", "build", "RHInBoxCore"], cwd=d, env=env, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
```

- [ ] **Step 2: Run to verify it fails.** `PYTHONPATH=src ... -m pytest tests/test_rhinbox.py::test_rh_in_box_core_builds -q` -> FAIL (target missing).

- [ ] **Step 3: Write `RHInBoxCore.lean`.** Generalize `box_localization_core` from literal corners + a fixed 5-tuple `z1..z5` to arbitrary real corners + a Finset `T` of on-line zeros:
```lean
import Mathlib
import BoxLocalization   -- reuse exhaustion_by_count
open Complex
namespace RHInBoxCore

/-- Counting capstone, corner- and count-generic. If the total divisor over `s` equals the
    cardinality of a sub-Finset `T subset s` of on-line zeros, then every zeta zero in the box
    lies on the line. `T.card` replaces the fixed `5`; corners are variables. -/
theorem rh_in_box_core
    (sigma0 sigma1 T0 T1 : ℝ)
    (s T : Finset ℂ) (d : ℂ → ℤ)
    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)
    (hTsub : T ⊆ s)
    (hTline : ∀ z ∈ T, z.re = 1 / 2)
    (hcount : (∑ ρ ∈ s, d ρ) = (T.card : ℤ))
    (hzero_in : ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ ∈ s) :
    ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  obtain ⟨hsT, _⟩ := exhaustion_by_count hTsub rfl hd1 hcount
  intro ρ hre him hρ0
  have hρs : ρ ∈ s := hzero_in ρ hre him hρ0
  rw [hsT] at hρs
  exact hTline ρ hρs
```
(The `hTcard = rfl` uses `T.card` directly as `n`.) Add `#print axioms rh_in_box_core` as a comment-guide; do NOT commit a bare `#print` that errors.

- [ ] **Step 4: Build + axiom check.** `cd .../lean && lake exe cache get && lake build RHInBoxCore`. Confirm sorry-free; axioms clean.

- [ ] **Step 5: Run the build test + commit.**
```bash
git add telperion/examples/zeta_zero_localization/lean/RHInBoxCore.lean telperion/examples/zeta_zero_localization/lean/lakefile.toml telperion/tests/test_rhinbox.py
git commit -m "feat(zeroloc): corner- and count-generic RH-in-box counting core (rh_in_box_core)"
```

**Acceptance:** `RHInBoxCore.lean` builds sorry-free with clean axioms; `rh_in_box_core` is corner-generic (real corner variables) and count-generic (`T.card`, not a fixed 5); reuses `exhaustion_by_count`.

---

### Task 2: Parameterized Blaschke split + box argument principle over a variable ball

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/RHInBoxAnalytic.lean`
- Modify: `lakefile.toml`
- Test: `telperion/tests/test_rhinbox.py` (build assertion)

**Interfaces:**
- Consumes: `MeromorphicOn.extract_zeros_poles`, `differentiableAt_riemannZeta`, `analyticOn_riemannZeta`, `MeromorphicOn.divisor`; the box-boundary integral atoms (`box_residue_sum`, `rect_winding`, `rect_argument_principle` from `dvp_geom_atoms`, and/or the box-B specializations in the merged `BoxArgPrinciple.lean`).
- Produces: `RHInBoxAnalytic.zeta_count_eq_winding_generic` — for a box with a valid Blaschke ball `(c,R)`, the total divisor over the box equals the (Arb) winding integer `N`, and the divisor is nonneg with support capturing every box zero:
```lean
theorem zeta_count_eq_winding_generic
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ)
    (hRpos : 0 < R)
    (hbox_ball : ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) → ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hwind : <box-boundary contour integral of logDeriv riemannZeta over [sigma0,sigma1]x[T0,T1]> = 2 * π * I * N)
    (hEintegrability_and_edge_nonvanishing : <the routine Arb boundary hypotheses>) :
    ∃ (s : Finset ℂ) (d : ℂ → ℤ),
      (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧
      (∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
        riemannZeta ρ = 0 → ρ ∈ s) ∧
      (∑ ρ ∈ s, d ρ) = N := by
  ...
```

- [ ] **Step 1: Write the failing build test** (`test_rh_in_box_analytic_builds`, same shape as Task 1 Step 1, target `RHInBoxAnalytic`).

- [ ] **Step 2: Run to verify it fails.**

- [ ] **Step 3: Write `RHInBoxAnalytic.lean`.** Generalize the merged `BlaschkeBox.zeta_blaschke_split_box` (which fixes `ball cB 13`) and `BoxArgPrincipleZeta.box_arg_principle_zeta'` to variable `(c,R)`:
  - `s := (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).support.toFinset`, `d := MeromorphicOn.divisor riemannZeta (Metric.ball c R)`.
  - `extract_zeros_poles` over `ball c R` (meromorphic since `hs1` excludes the only pole `s=1`; `hRpos`) gives `riemannZeta = (prod (z-u)^{d u}) * g`, `g` analytic nonvanishing on the ball; hence `logDeriv riemannZeta = sum d/(z-u) + logDeriv g` with `E = logDeriv g` holomorphic on the box (via `hbox_ball`).
  - `hd1` (`d >= 1` on `s`): from `divisor_nonneg` (analytic on the ball, no poles) + support means `d != 0`, so `d >= 1`. `hzero_in`: a box zero is in the ball (`hbox_ball`) so in the divisor support.
  - The box argument principle: `Bd(logDeriv zeta) = Bd(sum d/(z-u)) + Bd(E)`; `Bd(E) = 0` (rect_argument_principle, E holo on the box); `Bd(sum d/(z-u)) = 2*pi*i*sum d` (box_residue_sum + per-pole rect_winding, poles strictly interior); combine with `hwind` and cancel `2*pi*i` => `sum d = N`.
  - **Strategy note:** follow the merged `BoxArgPrincipleZeta.lean` proof structure verbatim, replacing the literal `cB`, `13`, and corner literals with the variables `c`, `R`, `sigma0..T1` and the concrete `norm_num` geometry facts with the hypotheses `hRpos`, `hbox_ball`, `hs1`. The per-pole winding side conditions (pole strictly interior to the box) follow from membership in `s` = divisor support intersect box; carry them as needed.

- [ ] **Step 4: Build + axiom check.** sorry-free; axioms clean. If a genuine Mathlib gap blocks full generality after real effort, report BLOCKED with the exact obstruction (controller may fall back to emit-per-box literal substitution for Task 3 — see plan revision note).

- [ ] **Step 5: Run the build test + commit.**
```bash
git add telperion/examples/zeta_zero_localization/lean/RHInBoxAnalytic.lean telperion/examples/zeta_zero_localization/lean/lakefile.toml telperion/tests/test_rhinbox.py
git commit -m "feat(zeroloc): parameterized zeta Blaschke split + box argument principle over a variable ball"
```

**Acceptance:** `zeta_count_eq_winding_generic` builds sorry-free, clean axioms; `(c,R)` and corners are variables; geometry enters only as `hRpos`/`hbox_ball`/`hs1` hypotheses; E-holomorphicity is in-kernel (not assumed); `sum d = N` derived; no residue-decomposition assumed.

---

### Task 3: Assemble the generic `rh_in_box_of_certificate` + regression on the original box

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/RHInBox.lean` (the generic theorem + the `[2/5,3/5]x[10,35]` regression instantiation)
- Modify: `lakefile.toml`
- Test: `telperion/tests/test_rhinbox.py`

**Interfaces:**
- Consumes: `RHInBoxCore.rh_in_box_core` (Task 1), `RHInBoxAnalytic.zeta_count_eq_winding_generic` (Task 2), `BoxLocalization.zeta_zero_iff_completed_zero` (Lambda<->zeta bridge on the line).
- Produces: `RHInBox.rh_in_box_of_certificate` (the full generic capstone) + `RHInBox.rh_in_box_10_35` (regression, must match the merged result).

- [ ] **Step 1: Write the failing build test** (`test_rh_in_box_generic_and_regression_build`, target `RHInBox`).

- [ ] **Step 2: Run to verify it fails.**

- [ ] **Step 3: Write `RHInBox.lean`.** The generic theorem takes corners + `(c,R)` + the Arb bundle (winding `hwind`, on-line Finset `T` with `hTline`/`hTsub`-via-`hzero_in`, edge/integrability), and:
```lean
theorem rh_in_box_of_certificate
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ)
    (hRpos : 0 < R) (hbox_ball : ...) (hs1 : ...)
    (T : Finset ℂ) (hTline : ∀ z ∈ T, z.re = 1/2)
    (hTzero : ∀ z ∈ T, riemannZeta z = 0)
    (hTbox : ∀ z ∈ T, (sigma0 ≤ z.re ∧ z.re ≤ sigma1) ∧ (T0 ≤ z.im ∧ z.im ≤ T1))
    (hwind : ... = 2 * π * I * N)
    (harb : ...)                              -- edge non-vanishing + integrability
    (hcount : (N : ℤ) = (T.card : ℤ)) :       -- N_line = N (the localization hypothesis)
    ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1/2 := by
  obtain ⟨s, d, hd1, hzero_in, hsum⟩ :=
    zeta_count_eq_winding_generic sigma0 sigma1 T0 T1 c R N hRpos hbox_ball hs1 hwind harb
  have hTsub : T ⊆ s := fun z hz => hzero_in z (hTbox z hz).1 (hTbox z hz).2 (hTzero z hz)
  have hcount' : (∑ ρ ∈ s, d ρ) = (T.card : ℤ) := by rw [hsum, hcount]
  exact rh_in_box_core sigma0 sigma1 T0 T1 s T d hd1 hTsub hTline hcount' hzero_in
```
Then the regression: `rh_in_box_10_35` instantiates all parameters with the original box's values — `sigma0=2/5, sigma1=3/5, T0=10, T1=35, c=cB, R=13, N=5`, `T` = the 5 known on-line zeros — discharging `hRpos`/`hbox_ball`/`hs1` by `norm_num` and wiring `hwind`/`harb`/`T` from the merged `BoxArgPrincipleZeta`/`XiLineZeros` results. Assert (in a docstring/comment) it reproduces `all_nontrivial_zeros_in_box_on_critical_line`.

- [ ] **Step 4: Build + axiom check** (sorry-free, clean axioms for both `rh_in_box_of_certificate` and `rh_in_box_10_35`).

- [ ] **Step 5: Run test + commit.**
```bash
git add telperion/examples/zeta_zero_localization/lean/RHInBox.lean telperion/examples/zeta_zero_localization/lean/lakefile.toml telperion/tests/test_rhinbox.py
git commit -m "feat(zeroloc): generic rh_in_box_of_certificate + regression instantiation on [10,35]"
```

**Acceptance:** `rh_in_box_of_certificate` is fully corner/ball/count generic, sorry-free, clean axioms; `rh_in_box_10_35` instantiates it and reproduces the merged capstone conclusion; geometry discharged by `norm_num`, Arb data as documented hypotheses.

---

### Task 4: Python driver (`--box`/`--height`) + per-box instantiation emitter

**Files:**
- Modify: `telperion/src/telperion/emit_box_localization.py` (emit the instantiation of `rh_in_box_of_certificate`), and corner-parameterize `emit_xi_line_zeros.py` / `emit_winding_count.py` where still literal.
- Modify: `telperion/examples/zeta_zero_localization/generate.py` (`--box`, `--height` modes)
- Modify: `telperion/src/telperion/arb_enclosure.py` if a `--height` boundary/sweep helper is needed
- Test: `telperion/tests/test_box_localization.py`, `telperion/tests/test_rhinbox.py`

**Interfaces:**
- Consumes: `arb_enclosure.enclose_zeta_segments` (winding), `enclose_lambda` (on-line sign changes), `emit_winding_count.segment_winding_certificate`, `RHInBox.rh_in_box_of_certificate` (Lean, instantiated).
- Produces: `generate.py --box sigma0,sigma1,T0,T1` and `generate.py --height T`, emitting a per-box Lean file `RHInBox_<tag>.lean` (or a section) that instantiates the generic theorem with the box's Arb data; extended `box_localization_certificate` accepting arbitrary corners + `n_line`/`n_total` (already corner-parameterized via `re_lo/re_hi/im_lo/im_hi`).

- [ ] **Step 1: Write failing tests.**
```python
def test_box_localization_certificate_refuses_invalid_box():
    import pytest
    from telperion.emit_box_localization import box_localization_certificate
    # n_line != n_total refused (already), and an invalid sigma-range excluding 1/2 refused
    with pytest.raises(ValueError):
        box_localization_certificate(n_line=6, n_total=5, re_lo="2/5", re_hi="3/5", im_lo="0", im_hi="100")

def test_driver_box_flag_emits_instantiation(tmp_path):
    # generate.py --box on a small already-known box emits an instantiation referencing rh_in_box_of_certificate
    ...  # invoke generate.py --box 2/5,3/5,10,35 --check ; assert the emitted text instantiates rh_in_box_of_certificate
```

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement.** Add `--box sigma0,sigma1,T0,T1` and `--height T` to `generate.py`. For a box: run the winding certificate (`enclose_zeta_segments` -> `segment_winding_certificate` -> `N`); run the on-line sign-change sweep over `[T0,T1]` at spacing `< pi/log(T1)` to extract the `N_line` distinct zeros (imag parts, strictly increasing); compute edge non-vanishing (segment enclosures off 0 on the 4 sides); choose `c = (sigma0+sigma1)/2 + (T0+T1)/2 * I`, `R = dist(c, (sigma0,T0)) + margin`. Emit a Lean file instantiating `rh_in_box_of_certificate` with these (geometry via `norm_num`, the on-line Finset `T` built from the `N_line` zeros with a strict-chain distinctness proof, `hwind`/`harb` as the Arb hypotheses). REFUSE (raise) if `N_line != N`, if the box is invalid (`s=1` in ball, or `sigma`-range excludes `1/2`), or if the on-line sweep fails to resolve all zeros (adaptive refine first).

- [ ] **Step 4: Run tests to verify pass.**

- [ ] **Step 5: Register/keep classification green + optional-dep guards.** If `emit_box_localization` gains an emitter class, keep `test_every_emitter_is_classified` green. All new flint/lake tests carry `@requires_flint`/`@requires_lake`.

- [ ] **Step 6: Commit.**
```bash
git add telperion/src/telperion/emit_box_localization.py telperion/src/telperion/emit_xi_line_zeros.py telperion/src/telperion/emit_winding_count.py telperion/examples/zeta_zero_localization/generate.py telperion/tests/
git commit -m "feat(zeroloc): --box/--height driver + per-box instantiation of rh_in_box_of_certificate"
```

**Acceptance:** `generate.py --box`/`--height` computes the winding + on-line zeros + edge non-vanishing for an arbitrary box and emits an instantiation of `rh_in_box_of_certificate`; refuses invalid/underresolved boxes; drift-clean `--check`; optional-dep guards present.

---

### Task 5: T=100 milestone + docs + CI

**Files:**
- Create (emitted): `telperion/examples/zeta_zero_localization/lean/RHInBox_h100.lean` (or a section) — `[2/5,3/5]x[0,100]`, ~29 on-line zeros
- Modify: `telperion/examples/zeta_zero_localization/generate.py` (wire `--height 100` case into `--check`)
- Modify: `telperion/docs/ZETA_ZERO_LOCALIZATION_STATUS.md`, `telperion/README.md`, `telperion/CHANGELOG.md`, `.github/workflows/telperion-lean-e2e.yml`
- Test: `telperion/tests/test_rhinbox.py`

**Interfaces:**
- Consumes: Task 4 driver, Task 3 generic theorem.
- Produces: a kernel-certified RH-in-box for `[2/5,3/5]x[0,100]`.

- [ ] **Step 1: Emit + build the T=100 instantiation.** `generate.py --height 100`. Verify `N == N_line == N(100)` (~29; the driver computes the exact integer). Build locally: `lake build RHInBox_h100` (or the combined target). sorry-free; `#print axioms` clean.

- [ ] **Step 2: Add a build-assertion test** (`@requires_lake`) for the T=100 target, and a drift assertion in `generate.py --check` that the certified `N_line` equals the winding `N` for the height-100 box.

- [ ] **Step 3: Update docs.** `ZETA_ZERO_LOCALIZATION_STATUS.md`: add the parameterized generic theorem + the T=100 milestone (RH verified in `[2/5,3/5]x[0,100]`, `conjecture1_proved = False`, winding/edge/enclosures = Arb non-kernel input). `README.md` + `CHANGELOG.md`: one honest line each. Framing exact: extends the verified range (Turing's method), NOT a proof of RH.

- [ ] **Step 4: CI.** Extend/add a job building the generic theorem + the T=100 instantiation (warm `lake exe cache get` then `lake build`). Validate YAML.

- [ ] **Step 5: Commit.**
```bash
git add -A telperion/ .github/
git commit -m "feat(zeroloc): T=100 RH-in-box milestone ([2/5,3/5]x[0,100], ~29 zeros) + docs + CI"
```

**Acceptance:** `[2/5,3/5]x[0,100]` RH-in-box builds sorry-free with clean axioms, ~29 on-line zeros = winding N(100); docs honest; CI job valid; drift-clean.

---

### Task 6: Probe higher T; report the achieved ceiling

**Files:**
- Create: `telperion/docs/RH_BOX_HEIGHT_PROBE.md` (findings)
- Optionally emit: a higher-T instantiation if it builds in reasonable time
- Test: none required (probe)

**Interfaces:** Consumes the Task 4 driver.

- [ ] **Step 1: Probe T=1000.** `generate.py --height 1000` (~649 on-line zeros). Time the Arb computation (Python) and the `lake build` of the emitted instantiation. Record: emit time, Lean file size, build time, peak memory, success/fail.

- [ ] **Step 2: Bisect the ceiling.** If T=1000 builds, try higher (2000, 4000, ...); if it fails/times out (set a generous but bounded wall-clock, e.g. 30 min build), bisect down (500, 750). Find the largest T whose kernel artifact builds in the bounded budget.

- [ ] **Step 3: Write `RH_BOX_HEIGHT_PROBE.md`.** Report the achieved ceiling T*, the cost curve (Arb ~T log T, Lean ~N(T)), the binding constraint (emitted theorem size / build time / memory), and whether the highest built instantiation is committed or left as an on-demand driver invocation. `conjecture1_proved = False`; no finite T is a proof.

- [ ] **Step 4: Commit** (findings doc + optionally the highest built instantiation).
```bash
git add telperion/docs/RH_BOX_HEIGHT_PROBE.md
git commit -m "docs(zeroloc): height-scaling probe -- achieved kernel-certified RH-in-box ceiling"
```

**Acceptance:** an honest findings doc naming the achieved ceiling T* and the binding constraint; any committed higher-T instantiation builds sorry-free with clean axioms.

---

## Self-Review

**Spec coverage:** Generic-corner core (spec S3) -> Tasks 1 (counting) + 2 (analytic) + 3 (assembly). Per-box pipeline (S4) -> Task 4. Scale-to-T + milestone + probe (S5) -> Tasks 5 (T=100) + 6 (probe). Trust boundary + honest ceiling (S2/S9) -> every task's constraints (winding Arb-carried, `conjecture1_proved=False`). Testing (S7): regression on `[10,35]` -> Task 3; new `[0,100]` -> Task 5; negative controls (invalid box, `N_line != N`) -> Task 4; drift + axioms + SoC-safe + optional-dep guards -> Tasks 1,4,5. All spec sections mapped.

**Placeholder scan:** research-grade Lean (Tasks 1-3) specified by exact theorem STATEMENT + named lemmas + template file (the merged `BoxLocalization`/`BlaschkeBox`/`BoxArgPrincipleZeta`) + acceptance (sorry-free, clean axioms) — the honest granularity for kernel proofs. The `<...>` placeholders in Task 2's `hwind`/`harb` are deliberately the "copy the merged theorem's exact boundary-integral and integrability hypotheses, with literals -> variables" instruction, not vague TODOs; the merged `BoxArgPrincipleZeta.lean` is the concrete source. Python tasks (4) carry full test + implementation detail.

**Type consistency:** `rh_in_box_core` (Task 1) corners `(sigma0..T1 : R)`, `T : Finset C`, `d : C -> Z`, `hcount : sum d = T.card` -> consumed by `rh_in_box_of_certificate` (Task 3) with the same names/types. `zeta_count_eq_winding_generic` (Task 2) returns `exists s d, hd1 and hzero_in and sum d = N` -> Task 3 `obtain`s exactly that. `N : Z`, `hcount : N = T.card` consistent Task 2->3. The driver (Task 4) supplies corners + `(c,R)` + `T` (Finset of `N_line` on-line zeros) + `N` matching the Task 3 signature. `box_localization_certificate` corner strings (`re_lo/re_hi/im_lo/im_hi`) already exist; extended with validity refusals.

**Risk note (controller):** Task 2 (parameterized Blaschke/arg-principle over a variable ball) is the hard core; the merged `BoxArgPrincipleZeta.lean` is a verbatim template with literals->variables. If full generality blocks after real effort, fall back (controller ruling) to Task-3-as-emit-per-box (substitute corner literals into a copy of the merged proof), which still delivers parameterization at the cost of a Lean file per box. Task 6 is a bounded probe with a wall-clock budget; the ceiling is reported, not chased indefinitely.
