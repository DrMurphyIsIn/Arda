# dVP + Box-Localization: All Zeros up to Height T on the Line — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Kernel-verify that ALL nontrivial zeros of the Riemann zeta function up to a finite height T lie on Re=1/2, by combining the effective dVP zero-free region (PR #316) + the functional equation + the parameterized box-localization (PR #312).

**Architecture:** dVP-effective + functional equation + a multiplicity bridge confine every zero up to T to a band `(delta_T, 1-delta_T)` with `delta_T = dlvpRateC/log T` (computable, since `dlvpRateC` is explicit); a concrete box `[a,1-a]x[0,T]` with `a <= dlvpRateC/log T` (a discharge-able `norm_num` inequality) therefore contains every zero, and `rh_in_box_of_certificate` puts the in-box zeros on the line. A Task-1 feasibility probe gates the extreme-precision (`a~1e-6`) concrete build; NO-GO falls back to the reduction-theorem framing.

**Tech Stack:** Lean 4 + Mathlib (kernel), Python 3.14 Telperion driver (Arb/python-flint), first-class emitter pattern.

**Spec:** `telperion/docs/superpowers/specs/2026-09-07-dvp-box-combination.md`

## Global Constraints

- Object: `riemannZeta`. Nontrivial zeros = zeros in `0 < Re < 1` (Mathlib `riemannZeta_ne_zero_of_one_le_re` gives none with `Re >= 1`; functional equation gives none with `Re <= 0`). Pole at `s=1` excluded from every box.
- Trust boundary (unchanged from #285/#312): winding integer N, edge non-vanishing, value enclosures = documented NON-KERNEL Arb input (theorem hypotheses). dVP-effective (#316), functional equation, and the multiplicity bridge are KERNEL. The kernel proves the implication. `conjecture1_proved = False` in every artifact. Complete FINITE Turing statement, NOT a proof of RH.
- No emoji. No `set_option linter.unusedVariables false` (a `maxHeartbeats` budget is allowed). Acceptance for every Lean deliverable: sorry-free, `#print axioms` = `{propext, Classical.choice, Quot.sound}` (no `sorryAx`), built lakefile target.
- Python: `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3` (3.14.6; flint 0.9.0). Run from `.../telperion`.
- Lean: `/Users/peterwmurphy/.elan/bin/lake`; local builds OK; ALWAYS `lake exe cache get` before `lake build`; NEVER a cold Mathlib compile.
- Optional-dep hygiene: new flint tests `@requires_flint`; Lean-build tests `@requires_lake`.
- On-main interfaces (verified):
  - `ZeroFreeBridge.dlvp_zeta_region_rate_effective (β γ : ℝ) (k : ℤ) (h34 : 3/4 ≤ β) (hβ1 : β < 1) (hΓ : 55/16 ≤ |γ|) (hk : 1 ≤ k) (hmρ₀ : MeromorphicOn.divisor riemannZeta (Metric.ball ((2:ℂ)+(γ:ℂ)*I) (11/8)) ((β:ℂ)+(γ:ℂ)*I) = k) : β ≤ 1 - ZeroFreeBridge.dlvpRateC / Real.log |γ|` (in `DlvpZetaRateEffective.lean`). `dlvpRateC : ℝ := 1/(112*16*dlvpRateK)` noncomputable; `dlvpRateC_pos : 0 < dlvpRateC`.
  - `RHInBox.rh_in_box_of_certificate (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ) (hRpos) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1) (hbox_ball) (hs1 : (1:ℂ) ∉ ball c R) (T : Finset ℂ) (hTline hTzero hTbox hwind harb) : ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) → riemannZeta ρ = 0 → ρ.re = 1/2` (`RHInBox.lean`).

---

### Task 1: Feasibility probe (extreme-precision concrete box edge) -- GATES the concrete build

**Files:**
- Create: `telperion/docs/DVP_BOX_FEASIBILITY_PROBE.md` (findings)
- Create (throwaway, may carry a LABELED sorry, NOT CI-wired): `telperion/examples/zeta_zero_localization/lean/DvpBoxProbe.lean`

**Interfaces:**
- Consumes: `dlvpRateC` (unfold its closed form), `generate.py`'s `run_box` (PR #312 driver), `enclose_zeta_segments`.
- Produces: a GO/NO-GO verdict + the concrete `a` value that works.

**Goal:** confirm the three risks in spec Section 4 before committing the full concrete build.

- [ ] **Step 1: Compute `dlvpRateC` and `delta_100 = dlvpRateC/log 100` numerically (Python).** Unfold `dlvpRateC = 1/(112*16*dlvpRateK)` with `dlvpRateK` built from `pi, log(23/22), log(15/(2-pi^2/6))` (read `DlvpZetaRateEffective.lean` + `DlvpZetaRate*.lean` for `dlvpRateK`'s exact closed form). Compute its float value and a safe rational LOWER bound `dlvpRateC >= p/q`. Compute `log 100 < 47/10` (check `47/10 = 4.7 > log 100 = 4.605`). Pick a concrete rational `a` (e.g. `a = 1/10^6`) and verify `a <= (p/q)/(47/10)` i.e. `a <= dlvpRateC/log 100` holds with margin. Record the numbers.

- [ ] **Step 2: Confirm the Arb winding over the wide box.** Run `run_box("1/1000000", "999999/1000000", "0", "100", write=False)` (PR #312 driver). Confirm: it computes winding `N = 29`; `N_line = 29`; no segment-box straddles 0; the driver's `choose_ball` produces a ball with `s=1` strictly outside (its exact-rational `R^2` midpoint between farthest corner and `s=1`). Record the segment count, emit time, and whether it succeeds or raises. If the winding is intractable at this width/precision, try a slightly larger `a` (still `<= delta_100`) and record.

- [ ] **Step 3: Confirm the `norm_num` discharges (small Lean toy).** In `DvpBoxProbe.lean` (NOT wired into any lakefile `defaultTargets`, not imported by a built target), write and build two `example`s: (a) `example : (1/10^6 : ℝ) <= 1 - (999999/10^6 : ℝ) ... ` -- no; instead (a) the geometric facts the driver-emitted box needs at `a=1e-6` (`box ⊆ ball`, `1 ∉ ball`) via `nlinarith`/`norm_num` on the concrete `c, R` the driver picked; (b) the effective-rate inequality `(1/10^6 : ℝ) <= dlvpRateC / Real.log 100` -- if this needs `dlvpRateC`'s closed form + a `Real.log 100` bound, sketch the discharge (a `sorry` labeled with the exact missing lemma is acceptable in this throwaway probe). Confirm (a) builds sorry-free; assess (b)'s tractability.

- [ ] **Step 4: Write `DVP_BOX_FEASIBILITY_PROBE.md` + verdict.** GO if all three risks clear (the `a` value, the Arb winding=29, the geometry norm_num, and a tractable path for the effective-rate inequality). NO-GO if the extreme precision breaks Arb or the effective-rate `norm_num` is intractable -- then the concrete T=100 build (Task 5) is replaced by the reduction-theorem framing (Task 4's theorem stated with `a <= dlvpRateC/log T` as a hypothesis, not discharged). Record the chosen concrete `a`. `conjecture1_proved = False`.

- [ ] **Step 5: Commit.**
```bash
git add telperion/docs/DVP_BOX_FEASIBILITY_PROBE.md telperion/examples/zeta_zero_localization/lean/DvpBoxProbe.lean
git commit -m "docs(dvp-box): feasibility probe for the concrete all-zeros-up-to-100 certificate (GO/NO-GO)"
```

**Acceptance:** a findings doc with a clear GO/NO-GO, the concrete `a` that works, the Arb winding result at that width, and the effective-rate discharge assessment; probe Lean NOT CI-wired.

---

### Task 2: The multiplicity bridge (kernel) -- DROPPED (subsumed by PR #318)

**PLAN REVISION 2026-09-07:** PR #318 (`ZeroFreeBridge.zeta_zero_divisor_pos` + the self-contained `riemannZeta_ne_zero_region`, on `main`) makes this task redundant -- the multiplicity bridge is built AND the region theorem needs no multiplicity input at all. SKIP Task 2. Task 3 (revised) consumes `riemannZeta_ne_zero_region` directly. The original Task 2 text below is retained for the record but NOT executed.



**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/ZetaZeroMult.lean`
- Modify: `telperion/examples/zeta_zero_localization/lean/lakefile.toml`
- Test: `telperion/tests/test_dvp_box.py` (build assertion, `@requires_lake`)

**Interfaces:**
- Consumes: Mathlib `differentiableAt_riemannZeta`, `analyticAt`/`analyticOrderAt` API, `MeromorphicOn.divisor`.
- Produces: `ZetaZeroMult.zeta_zero_divisor_pos` (signature below).

- [ ] **Step 1: Write the failing build test** (`test_zeta_zero_mult_builds`, `@requires_lake`, mirrors the PR #312 `test_rhinbox.py` build-test pattern: `lake exe cache get` then `lake build ZetaZeroMult`, assert returncode 0).

- [ ] **Step 2: Run to verify it fails.**

- [ ] **Step 3: Write `ZetaZeroMult.lean`.**
```lean
import Mathlib
open Complex MeromorphicOn Metric
namespace ZetaZeroMult

/-- A zeta zero inside the ball has divisor (multiplicity) at least 1. -/
theorem zeta_zero_divisor_pos {ρ : ℂ} {γ : ℝ}
    (hρ1 : ρ ≠ 1)
    (hmem : ρ ∈ Metric.ball ((2 : ℂ) + (γ : ℂ) * I) (11/8))
    (hzero : riemannZeta ρ = 0) :
    1 ≤ MeromorphicOn.divisor riemannZeta (Metric.ball ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ρ := by
  ...
```
**Strategy:** `riemannZeta` is analytic at `ρ` (`differentiableAt_riemannZeta hρ1`), and not identically 0, so `analyticOrderAt riemannZeta ρ` is a positive natural (zero of finite positive order) -- use `AnalyticAt.analyticOrderNatAt_pos_iff` (or the `analyticOrderAt`/`meromorphicOrderAt` bridge) with `hzero`. Then `MeromorphicOn.divisor riemannZeta (ball ...) ρ = analyticOrderAt riemannZeta ρ` at an interior zero (via `MeromorphicOn.divisor_apply` on the ball where `riemannZeta` is meromorphic -- `s=1` may or may not be in this ball; note the ball `ball (2+γI) (11/8)` has center `Re=2`, radius `11/8`, so it reaches `Re` in `(2-11/8, 2+11/8) = (5/8, 27/8)`; `s=1` has `Re=1 < 5/8`? NO, `1 > 5/8`, so `s=1` COULD be in this ball when `γ` is small -- but `|1 - (2+γI)| = sqrt(1 + γ^2) >= 1`; ball radius `11/8 = 1.375`; so `s=1 ∈ ball` iff `sqrt(1+γ^2) < 11/8` iff `γ^2 < 121/64 - 1 = 57/64` iff `|γ| < ~0.94`. Since our zeros have `|γ| >= 14`, `s=1 ∉` this ball, so `riemannZeta` is ANALYTIC on the ball and `divisor = analyticOrderAt >= 1`.) Add the `|γ|` hypothesis if needed to place `s=1` outside, OR keep `hρ1` + the ball-membership and derive analyticity on the ball from the zero's height. **If a Mathlib gap blocks the `divisor = analyticOrderAt >= 1` step after real effort, report BLOCKED with the exact lemma; the controller may carry `k>=1` as a documented hypothesis in Tasks 3-4 (spec Section 5 fallback).**

- [ ] **Step 4: Add `ZetaZeroMult` to `lakefile.toml` (lib + defaultTarget); build + axiom check** (`lake build ZetaZeroMult`; `#print axioms zeta_zero_divisor_pos` clean).

- [ ] **Step 5: Run the build test + commit.**
```bash
git add telperion/examples/zeta_zero_localization/lean/ZetaZeroMult.lean telperion/examples/zeta_zero_localization/lean/lakefile.toml telperion/tests/test_dvp_box.py
git commit -m "feat(dvp-box): multiplicity bridge -- zeta zero in ball has divisor >= 1 (kernel)"
```

**Acceptance:** `zeta_zero_divisor_pos` builds sorry-free, clean axioms; genuinely derives `divisor >= 1` from `riemannZeta ρ = 0` (not assumed).

---

### Task 3: The confinement lemma (kernel)

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/ZetaZeroConfinement.lean`
- Modify: `lakefile.toml`
- Test: `telperion/tests/test_dvp_box.py`

**Interfaces (REVISED -- consume PR #318's self-contained region; Task 2 dropped):**
- Consumes: `ZeroFreeBridge.riemannZeta_ne_zero_region (β γ : ℝ) (hγ : 55/16 ≤ |γ|) (hβlow : 1 - dlvpRateC / Real.log |γ| < β) : riemannZeta ((β:ℂ)+(γ:ℂ)*I) ≠ 0` (DlvpZetaZeroFree.lean, on main -- SELF-CONTAINED, NO multiplicity input, β≥3/4 handled internally); `ZeroFreeBridge.dlvpRateC`/`dlvpRateC_pos`; Mathlib functional equation (`completedRiemannZeta_one_sub`); `BoxLocalization.zeta_zero_iff_completed_zero` (strip bridge); `riemannZeta_ne_zero_of_one_le_re`.
- Produces: `ZetaZeroConfinement.zero_in_band` (signature below).

- [ ] **Step 1: Write the failing build test** (`test_zeta_confinement_builds`, `@requires_lake`, target `ZetaZeroConfinement`).

- [ ] **Step 2: Run to verify it fails.**

- [ ] **Step 3: Write `ZetaZeroConfinement.lean`.**
```lean
theorem zero_in_band (a T : ℝ) (haC : a ≤ ZeroFreeBridge.dlvpRateC / Real.log T)
    (ha0 : 0 < a) (hT : 100 ≤ T)   -- log T > 0 and 55/16 < first-zero height threshold
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (him0 : 0 < ρ.im) (himT : ρ.im ≤ T) :
    a ≤ ρ.re ∧ ρ.re ≤ 1 - a := by
  ...
```
**Strategy (REVISED -- `riemannZeta_ne_zero_region` is self-contained; NO multiplicity, NO β≥3/4 casework):** let `β = ρ.re`, `γ = ρ.im`, `0 < γ ≤ T`.
- **Height floor:** `55/16 ≤ |γ|` -- there are no nontrivial zeros with `0 < |γ| < 14` (first zero `~14.13`), `55/16 ~ 3.44 < 14`. If Mathlib lacks a "no low zeros" lemma, carry `55/16 ≤ |γ|` as a documented hypothesis on `zero_in_band` (honest, small classical fact) -- the concrete T=100 instantiation discharges it from the on-line sweep (all 29 zeros have `γ ≥ 14`).
- **Right edge (`β ≤ 1-a`):** the CONTRAPOSITIVE of `riemannZeta_ne_zero_region`. Since `riemannZeta ((β:ℂ)+(γ:ℂ)*I) = 0` (i.e. `ρ`, with `ρ = (β:ℂ)+(γ:ℂ)*I` after `Complex.re/im` normalization) and `55/16 ≤ |γ|`, we CANNOT have `1 - dlvpRateC/log|γ| < β`, so `β ≤ 1 - dlvpRateC/log|γ|`. Then `dlvpRateC/log|γ| ≥ dlvpRateC/log T ≥ a` (`log|γ| ≤ log T` monotone since `|γ| = γ ≤ T`; `dlvpRateC > 0` via `dlvpRateC_pos`; `haC`), so `β ≤ 1 - a`. (No `β ≥ 3/4` split -- the region theorem discharges it internally.)
- **Left edge (`a ≤ β`):** apply the region to the FE-reflected zero. From `riemannZeta ρ = 0` (strip, `0 < β`) get `completedRiemannZeta ρ = 0` (`zeta_zero_iff_completed_zero`), then `completedRiemannZeta (1-ρ) = 0` (`completedRiemannZeta_one_sub`), then `riemannZeta (1-ρ) = 0` (strip bridge, `0 < (1-ρ).re = 1-β`). The reflected zero `1-ρ = (1-β) + (-γ)*I` has real part `1-β`, `|(-γ)| = |γ| ≥ 55/16`. Contrapositive of the region on `1-ρ`: `1-β ≤ 1 - dlvpRateC/log|γ| ≤ 1 - a`, i.e. `β ≥ a`.
- **Strip `0 < β < 1`:** `β < 1` from `riemannZeta_ne_zero_of_one_le_re`; `β > 0` from the reflected-zero argument (or the nontrivial-strip fact) -- needed so `zeta_zero_iff_completed_zero` (which needs `0 < re`) applies to `ρ`. If `0 < β` needs its own small argument, obtain it from `riemannZeta_ne_zero_of_one_le_re` applied to `1-ρ` (`(1-ρ).re = 1-β ≥ 1` would force `β ≤ 0`; contrapositive gives `β > 0` once `ζ(1-ρ)=0`, which needs `0 < β` first -- so instead get `0 < β` directly from Mathlib's nontrivial-zero-in-strip fact if available, else carry `0 < β < 1` as a documented hypothesis, honest).
- Combine both edges: `a ≤ β ≤ 1-a`.
(The exact FE + conjugate-symmetry lemma names are the implementer's to find; `completedRiemannZeta_one_sub` is the FE. Note the reflected zero is at height `-γ`; the region's `|γ|` hypothesis uses absolute value so `-γ` is fine, but a conjugate-symmetry step `ζ(s̄)=conj ζ(s)` may be needed to land the reflected zero at height `+γ` if a Mathlib lemma requires it -- the implementer resolves this.)

- [ ] **Step 4: lakefile + build + axiom check** (clean).

- [ ] **Step 5: Run the build test + commit.**
```bash
git add telperion/examples/zeta_zero_localization/lean/ZetaZeroConfinement.lean telperion/examples/zeta_zero_localization/lean/lakefile.toml telperion/tests/test_dvp_box.py
git commit -m "feat(dvp-box): confinement -- every nontrivial zero up to T lies in [a,1-a] (dVP+FE, kernel)"
```

**Acceptance:** `zero_in_band` builds sorry-free, clean axioms; genuinely derives `a ≤ β ≤ 1-a` from `riemannZeta_ne_zero_region` (#318, self-contained) + FE (not assumed); `a` and `T` are free variables with `a ≤ dlvpRateC/log T` as the load-bearing hypothesis. Any residual (`55/16 ≤ |γ|` no-low-zeros, or `0 < β < 1` strip) carried as a documented honest hypothesis if a Mathlib gap forces it. NO multiplicity input, NO `β ≥ 3/4` casework (the region theorem discharges both).

---

### Task 4: The combination theorem (kernel)

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/AllZerosUpToHeight.lean`
- Modify: `lakefile.toml`
- Test: `telperion/tests/test_dvp_box.py`

**Interfaces:**
- Consumes: `ZetaZeroConfinement.zero_in_band` (Task 3), `RHInBox.rh_in_box_of_certificate` (PR #312).
- Produces: `AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line` (signature below).

- [ ] **Step 1: Write the failing build test** (`test_all_zeros_up_to_height_builds`, `@requires_lake`, target `AllZerosUpToHeight`).

- [ ] **Step 2: Run to verify it fails.**

- [ ] **Step 3: Write `AllZerosUpToHeight.lean`.** The generic combination, parameterized by `a`, `T`, the ball `(c,R)`, `N`, the on-line Finset, and the Arb bundle:
```lean
theorem all_nontrivial_zeros_up_to_height_on_line
    (a T : ℝ) (haC : a ≤ ZeroFreeBridge.dlvpRateC / Real.log T) (ha0 : 0 < a) (hT : 100 ≤ T)
    (c : ℂ) (R : ℝ) (N : ℤ) (hRpos : 0 < R) (hbox_ball : ...) (hs1 : (1:ℂ) ∉ Metric.ball c R)
    (Ton : Finset ℂ) (hTline hTzero hTbox hwind harb : ...)   -- the rh_in_box_of_certificate bundle at box [a,1-a]x[0,T]
    : ∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1/2 := by
  intro ρ hzero him0 himT
  obtain ⟨hlo, hhi⟩ := ZetaZeroConfinement.zero_in_band a T haC ha0 hT hzero him0 himT
  exact rh_in_box_of_certificate a (1-a) 0 T c R N hRpos (by linarith) (by linarith)
    hbox_ball hs1 Ton hTline hTzero hTbox hwind harb ρ ⟨hlo, hhi⟩ ⟨le_of_lt him0, himT⟩ hzero
```
(match `rh_in_box_of_certificate`'s exact argument order; `sigma0=a, sigma1=1-a, T0=0, T1=T`. `hsig : a ≤ 1-a` from `a ≤ 1/2`; `hT : 0 ≤ T`.)

- [ ] **Step 4: lakefile + build + axiom check** (clean; `N` free, non-circular -- the "on line" conclusion comes from `rh_in_box_of_certificate` + `zero_in_band`, not assumed).

- [ ] **Step 5: Run the build test + commit.**
```bash
git add telperion/examples/zeta_zero_localization/lean/AllZerosUpToHeight.lean telperion/examples/zeta_zero_localization/lean/lakefile.toml telperion/tests/test_dvp_box.py
git commit -m "feat(dvp-box): all nontrivial zeros up to height T on Re=1/2 (combination theorem, kernel)"
```

**Acceptance:** `all_nontrivial_zeros_up_to_height_on_line` builds sorry-free, clean axioms; `a, T, N` free; the conclusion (all zeros up to T on line) derived from confinement + box-localization; the Arb bundle + `a ≤ dlvpRateC/log T` are the documented hypotheses.

---

### Task 5: Concrete T=100 certificate (Task-1-probe-gated) + docs

**Files:**
- Create (emitted/committed): `telperion/examples/zeta_zero_localization/lean/AllZeros_h100.lean` (or a section instantiating Task 4 at `a=<probe value>`, `T=100`)
- Modify: `generate.py` (a helper wiring the wide-box Arb data into the Task-4 instantiation), `ZETA_ZERO_LOCALIZATION_STATUS.md`, `README.md`, `CHANGELOG.md`, CI YAML
- Test: `telperion/tests/test_dvp_box.py`

**Interfaces:** Consumes Task 4 + the PR #312 `--box` driver + Task 1's chosen `a`.

- [ ] **Step 1: Branch on Task 1's verdict (controller ruling in the dispatch).** If Task 1 = NO-GO: SKIP the concrete instantiation; instead state Task 4's theorem as the deliverable with `a ≤ dlvpRateC/log T` as an explicit hypothesis (the reduction framing), update docs to say "reduces RH-up-to-T to the wide-box winding + the effective-rate inequality", commit, done. If GO: proceed.

- [ ] **Step 2 (GO): Emit the wide-box Arb bundle + discharge the effective-rate inequality.** Use the driver at `--box <a>,<1-a>,0,100` (Task-1 `a`) to produce the winding `N=29`, on-line Finset (29 zeros), edge non-vanishing, and the Blaschke ball. Prove `a ≤ dlvpRateC / Real.log 100` by `norm_num` (unfold `dlvpRateC`'s closed form for a rational lower bound; `Real.log 100 < 47/10` upper bound) -- per Task 1's confirmed discharge path.

- [ ] **Step 3 (GO): Instantiate Task 4 -> `AllZeros_h100`.** `all_nontrivial_zeros_up_to_height_on_line (a:=<a>) (T:=100) ...` with all hypotheses discharged (geometry `norm_num`, Arb bundle from the driver, effective-rate inequality from Step 2). Register as a committed `lean_lib`. Build: sorry-free; `#print axioms` = `{propext, Classical.choice, Quot.sound}`. Conclusion: **`∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100 → ρ.re = 1/2`.**

- [ ] **Step 4: Docs.** `STATUS`/`README`/`CHANGELOG`: headline "ALL nontrivial zeros up to height 100 lie on Re=1/2 (complete finite Turing verification, kernel-checked)"; the non-effective-c caveat REMOVED; the multiplicity-bridge + any `55/16 ≤ γ` residual noted; winding/edge/enclosures = Arb non-kernel input; dVP+FE+multiplicity = kernel; `conjecture1_proved = False`; NOT a proof of RH.

- [ ] **Step 5: CI + test.** Extend the zeta CI to build `ZetaZeroMult ZetaZeroConfinement AllZerosUpToHeight AllZeros_h100`; add a `@requires_lake` build-assertion + a `@requires_flint` agreement test (`N == N_line == 29` for the wide box). Validate YAML.

- [ ] **Step 6: Commit.**
```bash
git add -A telperion/ .github/
git commit -m "feat(dvp-box): concrete certificate -- ALL nontrivial zeros up to height 100 on Re=1/2"
```

**Acceptance (GO):** `AllZeros_h100` builds sorry-free, clean axioms; conclusion is the genuine unweighted "all zeros up to 100 on Re=1/2"; `a ≤ dlvpRateC/log 100` discharged concretely; docs honest. **Acceptance (NO-GO):** Task 4's reduction theorem is the deliverable with the effective-rate inequality as a hypothesis; docs honestly framed.

---

### Task 6: CI axiom-guard tier elevation

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/AxiomGuardRHInBox.lean` (mirrors `AxiomGuardDlvp.lean` on main)
- Modify: `.github/workflows/telperion-lean-e2e.yml` (add the guard job)
- Test: `telperion/tests/test_dvp_box.py` (negative control)

**Interfaces:** Consumes the RH-in-box family theorems.

- [ ] **Step 1: Read `AxiomGuardDlvp.lean` on main** for the exact `#print axioms` / fail-on-`sorryAx` pattern (`git show origin/main:telperion/examples/zero_free_bridge/lean/AxiomGuardDlvp.lean`).

- [ ] **Step 2: Write `AxiomGuardRHInBox.lean`.** `#print axioms` on: `RHInBox.rh_in_box_of_certificate`, `RHInBox.rh_in_box_10_35`, the `RHInBox_2d5_3d5_0_100` theorem, `AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line`, and (if Task 5 GO) `AllZeros_h100`'s theorem. Follow the AxiomGuardDlvp structure (a file whose build + a CI grep step fail if `sorryAx` or any axiom outside `{propext, Classical.choice, Quot.sound}` appears).

- [ ] **Step 3: Add the CI job `axiom-guard-rh-in-box`** to the workflow (warm `lake exe cache get`, build the guard target, grep the output for `sorryAx`/unexpected axioms -> fail). Validate YAML.

- [ ] **Step 4: Negative control.** A `@requires_lake` test (or a documented manual check) that injecting a `sorry` into a copy of a guarded theorem makes the guard FAIL -- proving the guard bites.

- [ ] **Step 5: Commit.**
```bash
git add telperion/examples/zeta_zero_localization/lean/AxiomGuardRHInBox.lean .github/workflows/telperion-lean-e2e.yml telperion/tests/test_dvp_box.py
git commit -m "ci(dvp-box): axiom-guard the RH-in-box family (fail on sorryAx) -- CI-axiom-guarded tier"
```

**Acceptance:** the RH-in-box family is `#print axioms`-guarded in CI with fail-on-`sorryAx`; the negative control confirms the guard bites; the "CI-axiom-guarded tier" phrase is earned.

---

## Self-Review

**Spec coverage:** Combination theorem (spec S3) -> Tasks 2 (multiplicity), 3 (confinement), 4 (combination). Feasibility probe (S4) -> Task 1. Multiplicity bridge (S5) -> Task 2. Concrete T=100 + range (S6) -> Task 5. CI axiom-guard (S7) -> Task 6. Trust boundary + honest ceiling (S2/S11) -> every task's constraints (`conjecture1_proved=False`, Arb-non-kernel-input). Testing (S9) -> each task's build/axiom/negative-control steps. All spec sections mapped.

**Placeholder scan:** research-grade Lean (Tasks 2,3,4) specified by exact theorem STATEMENT + named Mathlib/on-main lemmas + strategy + acceptance (sorry-free, clean axioms) -- the honest granularity for kernel proofs. Task 1 is a probe (findings). Task 5 branches on Task 1's verdict (GO concrete / NO-GO reduction). No naked TODOs.

**Type consistency:** `zeta_zero_divisor_pos` (Task 2, `divisor ... ρ >= 1`) feeds `dlvp_zeta_region_rate_effective`'s `hk : 1 <= k` and `hmρ₀` in Task 3. `zero_in_band` (Task 3, `a <= ρ.re <= 1-a` from `a <= dlvpRateC/log T`) feeds Task 4's box membership. `all_nontrivial_zeros_up_to_height_on_line` (Task 4) instantiated in Task 5 at `a=<probe>, T=100`. `rh_in_box_of_certificate`'s exact arg order `(sigma0 sigma1 T0 T1 c R N hRpos hsig hT hbox_ball hs1 T hTline hTzero hTbox hwind harb)` used verbatim in Task 4. `dlvpRateC` / `dlvpRateC_pos` from #316 consistent Tasks 1,3,4,5.

**Risk note (controller):** Task 3 (confinement, the FE-reflection + both-edge dVP argument) is the hard kernel core; the FE lemma `completedRiemannZeta_one_sub` + the strip bridge are the load-bearing Mathlib pieces. Task 2's `divisor = analyticOrderAt >= 1` step may hit a Mathlib gap (carry `k>=1` as a documented hypothesis if so -- spec S5). Task 1 gates the concrete build (extreme `a~1e-6`); NO-GO cleanly degrades Task 5 to the reduction framing. Any `55/16 <= γ` "no low zeros" residual is a documented honest hypothesis if Mathlib lacks it.
