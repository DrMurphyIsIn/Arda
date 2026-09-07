import Mathlib

/-!
# Task-1 feasibility probe: DvpBoxProbe (dVP + box combination)

PROBE ARTIFACT — NOT CI-WIRED.  It is NOT declared in `lakefile.toml`
`defaultTargets` and is imported by NO built target, so the example's
`lake build` never compiles it.  It is an inert file kept alongside the
findings doc `docs/DVP_BOX_FEASIBILITY_PROBE.md`.  A single LABELED `sorry`
sits in the effective-rate `example` (Risk 3(b)) marking the exact Mathlib gap.

Purpose: confirm the two `norm_num`/`nlinarith` geometry discharges the PR #312
driver emits for the EXTREME-PRECISION box `[1/10^6, 1-1/10^6] x [0, 100]`
build sorry-free, and to SKETCH the effective-rate inequality
`(1/10^6 : ℝ) ≤ dlvpRateC / Real.log 100` discharge.

The ball `choose_ball` picks for this box (verified by the Python driver):
  center  cPB = ⟨1/2, 50⟩
  radius² RPB² = 5000499999000001 / 2000000000000   (≈ 2500.24999950)
  box corner-dist²  dc2 = 2500249999000001 / 1000000000000  (≈ 2500.24999900)
  pole s=1 dist²    d12 = 10001/4                              (= 2500.25)
so  dc2 < RPB² < d12  (box strictly inside, pole strictly outside) — but the
three values agree to ~10 significant figures, so the `nlinarith`/`norm_num`
must separate rationals differing by ~5e-7 relative.  That is the risk.

conjecture1_proved = False.
-/

open Complex

namespace DvpBoxProbe

/-- Chosen Blaschke ball center for the box `[1/10^6, 1-1/10^6] x [0, 100]`
    (exactly what `choose_ball` returns). -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (50)⟩

/-- Chosen radius: `RPB = sqrt(5000499999000001 / 2000000000000)`. -/
noncomputable def RPB : ℝ := Real.sqrt ((5000499999000001 / 2000000000000))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

/-- **Risk 3(a), part 1 — box ⊆ ball, sorry-free.**  Every `ρ` in the box
    `[1/10^6, 1-1/10^6] x [0,100]` lies in `Metric.ball cPB RPB`.  This is the
    EXACT proof term the PR #312 driver emits (`hbox_ball`), reproduced verbatim
    at the `a = 1e-6` width to test the `nlinarith` at extreme precision. -/
theorem hbox_ball_probe :
    ∀ ρ : ℂ, ((((1 / 1000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((999999 / 1000000))) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) → ρ ∈ Metric.ball cPB RPB := by
  intro ρ hre him
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  apply Real.sqrt_lt_sqrt (by positivity)
  have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
  nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (50))]

/-- **Risk 3(a), part 2 — pole s = 1 ∉ ball, sorry-free.**  The pole `s = 1`
    is strictly OUTSIDE `Metric.ball cPB RPB`.  Verbatim driver `hs1`. -/
theorem hs1_probe : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((5000499999000001 / 2000000000000)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (50)) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-!
## Risk 1 / 3(b): the effective-rate inequality `a ≤ dlvpRateC / Real.log 100`.

`dlvpRateC = 1 / (112 * 16 * dlvpRateK)` with
`dlvpRateK = 1 + 2 * ((8 / (3 * Real.log ((23/16)/(11/8))) + 608/9) / 16)
              * (Real.log (15 / (2 - π²/6)) + 1)`.

Numerics (mpmath, 50 dps):
  dlvpRateK ≈ 76.6266,  dlvpRateC ≈ 7.28253e-6,  log 100 ≈ 4.60517,
  delta_100 = dlvpRateC / log 100 ≈ 1.58138e-6,   a = 1e-6 ≤ delta_100  (margin 1.58×).

A SAFE RATIONAL LOWER BOUND (all bounds themselves rationally provable):
  Real.log ((23/16)/(11/8)) = Real.log (23/22) ≥ 444/10000
      [since exp(444/10000) ≈ 1.045400 ≤ 23/22 = 1.045454…],
  Real.log (15/(2-π²/6)) ≤ 3744/1000
      [since 15/(2-π²/6) ≈ 42.2457 ≤ exp(3.744) ≈ 42.2667],
  ⟹  dlvpRateK ≤ 76.67607  ⟹  dlvpRateC ≥ 41625/5719420672 ≈ 7.27784e-6.
  Real.log 100 ≤ 47/10   [= 4.7 > 4.60517].
  Hence  dlvpRateC / Real.log 100 ≥ (41625/5719420672) / (47/10) ≈ 1.54848e-6 ≥ 1e-6
  (margin 1.548×).

The Lean discharge chain (each step a standard Mathlib lemma, all EXIST in v4.32.0):
  1. `Real.add_pow_le_pow_mul_pow_of_sqrt`-free — pure `Real.log` monotonicity:
     `Real.le_log_iff_exp_le` / `Real.log_le_iff_le_exp` to turn the two `log`
     bounds into `exp`-form rational inequalities, then `Real.exp_le_exp` +
     an `Real.exp` lower/upper numeric bound (`Real.exp_one_lt_d9`-style, or
     `Real.add_one_le_exp` for the lower `log(23/22) ≥ 444/10000` via
     `exp(444/10000) ≤ 1 + 444/10000 · (…)` — cleanest: `Real.exp_le_exp` with
     a rational upper enclosure of `exp`).
  2. Substitute the two `log` bounds into `dlvpRateK`'s closed form to get the
     rational `dlvpRateK ≤ 76.67607` (a `nlinarith`/`gcongr` monotonicity step;
     note `8/(3·L)` is DECREASING in `L`, so the LOWER bound on `L=log(23/22)`
     gives the UPPER bound on that term — direction handled by `gcongr`).
  3. `dlvpRateC = 1/(112·16·K) ≥ 1/(112·16·K_upper)` by `one_div_le_one_div_of_le`.
  4. `Real.log 100 ≤ 47/10` via `Real.log_le_iff_le_exp` + `exp(4.7) ≥ 100`
     (or reuse the repo's existing `Real.log 100 < 47/10` lemma if present).
  5. `dlvpRateC / Real.log 100 ≥ C_lower / (47/10) ≥ 1e-6` by `div_le_div`
     monotonicity + a final `norm_num`.

TRACTABILITY: GO.  Every lemma above exists in Mathlib v4.32.0 and the repo
already discharges `Real.log (23/16 / (11/8))`-flavoured and `2 - π²/6 > 0`
facts in `DlvpZetaRateEffective.lean` (`two_sub_pi_sq_div_six_pos`,
`Real.log_pos`, `Real.log_nonneg`).  The ONLY genuinely new numeric ingredient
is the two `Real.exp` rational enclosures (steps 1 and 4), which are routine.

The `example` below states the target with a SINGLE LABELED `sorry` marking the
exact missing lemma — it is NOT a claim, just the probe's placeholder. -/

/-- `dlvpRateK`, copied from `ZeroFreeBridge.dlvpRateK` (kept local so this probe
    does not import the whole `zero_free_bridge` lib). -/
noncomputable def dlvpRateK : ℝ :=
  1 + 2 * ((8 / (3 * Real.log ((23/16) / (11/8))) + 608/9) / 16)
        * (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1)

/-- `dlvpRateC`, copied from `ZeroFreeBridge.dlvpRateC`. -/
noncomputable def dlvpRateC : ℝ := 1 / (112 * 16 * dlvpRateK)

/-- **Risk 1 / 3(b): the effective-rate box-edge inequality.**  The chosen
    `a = 1/10^6` satisfies `a ≤ dlvpRateC / Real.log 100`.  LABELED `sorry`:
    the missing ingredient is `dlvpRateC ≥ 41625/5719420672` (via the two
    `Real.log`↔`Real.exp` rational enclosures sketched above) together with
    `Real.log 100 ≤ 47/10`.  Both are routine Mathlib `norm_num`/`Real.exp`
    facts; see the tractability note above (assessed GO). -/
example : (1 / 1000000 : ℝ) ≤ dlvpRateC / Real.log 100 := by
  sorry -- MISSING: `dlvpRateC ≥ 41625/5719420672` + `Real.log 100 ≤ 47/10`
        -- (two Real.exp rational enclosures + monotone substitution; all v4.32.0)

end DvpBoxProbe
