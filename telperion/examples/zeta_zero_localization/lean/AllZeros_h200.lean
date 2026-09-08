/-  CONCRETE T=200 CERTIFICATE (kernel): ALL nontrivial zeta zeros up to height 200 lie on Re = 1/2.

    The first BAND-STACKED height certificate: two per-band box atoms glued by
    `RHInBoxBands.rh_box_two_bands` (height-tiling, PR #324), composed with dVP+FE confinement
    (`ZetaZeroConfinement.zero_in_band`) at `a = 1/10^6`, `T = 200`:

    * `RHInBox_1d1000000_999999d1000000_0_100`   -- band `[0, 100]`,  winding `N = 29` (29 on-line zeros)
    * `RHInBox_1d1000000_999999d1000000_100_200` -- band `[100, 200]`, winding `N = 50` (50 on-line zeros)
      (N(200) - N(100) = 79 - 29 = 50.)  Emitted by
      `generate.py --box 1/1000000,999999/1000000,100,200` with the O(N) list-based construction.

    Each band carries its own small winding and short vertical edges (the height-tiling compute
    lever); the O(N) emitter keeps per-band proof cost linear.  The glue is conclusion-level:
    a zero's `Im` is either `<= 100` or `>= 100`.

    EFFECTIVE RATE at T=200: `haC_200 : 1/10^6 <= dlvpRateC / log 200` discharged in-kernel via
    `log 200 <= 27/5` (`200 <= exp(27/5) = (exp 1)^5 * exp(2/5)`, `(exp 1)^5 >= 148`,
    `exp(2/5) >= 7/5`, `148 * 7/5 = 207.2 >= 200`) and the same `dlvpRateC >= 9/1369088`
    enclosure as `AllZeros_h100.haC_100`.  Margin: `5.4e-6 <= 6.57e-6`.

    TRUST BOUNDARY (honest, identical in KIND to AllZeros_h100 -- band-stacking adds no new
    kind of input):
    * KERNEL: dVP region + FE (confinement), argument principle + winding algebra (both boxes),
      band-gluing, and the `haC_200` rate inequality.
    * ARB NON-KERNEL INPUT: winding counts `N = 29` / `N = 50`, the 29 + 50 on-line zeros
      (`hLine1`/`hLine2`), the two boundary bundles (`hArb1`/`hArb2`), and the height floor
      `55/16 <= |Im|` (`hgamma`).

    conjecture1_proved = False.  A kernel-verified COMPLETE FINITE verification of RH up to
    height 200 (given the documented Arb inputs), NOT a proof of the Riemann Hypothesis.
-/
import Mathlib
import DlvpZetaZeroFree
import ZetaZeroConfinement
import RHInBoxBands
import RHInBox_1d1000000_999999d1000000_0_100
import RHInBox_1d1000000_999999d1000000_100_200

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h200

/-- **Effective-rate box-edge inequality at `T = 200`.**  `a = 1/10^6 <= dlvpRateC / log 200`.
    Same skeleton as `AllZeros_h100.haC_100`; only the `log` bound changes:
    `log 200 <= 27/5` via `200 <= (exp 1)^5 * exp(2/5)`.  conjecture1_proved = False. -/
theorem haC_200 : (1 / 1000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 200 := by
  have hpilt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpigt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpisq_lt : Real.pi ^ 2 < 9.87 := by nlinarith [hpilt, hpigt, hpi_pos]
  have hden_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by nlinarith [hpisq_lt]
  have hlog2322 : (1 / 25 : ℝ) ≤ Real.log ((23 / 16) / (11 / 8)) := by
    have h2322 : ((23 / 16) / (11 / 8) : ℝ) = 23 / 22 := by norm_num
    rw [h2322, Real.le_log_iff_exp_le (by norm_num)]
    have hb := Real.exp_bound' (x := (1/25 : ℝ)) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 3, (1/25 : ℝ) ^ m / m.factorial)
        + (1/25 : ℝ) ^ 3 * (3 + 1) / ((Nat.factorial 3) * 3) ≤ 23 / 22 := by
      simp [Finset.sum_range_succ, Nat.factorial]; norm_num
    linarith [hb, hsum]
  have hlog15 : Real.log (15 / (2 - Real.pi ^ 2 / 6)) ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h43 : (15 : ℝ) / (2 - Real.pi ^ 2 / 6) ≤ 43 := by
      rw [div_le_iff₀ hden_pos]; nlinarith [hpisq_lt]
    have hexp4 : (43 : ℝ) ≤ Real.exp 4 := by
      have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have hpow : (2.7 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
      rw [h4]; nlinarith [hpow]
    linarith [h43, hexp4]
  -- log 200 <= 27/5 : 200 <= exp(27/5) = (exp 1)^5 * exp(2/5).
  have hlog200 : Real.log 200 ≤ 27 / 5 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h275 : Real.exp (27 / 5) = (Real.exp 1) ^ 5 * Real.exp (2 / 5) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hpow5 : (148 : ℝ) ≤ (Real.exp 1) ^ 5 := by
      have hpow : (2.718 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) he1 5
      nlinarith [hpow]
    have hexp25 : (7 / 5 : ℝ) ≤ Real.exp (2 / 5) := by
      have := Real.add_one_le_exp (2 / 5 : ℝ); linarith
    rw [h275]
    nlinarith [hpow5, hexp25, pow_pos (Real.exp_pos (1:ℝ)) 5, Real.exp_pos (2/5:ℝ)]
  have hLrpos : 0 < Real.log ((23 / 16) / (11 / 8)) := by linarith [hlog2322]
  have hlog15nn : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hden_pos]; nlinarith [hden_pos])
  set L1 : ℝ := Real.log ((23 / 16) / (11 / 8)) with hL1
  set L15 : ℝ := Real.log (15 / (2 - Real.pi ^ 2 / 6)) with hL15
  set M : ℝ := (8 / (3 * L1) + 608 / 9) / 16 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hterm : 8 / (3 * L1) ≤ 200 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hlog2322, hLrpos]
  have hMup : M ≤ 151 / 18 := by
    have h1 : M ≤ (200 / 3 + 608 / 9) / 16 := by rw [hMdef]; gcongr
    nlinarith [h1]
  set K : ℝ := 1 + 2 * M * (L15 + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKub : K ≤ 764 / 9 := by
    rw [hKdef]
    have hfac : L15 + 1 ≤ 4 + 1 := by linarith [hlog15]
    have hfac_pos : 0 < L15 + 1 := by linarith [hlog15nn]
    nlinarith [hMpos, hMup, hfac, hfac_pos, hlog15nn]
  have hCdef : ZeroFreeBridge.dlvpRateC = 1 / (112 * 16 * K) := by
    rw [ZeroFreeBridge.dlvpRateC, ZeroFreeBridge.dlvpRateK, ← hL1, ← hL15, ← hMdef, ← hKdef]
  have hClo : (9 / 1369088 : ℝ) ≤ ZeroFreeBridge.dlvpRateC := by
    rw [hCdef]
    have hval : (9 / 1369088 : ℝ) = 1 / (112 * 16 * (764 / 9)) := by norm_num
    rw [hval]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [hKub, hKpos]
  have hlog200pos : 0 < Real.log 200 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog200pos]
  calc (1 / 1000000 : ℝ) * Real.log 200
      ≤ (1 / 1000000 : ℝ) * (27 / 5) := by nlinarith [hlog200, hlog200pos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := hClo

/-- **ALL nontrivial zeta zeros up to height 200 lie on Re = 1/2** (band-stacked T=200 certificate).

    Applies the two emitted per-band box atoms at their documented Arb inputs, glues them with
    `RHInBoxBands.rh_box_two_bands`, and composes with `ZetaZeroConfinement.zero_in_band` at
    `a = 1/10^6`, `T = 200` (effective-rate edge `haC_200`).

    **Documented Arb non-kernel inputs:** `hLine1`/`hArb1` (band `[0,100]`, `N = 29`),
    `hLine2`/`hArb2` (band `[100,200]`, `N = 50`), and `hgamma` (height floor `55/16 <= |Im|`).
    Hypothesis types are verbatim the two emitted theorems' signatures.

    **Conclusion:** `∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 200 → ρ.re = 1/2`.

    conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_200
    (hLine1 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : ℝ,
      (0 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 ≤ 100) ∧
      (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x6 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x7 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x8 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x9 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x10 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x11 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x12 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x13 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x14 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x15 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x16 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x17 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x18 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x19 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x20 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x21 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x22 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x23 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x24 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x25 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x26 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x27 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x28 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x29 : ℂ) * Complex.I) = 0))
    (hArb1 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 1000000)) : ℝ) ((999999 / 1000000)) ×ℂ Set.Icc ((0) : ℝ) (100)) →
      (∀ z ∈ Metric.ball RHInBox_1d1000000_999999d1000000_0_100.cPB RHInBox_1d1000000_999999d1000000_0_100.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((0) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 1000000)) : ℝ) < ρ.re ∧ ρ.re < ((999999 / 1000000)) ∧ ((0) : ℝ) < ρ.im ∧ ρ.im < (100)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((0) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      ((∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
          + I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (29 : ℂ)))
    (hLine2 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 : ℝ,
      (100 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 ≤ 200) ∧
      (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x6 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x7 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x8 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x9 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x10 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x11 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x12 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x13 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x14 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x15 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x16 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x17 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x18 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x19 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x20 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x21 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x22 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x23 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x24 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x25 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x26 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x27 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x28 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x29 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x30 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x31 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x32 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x33 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x34 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x35 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x36 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x37 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x38 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x39 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x40 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x41 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x42 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x43 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x44 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x45 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x46 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x47 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x48 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x49 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0))
    (hArb2 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 1000000)) : ℝ) ((999999 / 1000000)) ×ℂ Set.Icc ((100) : ℝ) (200)) →
      (∀ z ∈ Metric.ball RHInBox_1d1000000_999999d1000000_100_200.cPB RHInBox_1d1000000_999999d1000000_100_200.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 1000000)) : ℝ) ((999999 / 1000000)), riemannZeta (↑x + (((200) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((100) : ℝ) (200), riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((100) : ℝ) (200), riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 1000000)) : ℝ) < ρ.re ∧ ρ.re < ((999999 / 1000000)) ∧ ((100) : ℝ) < ρ.im ∧ ρ.im < (200)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((200) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((200) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((200) : ℝ) : ℂ) * I)) volume (((1 / 1000000))) (((999999 / 1000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((100)) ((200))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I)) volume ((100)) ((200))) ∧
      ((∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 1000000)) : ℝ)..((999999 / 1000000)), logDeriv riemannZeta (↑x + (((200) : ℝ) : ℂ) * I))
          + I • (∫ y in ((100) : ℝ)..(200), logDeriv riemannZeta (((((999999 / 1000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((100) : ℝ)..(200), logDeriv riemannZeta (((((1 / 1000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (50 : ℂ)))
    (hgamma : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 200 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 200 → ρ.re = 1 / 2 := by
  -- Per-band box atoms (each consumes its own Arb inputs).
  have hbox_low := RHInBox_1d1000000_999999d1000000_0_100.rh_in_box_1d1000000_999999d1000000_0_100
    hLine1 hArb1
  have hbox_high := RHInBox_1d1000000_999999d1000000_100_200.rh_in_box_1d1000000_999999d1000000_100_200
    hLine2 hArb2
  -- Height-tiling glue at Tm = 100.
  have hbox := RHInBoxBands.rh_box_two_bands (1 / 1000000) (999999 / 1000000) 0 100 200
    hbox_low hbox_high
  intro ρ hzero him0 himT
  -- Confinement: ρ lies in the band [1/10^6, 1 - 1/10^6].
  obtain ⟨hlo, hhi⟩ := ZetaZeroConfinement.zero_in_band (1 / 1000000) 200 haC_200
    (by norm_num) (by norm_num) hzero him0 himT (hgamma ρ hzero him0 himT)
  have hhi' : ρ.re ≤ 999999 / 1000000 := by
    have : (1 : ℝ) - 1 / 1000000 = 999999 / 1000000 := by norm_num
    linarith [hhi, this.le, this.ge]
  exact hbox ρ ⟨hlo, hhi'⟩ ⟨le_of_lt him0, himT⟩ hzero

end AllZeros_h200
