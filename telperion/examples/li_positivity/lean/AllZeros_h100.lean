/-  CONCRETE T=100 CERTIFICATE (kernel): ALL nontrivial zeta zeros up to height 100 lie on Re = 1/2.

    This is the headline instantiation of the combination theorem
    `AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line` at `a = 1/10^6`, `T = 100`.
    It composes the two atoms at the CONCRETE band/box:

    * `ZetaZeroConfinement.zero_in_band` (dVP + FE): every nontrivial zero up to height 100 lies
      in the band `[1/10^6, 1 - 1/10^6]`.  Instantiated at `a = 1/10^6`, `T = 100` with the
      effective-rate inequality `1/10^6 ≤ dlvpRateC / log 100` DISCHARGED here (see `haC` below).
    * `RHInBox_1d1000000_999999d1000000_0_100.rh_in_box_1d1000000_999999d1000000_0_100`
      (argument principle + winding count, PR #312 driver): every zeta zero IN the box
      `[1/10^6, 1 - 1/10^6] x [0, 100]` lies on Re = 1/2.  Emitted by
      `generate.py --box 1/1000000,999999/1000000,0,100` (winding `N = 29`, 29 on-line zeros).

    Confinement puts every nontrivial zero up to 100 inside the box; box-localization forces it
    onto Re = 1/2.  The conclusion is the genuine, unweighted
    `∀ ρ, ζ ρ = 0 → 0 < ρ.im → ρ.im ≤ 100 → ρ.re = 1/2` -- it is DERIVED, not assumed.

    EFFECTIVE RATE (no more non-effective-c caveat): `dlvpRateC` is a CONCRETE closed-form real
    (PR #316/#318), so `haC : 1/10^6 ≤ dlvpRateC / log 100` is discharged by explicit rational
    enclosures of `log(23/22)`, `log(15/(2-π²/6))`, and `log 100` (via `Real.exp` bounds).

    TRUST BOUNDARY (honest):
    * KERNEL: the dVP zero-free region + the functional equation (confinement side), the argument
      principle + winding-integral algebra (box side), and the `haC` rate inequality are all
      kernel-checked Lean.
    * ARB NON-KERNEL INPUT: the winding count `N = 29`, the 29 on-line zeros (`hLine`), the edge
      non-vanishing + integrability bundle (`hArb`), and the height floor `55/16 ≤ |Im|` (`hγ`)
      are supplied as documented external inputs.  They are outward-rounded python-flint/Arb ball
      certificates; Lean does not independently verify the ζ-values.  `hLine`/`hArb` are exactly
      the inputs the PR #312 box driver emits; `hγ` (route c: no nontrivial zeros below height
      55/16 ≈ 3.44) is a classical Arb-certifiable fact -- the on-line sweep for this box places
      all 29 zeros at height ≥ 14 > 55/16.  Carried as a documented non-kernel hypothesis,
      consistent with the winding/enclosure trust boundary.

    conjecture1_proved = False.  This is a kernel-verified COMPLETE FINITE Turing verification of
    RH up to height 100 (given the documented Arb inputs), NOT a proof of the Riemann Hypothesis.
-/
import Mathlib
import DlvpZetaZeroFree
import ZetaZeroConfinement
import RHInBox_1d1000000_999999d1000000_0_100

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h100

/-- **The effective-rate box-edge inequality at the concrete instance.**
    `a = 1/10^6` satisfies `a ≤ dlvpRateC / log 100`.

    `dlvpRateC = 1/(112·16·K)` with `K = 1 + 2·((8/(3·log(23/22)) + 608/9)/16)·(log(15/(2-π²/6)) + 1)`.
    We bound `K` from above using loose rational enclosures of the two internal logs and
    `log 100 ≤ 47/10`, all via `Real.exp` numeric bounds (`exp_one_gt_d9`, `pi_lt_d4`,
    `exp_bound'`, `add_one_le_exp`).  Margins are comfortable (actual `dlvpRateC/log 100 ≈ 1.58·10⁻⁶`,
    and the proven lower bound is `≈ 1.40·10⁻⁶ ≥ 10⁻⁶`).  conjecture1_proved = False. -/
theorem haC_100 : (1 / 1000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 100 := by
  -- π bounds → 2 - π²/6 > 0.
  have hpilt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpigt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpisq_lt : Real.pi ^ 2 < 9.87 := by nlinarith [hpilt, hpigt, hpi_pos]
  have hden_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by nlinarith [hpisq_lt]
  -- log(23/22) ≥ 1/25 : exp(1/25) ≤ 23/22 via the degree-3 exponential upper bound.
  have hlog2322 : (1 / 25 : ℝ) ≤ Real.log ((23 / 16) / (11 / 8)) := by
    have h2322 : ((23 / 16) / (11 / 8) : ℝ) = 23 / 22 := by norm_num
    rw [h2322, Real.le_log_iff_exp_le (by norm_num)]
    have hb := Real.exp_bound' (x := (1/25 : ℝ)) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 3, (1/25 : ℝ) ^ m / m.factorial)
        + (1/25 : ℝ) ^ 3 * (3 + 1) / ((Nat.factorial 3) * 3) ≤ 23 / 22 := by
      simp [Finset.sum_range_succ, Nat.factorial]; norm_num
    linarith [hb, hsum]
  -- log(15/(2-π²/6)) ≤ 4 : 15/(2-π²/6) ≤ 43 ≤ exp 4 = (exp 1)^4.
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
  -- log 100 ≤ 47/10 : 100 ≤ exp(47/10) = (exp 1)^4 · (exp(7/30))^3.
  have hlog100 : Real.log 100 ≤ 47 / 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h47 : Real.exp (47 / 10) = (Real.exp 1) ^ 4 * (Real.exp (7 / 30)) ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hpow4 : (54 : ℝ) ≤ (Real.exp 1) ^ 4 := by
      have hpow : (2.718 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
      nlinarith [hpow]
    have hexp730 : (37 / 30 : ℝ) ≤ Real.exp (7 / 30) := by
      have := Real.add_one_le_exp (7 / 30 : ℝ); linarith
    have hpow3 : (37 / 30 : ℝ) ^ 3 ≤ (Real.exp (7 / 30)) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hexp730 3
    rw [h47]
    nlinarith [hpow4, hpow3, pow_pos (Real.exp_pos (1:ℝ)) 4, pow_pos (Real.exp_pos (7/30:ℝ)) 3]
  -- Assemble the closed form: dlvpRateC = 1/(112·16·K), K = 1 + 2·M·(L15+1), M = (8/(3·L1)+608/9)/16.
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
  have hlog100pos : 0 < Real.log 100 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog100pos]
  calc (1 / 1000000 : ℝ) * Real.log 100
      ≤ (1 / 1000000 : ℝ) * (47 / 10) := by nlinarith [hlog100, hlog100pos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := hClo

/-- **ALL nontrivial zeta zeros up to height 100 lie on Re = 1/2** (concrete T=100 certificate).

    Instantiates the combination at `a = 1/10^6`, `T = 100`.  Every nontrivial zero `ρ`
    (`ζ ρ = 0`, `0 < ρ.im ≤ 100`) has `ρ.re = 1/2`.

    Composes `ZetaZeroConfinement.zero_in_band` (band `[1/10^6, 1 - 1/10^6]`, effective-rate edge
    `haC_100`) with the emitted wide-box atom
    `RHInBox_1d1000000_999999d1000000_0_100.rh_in_box_1d1000000_999999d1000000_0_100`
    (box-localization, winding `N = 29`).

    **Documented Arb non-kernel inputs** (identical shape to the PR #312 box driver):
    - `hLine` — the 29 on-line zeros (existential, increasing imaginary parts, on Re = 1/2).
    - `hArb` — the boundary non-vanishing + integrability bundle and the winding value `= 2πi·29`.
    - `hγ` — the height floor `55/16 ≤ |Im|` for nontrivial zeros up to 100 (route c: no nontrivial
      zeros below height 55/16; the on-line sweep places all zeros at height ≥ 14).

    **Conclusion:** `∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100 → ρ.re = 1/2`.

    conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_100
    (hLine : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : ℝ,
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
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
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
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100 → ρ.re = 1 / 2 := by
  -- The box atom: every zeta zero in [1/10^6, 1-1/10^6] x [0,100] is on Re = 1/2.
  have hbox := RHInBox_1d1000000_999999d1000000_0_100.rh_in_box_1d1000000_999999d1000000_0_100
    hLine hArb
  intro ρ hzero him0 himT
  -- Confinement: ρ is in the band [1/10^6, 1 - 1/10^6].
  obtain ⟨hlo, hhi⟩ := ZetaZeroConfinement.zero_in_band (1 / 1000000) 100 haC_100
    (by norm_num) (by norm_num) hzero him0 himT (hγ ρ hzero him0 himT)
  -- Reconcile the band's `1 - a` with the box's `999999/1000000`, then apply box-localization.
  have hhi' : ρ.re ≤ 999999 / 1000000 := by
    have : (1 : ℝ) - 1 / 1000000 = 999999 / 1000000 := by norm_num
    linarith [hhi, this.le, this.ge]
  exact hbox ρ ⟨hlo, hhi'⟩ ⟨le_of_lt him0, himT⟩ hzero

end AllZeros_h100
