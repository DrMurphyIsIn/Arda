/-  TILED MILESTONE (T = 1000): all nontrivial zeta zeros up to height 1000 lie on Re = 1/2,
    from TEN per-band box certificates via the tiled capstone
    `AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line_tiled`.

    Bands (all at width a = 1/2·10^6, emitted by generate.py --box 1/2000000,1999999/2000000,lo,hi;
    each in seconds, independently):
      [0,100] N=29, [100,200] N=50, [200,300] N=59, [300,400] N=64, [400,500] N=67,
      [500,600] N=72, [600,700] N=73, [700,800] N=77, [800,900] N=78, [900,1000] N=80.
    Sum = 649 = N(1000), the classical zero count to height 1000.  The [700,800] band required a
    6x-denser on-line sweep (a close zero pair defeats the mean-spacing grid; the driver honestly
    REFUSED at default density with n_line=75 != n_total=77 -- exactly the close-pair grid
    refinement predicted in TURING_METHOD_SCOPING §4).

    `haC_1000` proves `1/(2·10^6) ≤ dlvpRateC / log 1000` in-kernel (`log 1000 ≤ 7` via
    `exp 7 ≥ 2.7^7 = 1046`; margin comfortable: 7/2000000 = 3.5e-6 ≤ 9/1369088 ≈ 6.57e-6).

    Forms: `..._1000_of_bands` (ten band CONCLUSIONS) and `..._1000` (headline; RAW Arb inputs --
    ten hLine/hArb pairs), plus the height floor `hγ` (usual residual; StripClear-dischargeable).

    conjecture1_proved = False.  Kernel-verified CONDITIONAL theorems, NOT a proof of RH. -/
import Mathlib
import DlvpZetaZeroFree
import ZetaZeroConfinement
import AllZerosUpToHeight
import RHInBox_1d2000000_1999999d2000000_0_100
import RHInBox_1d2000000_1999999d2000000_100_200
import RHInBox_1d2000000_1999999d2000000_200_300
import RHInBox_1d2000000_1999999d2000000_300_400
import RHInBox_1d2000000_1999999d2000000_400_500
import RHInBox_1d2000000_1999999d2000000_500_600
import RHInBox_1d2000000_1999999d2000000_600_700
import RHInBox_1d2000000_1999999d2000000_700_800
import RHInBox_1d2000000_1999999d2000000_800_900
import RHInBox_1d2000000_1999999d2000000_900_1000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h1000

/-- The ten-band height partition `0, 100, ..., 1000, 1000, ...`. -/
noncomputable def bnd : ℕ → ℝ := fun i => match i with
  | 0 => 0
  | 1 => 100
  | 2 => 200
  | 3 => 300
  | 4 => 400
  | 5 => 500
  | 6 => 600
  | 7 => 700
  | 8 => 800
  | 9 => 900
  | 10 => 1000
  | _ => 1000

theorem bnd_mono : Monotone bnd := by
  refine monotone_nat_of_le_succ ?_
  intro n
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · show ((0:ℝ)) ≤ (100); norm_num
  · show ((100:ℝ)) ≤ (200); norm_num
  · show ((200:ℝ)) ≤ (300); norm_num
  · show ((300:ℝ)) ≤ (400); norm_num
  · show ((400:ℝ)) ≤ (500); norm_num
  · show ((500:ℝ)) ≤ (600); norm_num
  · show ((600:ℝ)) ≤ (700); norm_num
  · show ((700:ℝ)) ≤ (800); norm_num
  · show ((800:ℝ)) ≤ (900); norm_num
  · show ((900:ℝ)) ≤ (1000); norm_num
  · show ((1000:ℝ)) ≤ (1000); norm_num
  · exact le_refl _

/-- **The effective-rate band-width inequality at `T = 1000`:** `1/(2·10^6) ≤ dlvpRateC / log 1000`.
    Same numeric core as `AllZeros_h100.haC_100` with `log 1000 ≤ 7`.  conjecture1_proved = False. -/
theorem haC_1000 : (1 / 2000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 1000 := by
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
  -- log 1000 ≤ 7 : 1000 ≤ exp 7 = (exp 1)^7 ≥ 2.7^7 = 1046.03…
  have hlog1000 : Real.log 1000 ≤ 7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h7 : Real.exp 7 = (Real.exp 1) ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow7 : (2.7 : ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) he1 7
    rw [h7]; nlinarith [hpow7]
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
  have hlogpos : 0 < Real.log 1000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlogpos]
  calc (1 / 2000000 : ℝ) * Real.log 1000
      ≤ (1 / 2000000 : ℝ) * 7 := by nlinarith [hlog1000, hlogpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := hClo

/-- **T = 1000 from the ten band CONCLUSIONS** (the tiling glue).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_1000_of_bands
    (hband0 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband1 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((100) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband2 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (300)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband3 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((300) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband4 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (500)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband5 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((500) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband6 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (700)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband7 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband8 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (900)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband9 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((900) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 2000000 = 1999999 / 2000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line_tiled
    (1 / 2000000) 1000 bnd 10 (by norm_num) bnd_mono rfl rfl haC_1000 (by norm_num) (by norm_num)
    ?_ hγ
  intro i hi ρ hre him hz
  have hre' : ((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 1999999 / 2000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  interval_cases i
  · exact hband0 ρ hre' him hz
  · exact hband1 ρ hre' him hz
  · exact hband2 ρ hre' him hz
  · exact hband3 ρ hre' him hz
  · exact hband4 ρ hre' him hz
  · exact hband5 ρ hre' him hz
  · exact hband6 ρ hre' him hz
  · exact hband7 ρ hre' him hz
  · exact hband8 ρ hre' him hz
  · exact hband9 ρ hre' him hz

/-- **TILED MILESTONE: all nontrivial zeta zeros up to height 1000 lie on `Re = 1/2`** — from the
    ten bands' RAW Arb inputs (windings 29+50+59+64+67+72+73+77+78+80 = 649 = N(1000)) plus the
    height floor `hγ`.  Every hypothesis is a primitive Arb winding/edge input.
    conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_1000
    (hLine0 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : ℝ,
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
    (hArb0 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((0) : ℝ) (100)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_0_100.cPB RHInBox_1d2000000_1999999d2000000_0_100.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((0) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((0) : ℝ) (100), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((0) : ℝ) < ρ.im ∧ ρ.im < (100)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((0) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((0) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((0)) ((100))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((0) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
          + I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((0) : ℝ)..(100), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (29 : ℂ)))
    (hLine1 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 : ℝ,
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
    (hArb1 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((100) : ℝ) (200)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_100_200.cPB RHInBox_1d2000000_1999999d2000000_100_200.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((100) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((200) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((100) : ℝ) (200), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((100) : ℝ) (200), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((100) : ℝ) < ρ.im ∧ ρ.im < (200)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((200) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((100) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((200) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((100)) ((200))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((100) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((200) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((100)) ((200))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((100)) ((200))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((100) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((200) : ℝ) : ℂ) * I))
          + I • (∫ y in ((100) : ℝ)..(200), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((100) : ℝ)..(200), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (50 : ℂ)))
    (hLine2 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 : ℝ,
      (200 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 ≤ 300) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0))
    (hArb2 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((200) : ℝ) (300)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_200_300.cPB RHInBox_1d2000000_1999999d2000000_200_300.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((200) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((300) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((200) : ℝ) (300), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((200) : ℝ) (300), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((200) : ℝ) < ρ.im ∧ ρ.im < (300)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((200) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((300) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((200)) ((300))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((200)) ((300))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((200) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((300) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((200)) ((300))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((200)) ((300))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((200) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((300) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((200)) ((300))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((200)) ((300))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((200) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((300) : ℝ) : ℂ) * I))
          + I • (∫ y in ((200) : ℝ)..(300), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((200) : ℝ)..(300), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (59 : ℂ)))
    (hLine3 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 : ℝ,
      (300 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 ≤ 400) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0))
    (hArb3 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((300) : ℝ) (400)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_300_400.cPB RHInBox_1d2000000_1999999d2000000_300_400.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((300) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((400) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((300) : ℝ) (400), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((300) : ℝ) (400), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((300) : ℝ) < ρ.im ∧ ρ.im < (400)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((300) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((300)) ((400))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((300)) ((400))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((300) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((300)) ((400))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((300)) ((400))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((300) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((400) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((300)) ((400))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((300)) ((400))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((300) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((400) : ℝ) : ℂ) * I))
          + I • (∫ y in ((300) : ℝ)..(400), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((300) : ℝ)..(400), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (64 : ℂ)))
    (hLine4 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 : ℝ,
      (400 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 ≤ 500) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x65 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x66 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x67 : ℂ) * Complex.I) = 0))
    (hArb4 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((400) : ℝ) (500)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_400_500.cPB RHInBox_1d2000000_1999999d2000000_400_500.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((400) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((500) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((400) : ℝ) (500), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((400) : ℝ) (500), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((400) : ℝ) < ρ.im ∧ ρ.im < (500)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((500) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((500))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((500))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((400) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((500) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((500))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((400)) ((500))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((400) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((500) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((400)) ((500))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((400)) ((500))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((400) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((500) : ℝ) : ℂ) * I))
          + I • (∫ y in ((400) : ℝ)..(500), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((400) : ℝ)..(500), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (67 : ℂ)))
    (hLine5 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 : ℝ,
      (500 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 < x68 ∧ x68 < x69 ∧ x69 < x70 ∧ x70 < x71 ∧ x71 < x72 ∧ x72 ≤ 600) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x65 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x66 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x67 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x68 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x69 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x70 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x71 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x72 : ℂ) * Complex.I) = 0))
    (hArb5 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((500) : ℝ) (600)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_500_600.cPB RHInBox_1d2000000_1999999d2000000_500_600.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((500) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((600) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((500) : ℝ) (600), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((500) : ℝ) (600), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((500) : ℝ) < ρ.im ∧ ρ.im < (600)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((500) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((500)) ((600))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((500)) ((600))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((500) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((500)) ((600))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((500)) ((600))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((500) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((600) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((500)) ((600))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((500)) ((600))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((500) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((600) : ℝ) : ℂ) * I))
          + I • (∫ y in ((500) : ℝ)..(600), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((500) : ℝ)..(600), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (72 : ℂ)))
    (hLine6 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 : ℝ,
      (600 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 < x68 ∧ x68 < x69 ∧ x69 < x70 ∧ x70 < x71 ∧ x71 < x72 ∧ x72 < x73 ∧ x73 ≤ 700) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x65 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x66 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x67 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x68 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x69 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x70 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x71 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x72 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x73 : ℂ) * Complex.I) = 0))
    (hArb6 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((600) : ℝ) (700)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_600_700.cPB RHInBox_1d2000000_1999999d2000000_600_700.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((600) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((700) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((600) : ℝ) (700), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((600) : ℝ) (700), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((600) : ℝ) < ρ.im ∧ ρ.im < (700)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((600)) ((700))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((600)) ((700))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((600) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((600)) ((700))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((600)) ((700))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((600) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((700) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((600)) ((700))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((600)) ((700))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((600) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((700) : ℝ) : ℂ) * I))
          + I • (∫ y in ((600) : ℝ)..(700), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((600) : ℝ)..(700), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (73 : ℂ)))
    (hLine7 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 : ℝ,
      (700 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 < x68 ∧ x68 < x69 ∧ x69 < x70 ∧ x70 < x71 ∧ x71 < x72 ∧ x72 < x73 ∧ x73 < x74 ∧ x74 < x75 ∧ x75 < x76 ∧ x76 < x77 ∧ x77 ≤ 800) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x65 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x66 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x67 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x68 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x69 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x70 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x71 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x72 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x73 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x74 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x75 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x76 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x77 : ℂ) * Complex.I) = 0))
    (hArb7 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((700) : ℝ) (800)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_700_800.cPB RHInBox_1d2000000_1999999d2000000_700_800.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((700) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((800) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((700) : ℝ) (800), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((700) : ℝ) (800), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((700) : ℝ) < ρ.im ∧ ρ.im < (800)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((700) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((700)) ((800))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((700) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((800) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((700)) ((800))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((700)) ((800))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((700) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((800) : ℝ) : ℂ) * I))
          + I • (∫ y in ((700) : ℝ)..(800), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((700) : ℝ)..(800), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (77 : ℂ)))
    (hLine8 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 : ℝ,
      (800 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 < x68 ∧ x68 < x69 ∧ x69 < x70 ∧ x70 < x71 ∧ x71 < x72 ∧ x72 < x73 ∧ x73 < x74 ∧ x74 < x75 ∧ x75 < x76 ∧ x76 < x77 ∧ x77 < x78 ∧ x78 ≤ 900) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x65 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x66 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x67 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x68 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x69 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x70 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x71 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x72 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x73 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x74 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x75 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x76 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x77 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x78 : ℂ) * Complex.I) = 0))
    (hArb8 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((800) : ℝ) (900)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_800_900.cPB RHInBox_1d2000000_1999999d2000000_800_900.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((800) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((900) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((800) : ℝ) (900), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((800) : ℝ) (900), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((800) : ℝ) < ρ.im ∧ ρ.im < (900)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((900) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((800)) ((900))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((800)) ((900))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((800) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((900) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((800)) ((900))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((800)) ((900))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((800) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((900) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((800)) ((900))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((800)) ((900))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((800) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((900) : ℝ) : ℂ) * I))
          + I • (∫ y in ((800) : ℝ)..(900), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((800) : ℝ)..(900), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (78 : ℂ)))
    (hLine9 : ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 : ℝ,
      (900 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 ∧ x10 < x11 ∧ x11 < x12 ∧ x12 < x13 ∧ x13 < x14 ∧ x14 < x15 ∧ x15 < x16 ∧ x16 < x17 ∧ x17 < x18 ∧ x18 < x19 ∧ x19 < x20 ∧ x20 < x21 ∧ x21 < x22 ∧ x22 < x23 ∧ x23 < x24 ∧ x24 < x25 ∧ x25 < x26 ∧ x26 < x27 ∧ x27 < x28 ∧ x28 < x29 ∧ x29 < x30 ∧ x30 < x31 ∧ x31 < x32 ∧ x32 < x33 ∧ x33 < x34 ∧ x34 < x35 ∧ x35 < x36 ∧ x36 < x37 ∧ x37 < x38 ∧ x38 < x39 ∧ x39 < x40 ∧ x40 < x41 ∧ x41 < x42 ∧ x42 < x43 ∧ x43 < x44 ∧ x44 < x45 ∧ x45 < x46 ∧ x46 < x47 ∧ x47 < x48 ∧ x48 < x49 ∧ x49 < x50 ∧ x50 < x51 ∧ x51 < x52 ∧ x52 < x53 ∧ x53 < x54 ∧ x54 < x55 ∧ x55 < x56 ∧ x56 < x57 ∧ x57 < x58 ∧ x58 < x59 ∧ x59 < x60 ∧ x60 < x61 ∧ x61 < x62 ∧ x62 < x63 ∧ x63 < x64 ∧ x64 < x65 ∧ x65 < x66 ∧ x66 < x67 ∧ x67 < x68 ∧ x68 < x69 ∧ x69 < x70 ∧ x70 < x71 ∧ x71 < x72 ∧ x72 < x73 ∧ x73 < x74 ∧ x74 < x75 ∧ x75 < x76 ∧ x76 < x77 ∧ x77 < x78 ∧ x78 < x79 ∧ x79 < x80 ∧ x80 ≤ 1000) ∧
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
       completedRiemannZeta (1 / 2 + (x50 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x51 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x52 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x53 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x54 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x55 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x56 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x57 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x58 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x59 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x60 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x61 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x62 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x63 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x64 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x65 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x66 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x67 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x68 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x69 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x70 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x71 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x72 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x73 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x74 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x75 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x76 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x77 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x78 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x79 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x80 : ℂ) * Complex.I) = 0))
    (hArb9 : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E (Set.Icc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)) ×ℂ Set.Icc ((900) : ℝ) (1000)) →
      (∀ z ∈ Metric.ball RHInBox_1d2000000_1999999d2000000_900_1000.cPB RHInBox_1d2000000_1999999d2000000_900_1000.RPB, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((900) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (((1 / 2000000)) : ℝ) ((1999999 / 2000000)), riemannZeta (↑x + (((1000) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((900) : ℝ) (1000), riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((900) : ℝ) (1000), riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, (((1 / 2000000)) : ℝ) < ρ.re ∧ ρ.re < ((1999999 / 2000000)) ∧ ((900) : ℝ) < ρ.im ∧ ρ.im < (1000)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((900) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (((1000) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((900)) ((1000))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((900)) ((1000))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((900) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (((1000) : ℝ) : ℂ) * I) - ρ)⁻¹) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((900)) ((1000))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume ((900)) ((1000))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((900) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (((1000) : ℝ) : ℂ) * I)) volume (((1 / 2000000))) (((1999999 / 2000000)))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((900)) ((1000))) ∧
      (IntervalIntegrable (fun y : ℝ => E (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I)) volume ((900)) ((1000))) ∧
      ((∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((900) : ℝ) : ℂ) * I))
          - (∫ x in (((1 / 2000000)) : ℝ)..((1999999 / 2000000)), logDeriv riemannZeta (↑x + (((1000) : ℝ) : ℂ) * I))
          + I • (∫ y in ((900) : ℝ)..(1000), logDeriv riemannZeta (((((1999999 / 2000000)) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in ((900) : ℝ)..(1000), logDeriv riemannZeta (((((1 / 2000000)) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (80 : ℂ)))
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=
  all_nontrivial_zeros_up_to_height_1000_of_bands
    (RHInBox_1d2000000_1999999d2000000_0_100.rh_in_box_1d2000000_1999999d2000000_0_100 hLine0 hArb0)
    (RHInBox_1d2000000_1999999d2000000_100_200.rh_in_box_1d2000000_1999999d2000000_100_200 hLine1 hArb1)
    (RHInBox_1d2000000_1999999d2000000_200_300.rh_in_box_1d2000000_1999999d2000000_200_300 hLine2 hArb2)
    (RHInBox_1d2000000_1999999d2000000_300_400.rh_in_box_1d2000000_1999999d2000000_300_400 hLine3 hArb3)
    (RHInBox_1d2000000_1999999d2000000_400_500.rh_in_box_1d2000000_1999999d2000000_400_500 hLine4 hArb4)
    (RHInBox_1d2000000_1999999d2000000_500_600.rh_in_box_1d2000000_1999999d2000000_500_600 hLine5 hArb5)
    (RHInBox_1d2000000_1999999d2000000_600_700.rh_in_box_1d2000000_1999999d2000000_600_700 hLine6 hArb6)
    (RHInBox_1d2000000_1999999d2000000_700_800.rh_in_box_1d2000000_1999999d2000000_700_800 hLine7 hArb7)
    (RHInBox_1d2000000_1999999d2000000_800_900.rh_in_box_1d2000000_1999999d2000000_800_900 hLine8 hArb8)
    (RHInBox_1d2000000_1999999d2000000_900_1000.rh_in_box_1d2000000_1999999d2000000_900_1000 hLine9 hArb9)
    hγ

end AllZeros_h1000
