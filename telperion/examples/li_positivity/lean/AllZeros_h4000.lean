/-  TILED MILESTONE (T = 4000): all nontrivial zeta zeros up to height 4000 on Re = 1/2 —
    3,474 zeros — the FIRST EXERCISE OF THE HEIGHT CHAIN.

    Structure: `AllZeros_h2000` (39 bands, 1,517 zeros) + a `[2000, 4000]` SEGMENT certificate
    (fifty 40-height bands, n = 38..46; census 1,957 = N(4000) − N(2000)) composed by
    `AllZerosUpToHeight.height_chain`.  No single glue theorem exceeds the measured
    `interval_cases`/binder budgets — the pattern that iterates to ANY height.
    Eight close-pair re-sweeps (guard 25/25 lifetime); two bands exposed and fixed an emitter
    `nsimplify` landmine (the integer "3880" has a spurious radical closed form).
    conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h2000
import RHInBox_1d2000000_1999999d2000000_2000_2040
import RHInBox_1d2000000_1999999d2000000_2040_2080
import RHInBox_1d2000000_1999999d2000000_2080_2120
import RHInBox_1d2000000_1999999d2000000_2120_2160
import RHInBox_1d2000000_1999999d2000000_2160_2200
import RHInBox_1d2000000_1999999d2000000_2200_2240
import RHInBox_1d2000000_1999999d2000000_2240_2280
import RHInBox_1d2000000_1999999d2000000_2280_2320
import RHInBox_1d2000000_1999999d2000000_2320_2360
import RHInBox_1d2000000_1999999d2000000_2360_2400
import RHInBox_1d2000000_1999999d2000000_2400_2440
import RHInBox_1d2000000_1999999d2000000_2440_2480
import RHInBox_1d2000000_1999999d2000000_2480_2520
import RHInBox_1d2000000_1999999d2000000_2520_2560
import RHInBox_1d2000000_1999999d2000000_2560_2600
import RHInBox_1d2000000_1999999d2000000_2600_2640
import RHInBox_1d2000000_1999999d2000000_2640_2680
import RHInBox_1d2000000_1999999d2000000_2680_2720
import RHInBox_1d2000000_1999999d2000000_2720_2760
import RHInBox_1d2000000_1999999d2000000_2760_2800
import RHInBox_1d2000000_1999999d2000000_2800_2840
import RHInBox_1d2000000_1999999d2000000_2840_2880
import RHInBox_1d2000000_1999999d2000000_2880_2920
import RHInBox_1d2000000_1999999d2000000_2920_2960
import RHInBox_1d2000000_1999999d2000000_2960_3000
import RHInBox_1d2000000_1999999d2000000_3000_3040
import RHInBox_1d2000000_1999999d2000000_3040_3080
import RHInBox_1d2000000_1999999d2000000_3080_3120
import RHInBox_1d2000000_1999999d2000000_3120_3160
import RHInBox_1d2000000_1999999d2000000_3160_3200
import RHInBox_1d2000000_1999999d2000000_3200_3240
import RHInBox_1d2000000_1999999d2000000_3240_3280
import RHInBox_1d2000000_1999999d2000000_3280_3320
import RHInBox_1d2000000_1999999d2000000_3320_3360
import RHInBox_1d2000000_1999999d2000000_3360_3400
import RHInBox_1d2000000_1999999d2000000_3400_3440
import RHInBox_1d2000000_1999999d2000000_3440_3480
import RHInBox_1d2000000_1999999d2000000_3480_3520
import RHInBox_1d2000000_1999999d2000000_3520_3560
import RHInBox_1d2000000_1999999d2000000_3560_3600
import RHInBox_1d2000000_1999999d2000000_3600_3640
import RHInBox_1d2000000_1999999d2000000_3640_3680
import RHInBox_1d2000000_1999999d2000000_3680_3720
import RHInBox_1d2000000_1999999d2000000_3720_3760
import RHInBox_1d2000000_1999999d2000000_3760_3800
import RHInBox_1d2000000_1999999d2000000_3800_3840
import RHInBox_1d2000000_1999999d2000000_3840_3880
import RHInBox_1d2000000_1999999d2000000_3880_3920
import RHInBox_1d2000000_1999999d2000000_3920_3960
import RHInBox_1d2000000_1999999d2000000_3960_4000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h4000

/-- The 50-band partition of `[2000, 4000]` (height 40 each). -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 2000
  | 1 => 2040
  | 2 => 2080
  | 3 => 2120
  | 4 => 2160
  | 5 => 2200
  | 6 => 2240
  | 7 => 2280
  | 8 => 2320
  | 9 => 2360
  | 10 => 2400
  | 11 => 2440
  | 12 => 2480
  | 13 => 2520
  | 14 => 2560
  | 15 => 2600
  | 16 => 2640
  | 17 => 2680
  | 18 => 2720
  | 19 => 2760
  | 20 => 2800
  | 21 => 2840
  | 22 => 2880
  | 23 => 2920
  | 24 => 2960
  | 25 => 3000
  | 26 => 3040
  | 27 => 3080
  | 28 => 3120
  | 29 => 3160
  | 30 => 3200
  | 31 => 3240
  | 32 => 3280
  | 33 => 3320
  | 34 => 3360
  | 35 => 3400
  | 36 => 3440
  | 37 => 3480
  | 38 => 3520
  | 39 => 3560
  | 40 => 3600
  | 41 => 3640
  | 42 => 3680
  | 43 => 3720
  | 44 => 3760
  | 45 => 3800
  | 46 => 3840
  | 47 => 3880
  | 48 => 3920
  | 49 => 3960
  | 50 => 4000
  | _ => 4000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((2000:ℝ)) ≤ (2040); norm_num
  · show ((2040:ℝ)) ≤ (2080); norm_num
  · show ((2080:ℝ)) ≤ (2120); norm_num
  · show ((2120:ℝ)) ≤ (2160); norm_num
  · show ((2160:ℝ)) ≤ (2200); norm_num
  · show ((2200:ℝ)) ≤ (2240); norm_num
  · show ((2240:ℝ)) ≤ (2280); norm_num
  · show ((2280:ℝ)) ≤ (2320); norm_num
  · show ((2320:ℝ)) ≤ (2360); norm_num
  · show ((2360:ℝ)) ≤ (2400); norm_num
  · show ((2400:ℝ)) ≤ (2440); norm_num
  · show ((2440:ℝ)) ≤ (2480); norm_num
  · show ((2480:ℝ)) ≤ (2520); norm_num
  · show ((2520:ℝ)) ≤ (2560); norm_num
  · show ((2560:ℝ)) ≤ (2600); norm_num
  · show ((2600:ℝ)) ≤ (2640); norm_num
  · show ((2640:ℝ)) ≤ (2680); norm_num
  · show ((2680:ℝ)) ≤ (2720); norm_num
  · show ((2720:ℝ)) ≤ (2760); norm_num
  · show ((2760:ℝ)) ≤ (2800); norm_num
  · show ((2800:ℝ)) ≤ (2840); norm_num
  · show ((2840:ℝ)) ≤ (2880); norm_num
  · show ((2880:ℝ)) ≤ (2920); norm_num
  · show ((2920:ℝ)) ≤ (2960); norm_num
  · show ((2960:ℝ)) ≤ (3000); norm_num
  · show ((3000:ℝ)) ≤ (3040); norm_num
  · show ((3040:ℝ)) ≤ (3080); norm_num
  · show ((3080:ℝ)) ≤ (3120); norm_num
  · show ((3120:ℝ)) ≤ (3160); norm_num
  · show ((3160:ℝ)) ≤ (3200); norm_num
  · show ((3200:ℝ)) ≤ (3240); norm_num
  · show ((3240:ℝ)) ≤ (3280); norm_num
  · show ((3280:ℝ)) ≤ (3320); norm_num
  · show ((3320:ℝ)) ≤ (3360); norm_num
  · show ((3360:ℝ)) ≤ (3400); norm_num
  · show ((3400:ℝ)) ≤ (3440); norm_num
  · show ((3440:ℝ)) ≤ (3480); norm_num
  · show ((3480:ℝ)) ≤ (3520); norm_num
  · show ((3520:ℝ)) ≤ (3560); norm_num
  · show ((3560:ℝ)) ≤ (3600); norm_num
  · show ((3600:ℝ)) ≤ (3640); norm_num
  · show ((3640:ℝ)) ≤ (3680); norm_num
  · show ((3680:ℝ)) ≤ (3720); norm_num
  · show ((3720:ℝ)) ≤ (3760); norm_num
  · show ((3760:ℝ)) ≤ (3800); norm_num
  · show ((3800:ℝ)) ≤ (3840); norm_num
  · show ((3840:ℝ)) ≤ (3880); norm_num
  · show ((3880:ℝ)) ≤ (3920); norm_num
  · show ((3920:ℝ)) ≤ (3960); norm_num
  · show ((3960:ℝ)) ≤ (4000); norm_num
  · show ((4000:ℝ)) ≤ (4000); norm_num
  · exact le_refl _

/-- `1/(2·10⁶) ≤ dlvpRateC / log 4000` (`log 4000 ≤ 9`, `2.7⁹ ≈ 7626`). -/
theorem haC_4000 : (1 / 2000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 4000 := by
  have hlog : Real.log 4000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h9 : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 := pow_le_pow_left₀ (by norm_num) he1 9
    rw [h9]; nlinarith [hpow]
  have hpos : 0 < Real.log 4000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 2000000 : ℝ) * Real.log 4000
      ≤ (1 / 2000000) * 9 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[2000, 4000]` SEGMENT: every zero with `2000 ≤ Im ≤ 4000` is on the line, from the
    fifty band conclusions (the first use of `all_nontrivial_zeros_in_segment_on_line`). -/
theorem segment_2000_4000
    (hseg0 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg25 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg26 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg27 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg28 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg29 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg30 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg31 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg32 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg33 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg34 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg35 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg36 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg37 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg38 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg39 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg40 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg41 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg42 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg43 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg44 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg45 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg46 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg47 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg48 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg49 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (2000:ℝ) ≤ ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 2000000 = 1999999 / 2000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 2000000) 2000 4000 bndSeg 50 (by norm_num) bndSeg_mono rfl rfl haC_4000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : ((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 1999999 / 2000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  interval_cases i
  · exact hseg0 ρ hre' him hz
  · exact hseg1 ρ hre' him hz
  · exact hseg2 ρ hre' him hz
  · exact hseg3 ρ hre' him hz
  · exact hseg4 ρ hre' him hz
  · exact hseg5 ρ hre' him hz
  · exact hseg6 ρ hre' him hz
  · exact hseg7 ρ hre' him hz
  · exact hseg8 ρ hre' him hz
  · exact hseg9 ρ hre' him hz
  · exact hseg10 ρ hre' him hz
  · exact hseg11 ρ hre' him hz
  · exact hseg12 ρ hre' him hz
  · exact hseg13 ρ hre' him hz
  · exact hseg14 ρ hre' him hz
  · exact hseg15 ρ hre' him hz
  · exact hseg16 ρ hre' him hz
  · exact hseg17 ρ hre' him hz
  · exact hseg18 ρ hre' him hz
  · exact hseg19 ρ hre' him hz
  · exact hseg20 ρ hre' him hz
  · exact hseg21 ρ hre' him hz
  · exact hseg22 ρ hre' him hz
  · exact hseg23 ρ hre' him hz
  · exact hseg24 ρ hre' him hz
  · exact hseg25 ρ hre' him hz
  · exact hseg26 ρ hre' him hz
  · exact hseg27 ρ hre' him hz
  · exact hseg28 ρ hre' him hz
  · exact hseg29 ρ hre' him hz
  · exact hseg30 ρ hre' him hz
  · exact hseg31 ρ hre' him hz
  · exact hseg32 ρ hre' him hz
  · exact hseg33 ρ hre' him hz
  · exact hseg34 ρ hre' him hz
  · exact hseg35 ρ hre' him hz
  · exact hseg36 ρ hre' him hz
  · exact hseg37 ρ hre' him hz
  · exact hseg38 ρ hre' him hz
  · exact hseg39 ρ hre' him hz
  · exact hseg40 ρ hre' him hz
  · exact hseg41 ρ hre' him hz
  · exact hseg42 ρ hre' him hz
  · exact hseg43 ρ hre' him hz
  · exact hseg44 ρ hre' him hz
  · exact hseg45 ρ hre' him hz
  · exact hseg46 ρ hre' him hz
  · exact hseg47 ρ hre' him hz
  · exact hseg48 ρ hre' him hz
  · exact hseg49 ρ hre' him hz

/-- **T = 4000 via the HEIGHT CHAIN**: `[0,2000]` (AllZeros_h2000) ∘ `[2000,4000]` (segment).
    3,474 zeros.  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_4000_of_bands
    (hband0 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband1 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((100) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (150)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband2 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((150) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband3 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (250)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband4 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((250) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (300)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband5 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((300) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (350)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband6 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((350) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband7 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (450)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband8 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((450) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (500)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband9 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((500) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (550)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband10 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((550) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband11 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (650)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband12 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((650) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (700)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband13 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (750)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband14 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((750) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband15 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (850)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband16 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((850) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (900)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband17 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((900) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (950)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband18 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((950) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband19 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1050)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband20 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1050) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1100)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband21 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1100) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1150)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband22 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1150) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband23 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1250)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband24 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1250) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1300)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband25 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1300) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1350)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband26 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1350) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband27 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1450)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband28 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1450) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1500)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband29 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1500) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1550)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband30 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1550) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband31 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1650)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband32 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1650) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1700)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband33 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1750)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband34 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1750) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband35 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1850)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband36 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1850) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1900)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband37 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1900) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1950)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband38 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1950) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg0 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg25 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg26 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg27 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg28 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg29 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg30 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg31 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg32 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg33 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg34 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg35 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg36 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg37 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg38 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg39 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg40 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg41 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg42 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg43 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg44 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg45 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg46 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg47 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg48 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg49 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2 := by
  have hγ2000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 2000 4000
    (AllZeros_h2000.all_nontrivial_zeros_up_to_height_2000_of_bands
    hband0
    hband1
    hband2
    hband3
    hband4
    hband5
    hband6
    hband7
    hband8
    hband9
    hband10
    hband11
    hband12
    hband13
    hband14
    hband15
    hband16
    hband17
    hband18
    hband19
    hband20
    hband21
    hband22
    hband23
    hband24
    hband25
    hband26
    hband27
    hband28
    hband29
    hband30
    hband31
    hband32
    hband33
    hband34
    hband35
    hband36
    hband37
    hband38
      hγ2000)
    (segment_2000_4000
      hseg0
      hseg1
      hseg2
      hseg3
      hseg4
      hseg5
      hseg6
      hseg7
      hseg8
      hseg9
      hseg10
      hseg11
      hseg12
      hseg13
      hseg14
      hseg15
      hseg16
      hseg17
      hseg18
      hseg19
      hseg20
      hseg21
      hseg22
      hseg23
      hseg24
      hseg25
      hseg26
      hseg27
      hseg28
      hseg29
      hseg30
      hseg31
      hseg32
      hseg33
      hseg34
      hseg35
      hseg36
      hseg37
      hseg38
      hseg39
      hseg40
      hseg41
      hseg42
      hseg43
      hseg44
      hseg45
      hseg46
      hseg47
      hseg48
      hseg49
      hγ)

end AllZeros_h4000
