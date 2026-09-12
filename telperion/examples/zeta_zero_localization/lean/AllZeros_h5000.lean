/-  Height-chain step: all nontrivial zeta zeros up to height 5000 on Re = 1/2 --
    `AllZeros_h4000` + a `[4000, 5000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  Emitted by campaign.py.
    conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h4000
import RHInBoxT_1d4000000_3999999d4000000_4000_4040
import RHInBoxT_1d4000000_3999999d4000000_4040_4080
import RHInBoxT_1d4000000_3999999d4000000_4080_4120
import RHInBoxT_1d4000000_3999999d4000000_4120_4160
import RHInBoxT_1d4000000_3999999d4000000_16639d4_4200
import RHInBoxT_1d4000000_3999999d4000000_4200_4240
import RHInBoxT_1d4000000_3999999d4000000_4240_4280
import RHInBoxT_1d4000000_3999999d4000000_4280_4320
import RHInBoxT_1d4000000_3999999d4000000_4320_4360
import RHInBoxT_1d4000000_3999999d4000000_4360_4400
import RHInBoxT_1d4000000_3999999d4000000_4400_4440
import RHInBoxT_1d4000000_3999999d4000000_4440_4480
import RHInBoxT_1d4000000_3999999d4000000_4480_4520
import RHInBoxT_1d4000000_3999999d4000000_4520_4560
import RHInBoxT_1d4000000_3999999d4000000_4560_4600
import RHInBoxT_1d4000000_3999999d4000000_4600_4640
import RHInBoxT_1d4000000_3999999d4000000_4640_4680
import RHInBoxT_1d4000000_3999999d4000000_4680_4720
import RHInBoxT_1d4000000_3999999d4000000_4720_4760
import RHInBoxT_1d4000000_3999999d4000000_4760_4800
import RHInBoxT_1d4000000_3999999d4000000_4800_4840
import RHInBoxT_1d4000000_3999999d4000000_4840_19521d4
import RHInBoxT_1d4000000_3999999d4000000_4880_4920
import RHInBoxT_1d4000000_3999999d4000000_4920_4960
import RHInBoxT_1d4000000_3999999d4000000_4960_5000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h5000

/-- The 25-band partition of `[4000, 5000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 4000
  | 1 => 4040
  | 2 => 4080
  | 3 => 4120
  | 4 => 4160
  | 5 => 4200
  | 6 => 4240
  | 7 => 4280
  | 8 => 4320
  | 9 => 4360
  | 10 => 4400
  | 11 => 4440
  | 12 => 4480
  | 13 => 4520
  | 14 => 4560
  | 15 => 4600
  | 16 => 4640
  | 17 => 4680
  | 18 => 4720
  | 19 => 4760
  | 20 => 4800
  | 21 => 4840
  | 22 => 4880
  | 23 => 4920
  | 24 => 4960
  | 25 => 5000
  | _ => 5000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((4000:ℝ)) ≤ (4040); norm_num
  · show ((4040:ℝ)) ≤ (4080); norm_num
  · show ((4080:ℝ)) ≤ (4120); norm_num
  · show ((4120:ℝ)) ≤ (4160); norm_num
  · show ((4160:ℝ)) ≤ (4200); norm_num
  · show ((4200:ℝ)) ≤ (4240); norm_num
  · show ((4240:ℝ)) ≤ (4280); norm_num
  · show ((4280:ℝ)) ≤ (4320); norm_num
  · show ((4320:ℝ)) ≤ (4360); norm_num
  · show ((4360:ℝ)) ≤ (4400); norm_num
  · show ((4400:ℝ)) ≤ (4440); norm_num
  · show ((4440:ℝ)) ≤ (4480); norm_num
  · show ((4480:ℝ)) ≤ (4520); norm_num
  · show ((4520:ℝ)) ≤ (4560); norm_num
  · show ((4560:ℝ)) ≤ (4600); norm_num
  · show ((4600:ℝ)) ≤ (4640); norm_num
  · show ((4640:ℝ)) ≤ (4680); norm_num
  · show ((4680:ℝ)) ≤ (4720); norm_num
  · show ((4720:ℝ)) ≤ (4760); norm_num
  · show ((4760:ℝ)) ≤ (4800); norm_num
  · show ((4800:ℝ)) ≤ (4840); norm_num
  · show ((4840:ℝ)) ≤ (4880); norm_num
  · show ((4880:ℝ)) ≤ (4920); norm_num
  · show ((4920:ℝ)) ≤ (4960); norm_num
  · show ((4960:ℝ)) ≤ (5000); norm_num
  · show ((5000:ℝ)) ≤ (5000); norm_num
  · exact le_refl _

/-- `1/4000000 ≤ dlvpRateC / log 5000` (`log 5000 ≤ 9`, `2.7^9 ≥ 5000`). -/
theorem haC_5000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 5000 := by
  have hlog : Real.log 5000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h9 : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 := pow_le_pow_left₀ (by norm_num) he1 9
    rw [h9]; nlinarith [hpow]
  have hpos : 0 < Real.log 5000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 5000
      ≤ (1 / 4000000) * 9 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[4000, 5000]` SEGMENT: every zero with `4000 ≤ Im ≤ 5000` is on the line. -/
theorem segment_4000_5000
    (hseg0 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((16639 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (19521 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (5000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 5000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (4000:ℝ) ≤ ρ.im → ρ.im ≤ 5000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 4000 5000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_5000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : ((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  interval_cases i
  · exact hseg0 ρ hre' ⟨le_trans (show ((4000) : ℝ) ≤ (4000) by norm_num) him.1, le_trans him.2 (show ((4040) : ℝ) ≤ (4040) by norm_num)⟩ hz
  · exact hseg1 ρ hre' ⟨le_trans (show ((4040) : ℝ) ≤ (4040) by norm_num) him.1, le_trans him.2 (show ((4080) : ℝ) ≤ (4080) by norm_num)⟩ hz
  · exact hseg2 ρ hre' ⟨le_trans (show ((4080) : ℝ) ≤ (4080) by norm_num) him.1, le_trans him.2 (show ((4120) : ℝ) ≤ (4120) by norm_num)⟩ hz
  · exact hseg3 ρ hre' ⟨le_trans (show ((4120) : ℝ) ≤ (4120) by norm_num) him.1, le_trans him.2 (show ((4160) : ℝ) ≤ (4160) by norm_num)⟩ hz
  · exact hseg4 ρ hre' ⟨le_trans (show ((16639 / 4) : ℝ) ≤ (4160) by norm_num) him.1, le_trans him.2 (show ((4200) : ℝ) ≤ (4200) by norm_num)⟩ hz
  · exact hseg5 ρ hre' ⟨le_trans (show ((4200) : ℝ) ≤ (4200) by norm_num) him.1, le_trans him.2 (show ((4240) : ℝ) ≤ (4240) by norm_num)⟩ hz
  · exact hseg6 ρ hre' ⟨le_trans (show ((4240) : ℝ) ≤ (4240) by norm_num) him.1, le_trans him.2 (show ((4280) : ℝ) ≤ (4280) by norm_num)⟩ hz
  · exact hseg7 ρ hre' ⟨le_trans (show ((4280) : ℝ) ≤ (4280) by norm_num) him.1, le_trans him.2 (show ((4320) : ℝ) ≤ (4320) by norm_num)⟩ hz
  · exact hseg8 ρ hre' ⟨le_trans (show ((4320) : ℝ) ≤ (4320) by norm_num) him.1, le_trans him.2 (show ((4360) : ℝ) ≤ (4360) by norm_num)⟩ hz
  · exact hseg9 ρ hre' ⟨le_trans (show ((4360) : ℝ) ≤ (4360) by norm_num) him.1, le_trans him.2 (show ((4400) : ℝ) ≤ (4400) by norm_num)⟩ hz
  · exact hseg10 ρ hre' ⟨le_trans (show ((4400) : ℝ) ≤ (4400) by norm_num) him.1, le_trans him.2 (show ((4440) : ℝ) ≤ (4440) by norm_num)⟩ hz
  · exact hseg11 ρ hre' ⟨le_trans (show ((4440) : ℝ) ≤ (4440) by norm_num) him.1, le_trans him.2 (show ((4480) : ℝ) ≤ (4480) by norm_num)⟩ hz
  · exact hseg12 ρ hre' ⟨le_trans (show ((4480) : ℝ) ≤ (4480) by norm_num) him.1, le_trans him.2 (show ((4520) : ℝ) ≤ (4520) by norm_num)⟩ hz
  · exact hseg13 ρ hre' ⟨le_trans (show ((4520) : ℝ) ≤ (4520) by norm_num) him.1, le_trans him.2 (show ((4560) : ℝ) ≤ (4560) by norm_num)⟩ hz
  · exact hseg14 ρ hre' ⟨le_trans (show ((4560) : ℝ) ≤ (4560) by norm_num) him.1, le_trans him.2 (show ((4600) : ℝ) ≤ (4600) by norm_num)⟩ hz
  · exact hseg15 ρ hre' ⟨le_trans (show ((4600) : ℝ) ≤ (4600) by norm_num) him.1, le_trans him.2 (show ((4640) : ℝ) ≤ (4640) by norm_num)⟩ hz
  · exact hseg16 ρ hre' ⟨le_trans (show ((4640) : ℝ) ≤ (4640) by norm_num) him.1, le_trans him.2 (show ((4680) : ℝ) ≤ (4680) by norm_num)⟩ hz
  · exact hseg17 ρ hre' ⟨le_trans (show ((4680) : ℝ) ≤ (4680) by norm_num) him.1, le_trans him.2 (show ((4720) : ℝ) ≤ (4720) by norm_num)⟩ hz
  · exact hseg18 ρ hre' ⟨le_trans (show ((4720) : ℝ) ≤ (4720) by norm_num) him.1, le_trans him.2 (show ((4760) : ℝ) ≤ (4760) by norm_num)⟩ hz
  · exact hseg19 ρ hre' ⟨le_trans (show ((4760) : ℝ) ≤ (4760) by norm_num) him.1, le_trans him.2 (show ((4800) : ℝ) ≤ (4800) by norm_num)⟩ hz
  · exact hseg20 ρ hre' ⟨le_trans (show ((4800) : ℝ) ≤ (4800) by norm_num) him.1, le_trans him.2 (show ((4840) : ℝ) ≤ (4840) by norm_num)⟩ hz
  · exact hseg21 ρ hre' ⟨le_trans (show ((4840) : ℝ) ≤ (4840) by norm_num) him.1, le_trans him.2 (show ((4880) : ℝ) ≤ (19521 / 4) by norm_num)⟩ hz
  · exact hseg22 ρ hre' ⟨le_trans (show ((4880) : ℝ) ≤ (4880) by norm_num) him.1, le_trans him.2 (show ((4920) : ℝ) ≤ (4920) by norm_num)⟩ hz
  · exact hseg23 ρ hre' ⟨le_trans (show ((4920) : ℝ) ≤ (4920) by norm_num) him.1, le_trans him.2 (show ((4960) : ℝ) ≤ (4960) by norm_num)⟩ hz
  · exact hseg24 ρ hre' ⟨le_trans (show ((4960) : ℝ) ≤ (4960) by norm_num) him.1, le_trans him.2 (show ((5000) : ℝ) ≤ (5000) by norm_num)⟩ hz

/-- **T = 5000 via the HEIGHT CHAIN**: `[0,4000]` ∘ `[4000,5000]` (segment).
    conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_5000_of_bands
    (hband0 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (41)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband1 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((41) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (81)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband2 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((81) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (121)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband3 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((121) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (161)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband4 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((161) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (201)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband5 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((201) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (965 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband6 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((241) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (281)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband7 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((281) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (321)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband8 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((321) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (361)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband9 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((361) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (401)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband10 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((401) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (441)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband11 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((441) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (481)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband12 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((481) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband13 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband14 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband15 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband16 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband17 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband18 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband19 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband20 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband21 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband22 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband23 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband24 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband25 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband26 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband27 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband28 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband29 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband30 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband31 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband32 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband33 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((5279 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband34 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband35 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband36 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband37 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband38 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband39 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (6401 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband40 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband41 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (6721 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband42 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband43 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband44 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (7201 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband45 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband46 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband47 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband48 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((7679 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband49 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband50 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband51 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband52 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband53 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband54 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband55 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (8961 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband56 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband57 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband58 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband59 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband60 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband61 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((9759 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband62 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((9919 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband63 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband64 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband65 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (10561 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband66 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (10721 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband67 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband68 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband69 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (11201 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband70 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband71 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband72 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband73 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (11841 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband74 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((2960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband75 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband76 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband77 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband78 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((12479 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband79 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband80 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband81 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband82 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband83 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband84 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband85 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband86 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband87 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband88 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (14241 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband89 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband90 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband91 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband92 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband93 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband94 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband95 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband96 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((15359 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband97 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband98 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (15841 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband99 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((3960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (16001 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg0 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((16639 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (19521 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((4960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (5000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 5000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 5000 → ρ.re = 1 / 2 := by
  have hγ4000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 4000 5000
    (AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands
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
    hband39
    hband40
    hband41
    hband42
    hband43
    hband44
    hband45
    hband46
    hband47
    hband48
    hband49
    hband50
    hband51
    hband52
    hband53
    hband54
    hband55
    hband56
    hband57
    hband58
    hband59
    hband60
    hband61
    hband62
    hband63
    hband64
    hband65
    hband66
    hband67
    hband68
    hband69
    hband70
    hband71
    hband72
    hband73
    hband74
    hband75
    hband76
    hband77
    hband78
    hband79
    hband80
    hband81
    hband82
    hband83
    hband84
    hband85
    hband86
    hband87
    hband88
    hband89
    hband90
    hband91
    hband92
    hband93
    hband94
    hband95
    hband96
    hband97
    hband98
    hband99
      hγ4000)
    (segment_4000_5000
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
      hγ)

end AllZeros_h5000
