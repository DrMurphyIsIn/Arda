/-  Height-chain step: all nontrivial zeta zeros up to height 2000 on Re = 1/2 --
    `AllZeros_h1000` + a `[1000, 2000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  Emitted by campaign.py.
    conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h1000
import RHInBoxT_1d4000000_3999999d4000000_1000_1040
import RHInBoxT_1d4000000_3999999d4000000_1040_1080
import RHInBoxT_1d4000000_3999999d4000000_1080_1120
import RHInBoxT_1d4000000_3999999d4000000_1120_1160
import RHInBoxT_1d4000000_3999999d4000000_1160_1200
import RHInBoxT_1d4000000_3999999d4000000_1200_1240
import RHInBoxT_1d4000000_3999999d4000000_1240_1280
import RHInBoxT_1d4000000_3999999d4000000_1280_1320
import RHInBoxT_1d4000000_3999999d4000000_5279d4_1360
import RHInBoxT_1d4000000_3999999d4000000_1360_1400
import RHInBoxT_1d4000000_3999999d4000000_1400_1440
import RHInBoxT_1d4000000_3999999d4000000_1440_1480
import RHInBoxT_1d4000000_3999999d4000000_1480_1520
import RHInBoxT_1d4000000_3999999d4000000_1520_1560
import RHInBoxT_1d4000000_3999999d4000000_1560_6401d4
import RHInBoxT_1d4000000_3999999d4000000_1600_1640
import RHInBoxT_1d4000000_3999999d4000000_1640_6721d4
import RHInBoxT_1d4000000_3999999d4000000_1680_1720
import RHInBoxT_1d4000000_3999999d4000000_1720_1760
import RHInBoxT_1d4000000_3999999d4000000_1760_7201d4
import RHInBoxT_1d4000000_3999999d4000000_1800_1840
import RHInBoxT_1d4000000_3999999d4000000_1840_1880
import RHInBoxT_1d4000000_3999999d4000000_1880_1920
import RHInBoxT_1d4000000_3999999d4000000_7679d4_1960
import RHInBoxT_1d4000000_3999999d4000000_1960_2000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h2000

/-- The 25-band partition of `[1000, 2000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 1000
  | 1 => 1040
  | 2 => 1080
  | 3 => 1120
  | 4 => 1160
  | 5 => 1200
  | 6 => 1240
  | 7 => 1280
  | 8 => 1320
  | 9 => 1360
  | 10 => 1400
  | 11 => 1440
  | 12 => 1480
  | 13 => 1520
  | 14 => 1560
  | 15 => 1600
  | 16 => 1640
  | 17 => 1680
  | 18 => 1720
  | 19 => 1760
  | 20 => 1800
  | 21 => 1840
  | 22 => 1880
  | 23 => 1920
  | 24 => 1960
  | 25 => 2000
  | _ => 2000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((1000:ℝ)) ≤ (1040); norm_num
  · show ((1040:ℝ)) ≤ (1080); norm_num
  · show ((1080:ℝ)) ≤ (1120); norm_num
  · show ((1120:ℝ)) ≤ (1160); norm_num
  · show ((1160:ℝ)) ≤ (1200); norm_num
  · show ((1200:ℝ)) ≤ (1240); norm_num
  · show ((1240:ℝ)) ≤ (1280); norm_num
  · show ((1280:ℝ)) ≤ (1320); norm_num
  · show ((1320:ℝ)) ≤ (1360); norm_num
  · show ((1360:ℝ)) ≤ (1400); norm_num
  · show ((1400:ℝ)) ≤ (1440); norm_num
  · show ((1440:ℝ)) ≤ (1480); norm_num
  · show ((1480:ℝ)) ≤ (1520); norm_num
  · show ((1520:ℝ)) ≤ (1560); norm_num
  · show ((1560:ℝ)) ≤ (1600); norm_num
  · show ((1600:ℝ)) ≤ (1640); norm_num
  · show ((1640:ℝ)) ≤ (1680); norm_num
  · show ((1680:ℝ)) ≤ (1720); norm_num
  · show ((1720:ℝ)) ≤ (1760); norm_num
  · show ((1760:ℝ)) ≤ (1800); norm_num
  · show ((1800:ℝ)) ≤ (1840); norm_num
  · show ((1840:ℝ)) ≤ (1880); norm_num
  · show ((1880:ℝ)) ≤ (1920); norm_num
  · show ((1920:ℝ)) ≤ (1960); norm_num
  · show ((1960:ℝ)) ≤ (2000); norm_num
  · show ((2000:ℝ)) ≤ (2000); norm_num
  · exact le_refl _

/-- `1/4000000 ≤ dlvpRateC / log 2000` (`log 2000 ≤ 8`, `2.7^8 ≥ 2000`). -/
theorem haC_2000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 2000 := by
  have hlog : Real.log 2000 ≤ 8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h8 : Real.exp 8 = (Real.exp 1) ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 8 ≤ (Real.exp 1) ^ 8 := pow_le_pow_left₀ (by norm_num) he1 8
    rw [h8]; nlinarith [hpow]
  have hpos : 0 < Real.log 2000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 2000
      ≤ (1 / 4000000) * 8 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[1000, 2000]` SEGMENT: every zero with `1000 ≤ Im ≤ 2000` is on the line. -/
theorem segment_1000_2000
    (hseg0 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((5279 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (6401 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (6721 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (7201 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((7679 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (1000:ℝ) ≤ ρ.im → ρ.im ≤ 2000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 1000 2000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_2000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : ((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  interval_cases i
  · exact hseg0 ρ hre' ⟨le_trans (show ((1000) : ℝ) ≤ (1000) by norm_num) him.1, le_trans him.2 (show ((1040) : ℝ) ≤ (1040) by norm_num)⟩ hz
  · exact hseg1 ρ hre' ⟨le_trans (show ((1040) : ℝ) ≤ (1040) by norm_num) him.1, le_trans him.2 (show ((1080) : ℝ) ≤ (1080) by norm_num)⟩ hz
  · exact hseg2 ρ hre' ⟨le_trans (show ((1080) : ℝ) ≤ (1080) by norm_num) him.1, le_trans him.2 (show ((1120) : ℝ) ≤ (1120) by norm_num)⟩ hz
  · exact hseg3 ρ hre' ⟨le_trans (show ((1120) : ℝ) ≤ (1120) by norm_num) him.1, le_trans him.2 (show ((1160) : ℝ) ≤ (1160) by norm_num)⟩ hz
  · exact hseg4 ρ hre' ⟨le_trans (show ((1160) : ℝ) ≤ (1160) by norm_num) him.1, le_trans him.2 (show ((1200) : ℝ) ≤ (1200) by norm_num)⟩ hz
  · exact hseg5 ρ hre' ⟨le_trans (show ((1200) : ℝ) ≤ (1200) by norm_num) him.1, le_trans him.2 (show ((1240) : ℝ) ≤ (1240) by norm_num)⟩ hz
  · exact hseg6 ρ hre' ⟨le_trans (show ((1240) : ℝ) ≤ (1240) by norm_num) him.1, le_trans him.2 (show ((1280) : ℝ) ≤ (1280) by norm_num)⟩ hz
  · exact hseg7 ρ hre' ⟨le_trans (show ((1280) : ℝ) ≤ (1280) by norm_num) him.1, le_trans him.2 (show ((1320) : ℝ) ≤ (1320) by norm_num)⟩ hz
  · exact hseg8 ρ hre' ⟨le_trans (show ((5279 / 4) : ℝ) ≤ (1320) by norm_num) him.1, le_trans him.2 (show ((1360) : ℝ) ≤ (1360) by norm_num)⟩ hz
  · exact hseg9 ρ hre' ⟨le_trans (show ((1360) : ℝ) ≤ (1360) by norm_num) him.1, le_trans him.2 (show ((1400) : ℝ) ≤ (1400) by norm_num)⟩ hz
  · exact hseg10 ρ hre' ⟨le_trans (show ((1400) : ℝ) ≤ (1400) by norm_num) him.1, le_trans him.2 (show ((1440) : ℝ) ≤ (1440) by norm_num)⟩ hz
  · exact hseg11 ρ hre' ⟨le_trans (show ((1440) : ℝ) ≤ (1440) by norm_num) him.1, le_trans him.2 (show ((1480) : ℝ) ≤ (1480) by norm_num)⟩ hz
  · exact hseg12 ρ hre' ⟨le_trans (show ((1480) : ℝ) ≤ (1480) by norm_num) him.1, le_trans him.2 (show ((1520) : ℝ) ≤ (1520) by norm_num)⟩ hz
  · exact hseg13 ρ hre' ⟨le_trans (show ((1520) : ℝ) ≤ (1520) by norm_num) him.1, le_trans him.2 (show ((1560) : ℝ) ≤ (1560) by norm_num)⟩ hz
  · exact hseg14 ρ hre' ⟨le_trans (show ((1560) : ℝ) ≤ (1560) by norm_num) him.1, le_trans him.2 (show ((1600) : ℝ) ≤ (6401 / 4) by norm_num)⟩ hz
  · exact hseg15 ρ hre' ⟨le_trans (show ((1600) : ℝ) ≤ (1600) by norm_num) him.1, le_trans him.2 (show ((1640) : ℝ) ≤ (1640) by norm_num)⟩ hz
  · exact hseg16 ρ hre' ⟨le_trans (show ((1640) : ℝ) ≤ (1640) by norm_num) him.1, le_trans him.2 (show ((1680) : ℝ) ≤ (6721 / 4) by norm_num)⟩ hz
  · exact hseg17 ρ hre' ⟨le_trans (show ((1680) : ℝ) ≤ (1680) by norm_num) him.1, le_trans him.2 (show ((1720) : ℝ) ≤ (1720) by norm_num)⟩ hz
  · exact hseg18 ρ hre' ⟨le_trans (show ((1720) : ℝ) ≤ (1720) by norm_num) him.1, le_trans him.2 (show ((1760) : ℝ) ≤ (1760) by norm_num)⟩ hz
  · exact hseg19 ρ hre' ⟨le_trans (show ((1760) : ℝ) ≤ (1760) by norm_num) him.1, le_trans him.2 (show ((1800) : ℝ) ≤ (7201 / 4) by norm_num)⟩ hz
  · exact hseg20 ρ hre' ⟨le_trans (show ((1800) : ℝ) ≤ (1800) by norm_num) him.1, le_trans him.2 (show ((1840) : ℝ) ≤ (1840) by norm_num)⟩ hz
  · exact hseg21 ρ hre' ⟨le_trans (show ((1840) : ℝ) ≤ (1840) by norm_num) him.1, le_trans him.2 (show ((1880) : ℝ) ≤ (1880) by norm_num)⟩ hz
  · exact hseg22 ρ hre' ⟨le_trans (show ((1880) : ℝ) ≤ (1880) by norm_num) him.1, le_trans him.2 (show ((1920) : ℝ) ≤ (1920) by norm_num)⟩ hz
  · exact hseg23 ρ hre' ⟨le_trans (show ((7679 / 4) : ℝ) ≤ (1920) by norm_num) him.1, le_trans him.2 (show ((1960) : ℝ) ≤ (1960) by norm_num)⟩ hz
  · exact hseg24 ρ hre' ⟨le_trans (show ((1960) : ℝ) ≤ (1960) by norm_num) him.1, le_trans him.2 (show ((2000) : ℝ) ≤ (2000) by norm_num)⟩ hz

/-- **T = 2000 via the HEIGHT CHAIN**: `[0,1000]` ∘ `[1000,2000]` (segment).
    conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_2000_of_bands
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
    (hseg0 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((5279 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (6401 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (6721 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (7201 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((7679 / 4) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → ρ.re = 1 / 2 := by
  have hγ1000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 1000 2000
    (AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands
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
      hγ1000)
    (segment_1000_2000
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

end AllZeros_h2000
