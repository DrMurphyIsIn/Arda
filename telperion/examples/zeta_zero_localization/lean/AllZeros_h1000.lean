/-  Height-chain step: all nontrivial zeta zeros up to height 1000 on Re = 1/2 --
    `AllZeros_h1` + a `[1, 1000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  Emitted by campaign.py.
    conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import RHInBoxT_1d4000000_3999999d4000000_1_41
import RHInBoxT_1d4000000_3999999d4000000_41_81
import RHInBoxT_1d4000000_3999999d4000000_81_121
import RHInBoxT_1d4000000_3999999d4000000_121_161
import RHInBoxT_1d4000000_3999999d4000000_161_201
import RHInBoxT_1d4000000_3999999d4000000_201_965d4
import RHInBoxT_1d4000000_3999999d4000000_241_281
import RHInBoxT_1d4000000_3999999d4000000_281_321
import RHInBoxT_1d4000000_3999999d4000000_321_361
import RHInBoxT_1d4000000_3999999d4000000_361_401
import RHInBoxT_1d4000000_3999999d4000000_401_441
import RHInBoxT_1d4000000_3999999d4000000_441_481
import RHInBoxT_1d4000000_3999999d4000000_481_520
import RHInBoxT_1d4000000_3999999d4000000_520_560
import RHInBoxT_1d4000000_3999999d4000000_560_600
import RHInBoxT_1d4000000_3999999d4000000_600_640
import RHInBoxT_1d4000000_3999999d4000000_640_680
import RHInBoxT_1d4000000_3999999d4000000_680_720
import RHInBoxT_1d4000000_3999999d4000000_720_760
import RHInBoxT_1d4000000_3999999d4000000_760_800
import RHInBoxT_1d4000000_3999999d4000000_800_840
import RHInBoxT_1d4000000_3999999d4000000_840_880
import RHInBoxT_1d4000000_3999999d4000000_880_920
import RHInBoxT_1d4000000_3999999d4000000_920_960
import RHInBoxT_1d4000000_3999999d4000000_960_1000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h1000

/-- The 25-band partition of `[1, 1000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 1
  | 1 => 41
  | 2 => 81
  | 3 => 121
  | 4 => 161
  | 5 => 201
  | 6 => 241
  | 7 => 281
  | 8 => 321
  | 9 => 361
  | 10 => 401
  | 11 => 441
  | 12 => 481
  | 13 => 520
  | 14 => 560
  | 15 => 600
  | 16 => 640
  | 17 => 680
  | 18 => 720
  | 19 => 760
  | 20 => 800
  | 21 => 840
  | 22 => 880
  | 23 => 920
  | 24 => 960
  | 25 => 1000
  | _ => 1000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((1:ℝ)) ≤ (41); norm_num
  · show ((41:ℝ)) ≤ (81); norm_num
  · show ((81:ℝ)) ≤ (121); norm_num
  · show ((121:ℝ)) ≤ (161); norm_num
  · show ((161:ℝ)) ≤ (201); norm_num
  · show ((201:ℝ)) ≤ (241); norm_num
  · show ((241:ℝ)) ≤ (281); norm_num
  · show ((281:ℝ)) ≤ (321); norm_num
  · show ((321:ℝ)) ≤ (361); norm_num
  · show ((361:ℝ)) ≤ (401); norm_num
  · show ((401:ℝ)) ≤ (441); norm_num
  · show ((441:ℝ)) ≤ (481); norm_num
  · show ((481:ℝ)) ≤ (520); norm_num
  · show ((520:ℝ)) ≤ (560); norm_num
  · show ((560:ℝ)) ≤ (600); norm_num
  · show ((600:ℝ)) ≤ (640); norm_num
  · show ((640:ℝ)) ≤ (680); norm_num
  · show ((680:ℝ)) ≤ (720); norm_num
  · show ((720:ℝ)) ≤ (760); norm_num
  · show ((760:ℝ)) ≤ (800); norm_num
  · show ((800:ℝ)) ≤ (840); norm_num
  · show ((840:ℝ)) ≤ (880); norm_num
  · show ((880:ℝ)) ≤ (920); norm_num
  · show ((920:ℝ)) ≤ (960); norm_num
  · show ((960:ℝ)) ≤ (1000); norm_num
  · show ((1000:ℝ)) ≤ (1000); norm_num
  · exact le_refl _

/-- `1/4000000 ≤ dlvpRateC / log 1000` (`log 1000 ≤ 7`, `2.7^7 ≥ 1000`). -/
theorem haC_1000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 1000 := by
  have hlog : Real.log 1000 ≤ 7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h7 : Real.exp 7 = (Real.exp 1) ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) he1 7
    rw [h7]; nlinarith [hpow]
  have hpos : 0 < Real.log 1000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 1000
      ≤ (1 / 4000000) * 7 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[1, 1000]` SEGMENT: every zero with `1 ≤ Im ≤ 1000` is on the line. -/
theorem segment_1_1000
    (hseg0 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (41)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((41) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (81)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((81) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (121)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((121) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (161)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((161) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (201)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((201) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (965 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((241) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (281)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((281) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (321)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((321) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (361)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((361) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (401)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((401) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (441)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((441) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (481)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((481) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (1:ℝ) ≤ ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 1 1000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_1000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : ((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  interval_cases i
  · exact hseg0 ρ hre' ⟨le_trans (show ((1) : ℝ) ≤ (1) by norm_num) him.1, le_trans him.2 (show ((41) : ℝ) ≤ (41) by norm_num)⟩ hz
  · exact hseg1 ρ hre' ⟨le_trans (show ((41) : ℝ) ≤ (41) by norm_num) him.1, le_trans him.2 (show ((81) : ℝ) ≤ (81) by norm_num)⟩ hz
  · exact hseg2 ρ hre' ⟨le_trans (show ((81) : ℝ) ≤ (81) by norm_num) him.1, le_trans him.2 (show ((121) : ℝ) ≤ (121) by norm_num)⟩ hz
  · exact hseg3 ρ hre' ⟨le_trans (show ((121) : ℝ) ≤ (121) by norm_num) him.1, le_trans him.2 (show ((161) : ℝ) ≤ (161) by norm_num)⟩ hz
  · exact hseg4 ρ hre' ⟨le_trans (show ((161) : ℝ) ≤ (161) by norm_num) him.1, le_trans him.2 (show ((201) : ℝ) ≤ (201) by norm_num)⟩ hz
  · exact hseg5 ρ hre' ⟨le_trans (show ((201) : ℝ) ≤ (201) by norm_num) him.1, le_trans him.2 (show ((241) : ℝ) ≤ (965 / 4) by norm_num)⟩ hz
  · exact hseg6 ρ hre' ⟨le_trans (show ((241) : ℝ) ≤ (241) by norm_num) him.1, le_trans him.2 (show ((281) : ℝ) ≤ (281) by norm_num)⟩ hz
  · exact hseg7 ρ hre' ⟨le_trans (show ((281) : ℝ) ≤ (281) by norm_num) him.1, le_trans him.2 (show ((321) : ℝ) ≤ (321) by norm_num)⟩ hz
  · exact hseg8 ρ hre' ⟨le_trans (show ((321) : ℝ) ≤ (321) by norm_num) him.1, le_trans him.2 (show ((361) : ℝ) ≤ (361) by norm_num)⟩ hz
  · exact hseg9 ρ hre' ⟨le_trans (show ((361) : ℝ) ≤ (361) by norm_num) him.1, le_trans him.2 (show ((401) : ℝ) ≤ (401) by norm_num)⟩ hz
  · exact hseg10 ρ hre' ⟨le_trans (show ((401) : ℝ) ≤ (401) by norm_num) him.1, le_trans him.2 (show ((441) : ℝ) ≤ (441) by norm_num)⟩ hz
  · exact hseg11 ρ hre' ⟨le_trans (show ((441) : ℝ) ≤ (441) by norm_num) him.1, le_trans him.2 (show ((481) : ℝ) ≤ (481) by norm_num)⟩ hz
  · exact hseg12 ρ hre' ⟨le_trans (show ((481) : ℝ) ≤ (481) by norm_num) him.1, le_trans him.2 (show ((520) : ℝ) ≤ (520) by norm_num)⟩ hz
  · exact hseg13 ρ hre' ⟨le_trans (show ((520) : ℝ) ≤ (520) by norm_num) him.1, le_trans him.2 (show ((560) : ℝ) ≤ (560) by norm_num)⟩ hz
  · exact hseg14 ρ hre' ⟨le_trans (show ((560) : ℝ) ≤ (560) by norm_num) him.1, le_trans him.2 (show ((600) : ℝ) ≤ (600) by norm_num)⟩ hz
  · exact hseg15 ρ hre' ⟨le_trans (show ((600) : ℝ) ≤ (600) by norm_num) him.1, le_trans him.2 (show ((640) : ℝ) ≤ (640) by norm_num)⟩ hz
  · exact hseg16 ρ hre' ⟨le_trans (show ((640) : ℝ) ≤ (640) by norm_num) him.1, le_trans him.2 (show ((680) : ℝ) ≤ (680) by norm_num)⟩ hz
  · exact hseg17 ρ hre' ⟨le_trans (show ((680) : ℝ) ≤ (680) by norm_num) him.1, le_trans him.2 (show ((720) : ℝ) ≤ (720) by norm_num)⟩ hz
  · exact hseg18 ρ hre' ⟨le_trans (show ((720) : ℝ) ≤ (720) by norm_num) him.1, le_trans him.2 (show ((760) : ℝ) ≤ (760) by norm_num)⟩ hz
  · exact hseg19 ρ hre' ⟨le_trans (show ((760) : ℝ) ≤ (760) by norm_num) him.1, le_trans him.2 (show ((800) : ℝ) ≤ (800) by norm_num)⟩ hz
  · exact hseg20 ρ hre' ⟨le_trans (show ((800) : ℝ) ≤ (800) by norm_num) him.1, le_trans him.2 (show ((840) : ℝ) ≤ (840) by norm_num)⟩ hz
  · exact hseg21 ρ hre' ⟨le_trans (show ((840) : ℝ) ≤ (840) by norm_num) him.1, le_trans him.2 (show ((880) : ℝ) ≤ (880) by norm_num)⟩ hz
  · exact hseg22 ρ hre' ⟨le_trans (show ((880) : ℝ) ≤ (880) by norm_num) him.1, le_trans him.2 (show ((920) : ℝ) ≤ (920) by norm_num)⟩ hz
  · exact hseg23 ρ hre' ⟨le_trans (show ((920) : ℝ) ≤ (920) by norm_num) him.1, le_trans him.2 (show ((960) : ℝ) ≤ (960) by norm_num)⟩ hz
  · exact hseg24 ρ hre' ⟨le_trans (show ((960) : ℝ) ≤ (960) by norm_num) him.1, le_trans him.2 (show ((1000) : ℝ) ≤ (1000) by norm_num)⟩ hz

/-- Below height 1 the ladder is vacuous: the height floor `55/16 ≤ |Im ρ|`
    (carried `hγ`, discharged by StripClear at assembly) contradicts `Im ρ ≤ 1`. -/
theorem upTo_1
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1 → ρ.re = 1 / 2 := by
  intro ρ hz h0 h1
  have h := hγ ρ hz h0 h1
  rw [abs_of_pos h0] at h
  have habs : (55 / 16 : ℝ) ≤ 1 := le_trans h h1
  norm_num at habs

/-- **T = 1000 via the HEIGHT CHAIN**: `[0,1]` ∘ `[1,1000]` (segment).
    conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_1000_of_bands
    (hseg0 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (41)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((41) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (81)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((81) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (121)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((121) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (161)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((161) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (201)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((201) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (965 / 4)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((241) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (281)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((281) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (321)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((321) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (361)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((361) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (401)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((401) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (441)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((441) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (481)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((481) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by
  have hγ1 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 1 1000
    (upTo_1 hγ1)
    (segment_1_1000
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

end AllZeros_h1000
