/-  Height-chain step: all nontrivial zeta zeros up to height 1000 on Re = 1/2 --
    `AllZeros_h1` + a `[1, 1000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
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

/-- The 25-band NOMINAL partition of `[1, 1000]`. -/
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

/-- The lower edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
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
  | _ => 960

/-- The upper edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 41
  | 1 => 81
  | 2 => 121
  | 3 => 161
  | 4 => 201
  | 5 => 965 / 4
  | 6 => 281
  | 7 => 321
  | 8 => 361
  | 9 => 401
  | 10 => 441
  | 11 => 481
  | 12 => 520
  | 13 => 560
  | 14 => 600
  | 15 => 640
  | 16 => 680
  | 17 => 720
  | 18 => 760
  | 19 => 800
  | 20 => 840
  | 21 => 880
  | 22 => 920
  | 23 => 960
  | 24 => 1000
  | _ => 1000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 25 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

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

/-- The `[1, 1000]` segment's band hypothesis: every band `i < 25` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 25 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 25 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[1, 1000]` SEGMENT: every zero with `1 ≤ Im ≤ 1000` is on the line. -/
theorem segment_1_1000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (1:ℝ) ≤ ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 1 1000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_1000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

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
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_1000_of_bands
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by
  have hγ1 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 1 1000
    (upTo_1 hγ1)
    (segment_1_1000 hbands hγ)

end AllZeros_h1000
