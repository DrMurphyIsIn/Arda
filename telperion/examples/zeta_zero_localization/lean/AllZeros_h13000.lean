/-  Height-chain step: all nontrivial zeta zeros up to height 13000 on Re = 1/2 --
    `AllZeros_h12000` + a `[12000, 13000]` SEGMENT certificate (29 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h12000
import RHInBoxT_1d4000000_3999999d4000000_12000_12034
import RHInBoxT_1d4000000_3999999d4000000_12034_48277d4
import RHInBoxT_1d4000000_3999999d4000000_12069_12103
import RHInBoxT_1d4000000_3999999d4000000_12103_12138
import RHInBoxT_1d4000000_3999999d4000000_12138_12172
import RHInBoxT_1d4000000_3999999d4000000_12172_12207
import RHInBoxT_1d4000000_3999999d4000000_48827d4_12241
import RHInBoxT_1d4000000_3999999d4000000_12241_12276
import RHInBoxT_1d4000000_3999999d4000000_12276_12310
import RHInBoxT_1d4000000_3999999d4000000_12310_12345
import RHInBoxT_1d4000000_3999999d4000000_12345_12379
import RHInBoxT_1d4000000_3999999d4000000_12379_12414
import RHInBoxT_1d4000000_3999999d4000000_12414_12448
import RHInBoxT_1d4000000_3999999d4000000_12448_12483
import RHInBoxT_1d4000000_3999999d4000000_12483_12517
import RHInBoxT_1d4000000_3999999d4000000_12517_50209d4
import RHInBoxT_1d4000000_3999999d4000000_12552_12586
import RHInBoxT_1d4000000_3999999d4000000_12586_12621
import RHInBoxT_1d4000000_3999999d4000000_12621_12655
import RHInBoxT_1d4000000_3999999d4000000_50619d4_12690
import RHInBoxT_1d4000000_3999999d4000000_12690_12724
import RHInBoxT_1d4000000_3999999d4000000_12724_12759
import RHInBoxT_1d4000000_3999999d4000000_12759_12793
import RHInBoxT_1d4000000_3999999d4000000_12793_12828
import RHInBoxT_1d4000000_3999999d4000000_12828_12862
import RHInBoxT_1d4000000_3999999d4000000_12862_12897
import RHInBoxT_1d4000000_3999999d4000000_12897_12931
import RHInBoxT_1d4000000_3999999d4000000_12931_12966
import RHInBoxT_1d4000000_3999999d4000000_12966_13000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h13000

/-- The 29-band NOMINAL partition of `[12000, 13000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 12000
  | 1 => 12034
  | 2 => 12069
  | 3 => 12103
  | 4 => 12138
  | 5 => 12172
  | 6 => 12207
  | 7 => 12241
  | 8 => 12276
  | 9 => 12310
  | 10 => 12345
  | 11 => 12379
  | 12 => 12414
  | 13 => 12448
  | 14 => 12483
  | 15 => 12517
  | 16 => 12552
  | 17 => 12586
  | 18 => 12621
  | 19 => 12655
  | 20 => 12690
  | 21 => 12724
  | 22 => 12759
  | 23 => 12793
  | 24 => 12828
  | 25 => 12862
  | 26 => 12897
  | 27 => 12931
  | 28 => 12966
  | 29 => 13000
  | _ => 13000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((12000:ℝ)) ≤ (12034); norm_num
  · show ((12034:ℝ)) ≤ (12069); norm_num
  · show ((12069:ℝ)) ≤ (12103); norm_num
  · show ((12103:ℝ)) ≤ (12138); norm_num
  · show ((12138:ℝ)) ≤ (12172); norm_num
  · show ((12172:ℝ)) ≤ (12207); norm_num
  · show ((12207:ℝ)) ≤ (12241); norm_num
  · show ((12241:ℝ)) ≤ (12276); norm_num
  · show ((12276:ℝ)) ≤ (12310); norm_num
  · show ((12310:ℝ)) ≤ (12345); norm_num
  · show ((12345:ℝ)) ≤ (12379); norm_num
  · show ((12379:ℝ)) ≤ (12414); norm_num
  · show ((12414:ℝ)) ≤ (12448); norm_num
  · show ((12448:ℝ)) ≤ (12483); norm_num
  · show ((12483:ℝ)) ≤ (12517); norm_num
  · show ((12517:ℝ)) ≤ (12552); norm_num
  · show ((12552:ℝ)) ≤ (12586); norm_num
  · show ((12586:ℝ)) ≤ (12621); norm_num
  · show ((12621:ℝ)) ≤ (12655); norm_num
  · show ((12655:ℝ)) ≤ (12690); norm_num
  · show ((12690:ℝ)) ≤ (12724); norm_num
  · show ((12724:ℝ)) ≤ (12759); norm_num
  · show ((12759:ℝ)) ≤ (12793); norm_num
  · show ((12793:ℝ)) ≤ (12828); norm_num
  · show ((12828:ℝ)) ≤ (12862); norm_num
  · show ((12862:ℝ)) ≤ (12897); norm_num
  · show ((12897:ℝ)) ≤ (12931); norm_num
  · show ((12931:ℝ)) ≤ (12966); norm_num
  · show ((12966:ℝ)) ≤ (13000); norm_num
  · show ((13000:ℝ)) ≤ (13000); norm_num
  · exact le_refl _

/-- The lower edges of the 29 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 12000
  | 1 => 12034
  | 2 => 12069
  | 3 => 12103
  | 4 => 12138
  | 5 => 12172
  | 6 => 48827 / 4
  | 7 => 12241
  | 8 => 12276
  | 9 => 12310
  | 10 => 12345
  | 11 => 12379
  | 12 => 12414
  | 13 => 12448
  | 14 => 12483
  | 15 => 12517
  | 16 => 12552
  | 17 => 12586
  | 18 => 12621
  | 19 => 50619 / 4
  | 20 => 12690
  | 21 => 12724
  | 22 => 12759
  | 23 => 12793
  | 24 => 12828
  | 25 => 12862
  | 26 => 12897
  | 27 => 12931
  | 28 => 12966
  | _ => 12966

/-- The upper edges of the 29 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 12034
  | 1 => 48277 / 4
  | 2 => 12103
  | 3 => 12138
  | 4 => 12172
  | 5 => 12207
  | 6 => 12241
  | 7 => 12276
  | 8 => 12310
  | 9 => 12345
  | 10 => 12379
  | 11 => 12414
  | 12 => 12448
  | 13 => 12483
  | 14 => 12517
  | 15 => 50209 / 4
  | 16 => 12586
  | 17 => 12621
  | 18 => 12655
  | 19 => 12690
  | 20 => 12724
  | 21 => 12759
  | 22 => 12793
  | 23 => 12828
  | 24 => 12862
  | 25 => 12897
  | 26 => 12931
  | 27 => 12966
  | 28 => 13000
  | _ => 13000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 29 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 13000` (`log 13000 ≤ 10`, `2.7^10 ≥ 13000`). -/
theorem haC_13000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 13000 := by
  have hlog : Real.log 13000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 13000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 13000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[12000, 13000]` segment's band hypothesis: every band `i < 29` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 29 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 29 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[12000, 13000]` SEGMENT: every zero with `12000 ≤ Im ≤ 13000` is on the line. -/
theorem segment_12000_13000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 13000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (12000:ℝ) ≤ ρ.im → ρ.im ≤ 13000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 12000 13000 bndSeg 29 (by norm_num) bndSeg_mono rfl rfl haC_13000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 13000 via the HEIGHT CHAIN**: `[0,12000]` ∘ `[12000,13000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_13000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands_6000 : AllZeros_h6000.BandHyp)
    (hbands_7000 : AllZeros_h7000.BandHyp)
    (hbands_8000 : AllZeros_h8000.BandHyp)
    (hbands_9000 : AllZeros_h9000.BandHyp)
    (hbands_10000 : AllZeros_h10000.BandHyp)
    (hbands_11000 : AllZeros_h11000.BandHyp)
    (hbands_12000 : AllZeros_h12000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 13000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 13000 → ρ.re = 1 / 2 := by
  have hγ12000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 12000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 12000 13000
    (AllZeros_h12000.all_nontrivial_zeros_up_to_height_12000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hbands_6000
      hbands_7000
      hbands_8000
      hbands_9000
      hbands_10000
      hbands_11000
      hbands_12000
      hγ12000)
    (segment_12000_13000 hbands hγ)

end AllZeros_h13000
