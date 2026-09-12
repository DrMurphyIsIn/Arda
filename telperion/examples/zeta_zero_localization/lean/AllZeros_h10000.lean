/-  Height-chain step: all nontrivial zeta zeros up to height 10000 on Re = 1/2 --
    `AllZeros_h9000` + a `[9000, 10000]` SEGMENT certificate (28 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h9000
import RHInBoxT_1d4000000_3999999d4000000_9000_9036
import RHInBoxT_1d4000000_3999999d4000000_9036_9071
import RHInBoxT_1d4000000_3999999d4000000_9071_9107
import RHInBoxT_1d4000000_3999999d4000000_9107_9143
import RHInBoxT_1d4000000_3999999d4000000_9143_9179
import RHInBoxT_1d4000000_3999999d4000000_9179_9214
import RHInBoxT_1d4000000_3999999d4000000_36855d4_9250
import RHInBoxT_1d4000000_3999999d4000000_9250_9286
import RHInBoxT_1d4000000_3999999d4000000_9286_9321
import RHInBoxT_1d4000000_3999999d4000000_9321_9357
import RHInBoxT_1d4000000_3999999d4000000_9357_9393
import RHInBoxT_1d4000000_3999999d4000000_37571d4_9429
import RHInBoxT_1d4000000_3999999d4000000_9429_9464
import RHInBoxT_1d4000000_3999999d4000000_9464_9500
import RHInBoxT_1d4000000_3999999d4000000_9500_9536
import RHInBoxT_1d4000000_3999999d4000000_9536_9571
import RHInBoxT_1d4000000_3999999d4000000_9571_9607
import RHInBoxT_1d4000000_3999999d4000000_38427d4_9643
import RHInBoxT_1d4000000_3999999d4000000_9643_9679
import RHInBoxT_1d4000000_3999999d4000000_9679_9714
import RHInBoxT_1d4000000_3999999d4000000_9714_39001d4
import RHInBoxT_1d4000000_3999999d4000000_9750_9786
import RHInBoxT_1d4000000_3999999d4000000_9786_9821
import RHInBoxT_1d4000000_3999999d4000000_9821_9857
import RHInBoxT_1d4000000_3999999d4000000_9857_9893
import RHInBoxT_1d4000000_3999999d4000000_9893_9929
import RHInBoxT_1d4000000_3999999d4000000_9929_9964
import RHInBoxT_1d4000000_3999999d4000000_9964_40001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h10000

/-- The 28-band NOMINAL partition of `[9000, 10000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 9000
  | 1 => 9036
  | 2 => 9071
  | 3 => 9107
  | 4 => 9143
  | 5 => 9179
  | 6 => 9214
  | 7 => 9250
  | 8 => 9286
  | 9 => 9321
  | 10 => 9357
  | 11 => 9393
  | 12 => 9429
  | 13 => 9464
  | 14 => 9500
  | 15 => 9536
  | 16 => 9571
  | 17 => 9607
  | 18 => 9643
  | 19 => 9679
  | 20 => 9714
  | 21 => 9750
  | 22 => 9786
  | 23 => 9821
  | 24 => 9857
  | 25 => 9893
  | 26 => 9929
  | 27 => 9964
  | 28 => 10000
  | _ => 10000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((9000:ℝ)) ≤ (9036); norm_num
  · show ((9036:ℝ)) ≤ (9071); norm_num
  · show ((9071:ℝ)) ≤ (9107); norm_num
  · show ((9107:ℝ)) ≤ (9143); norm_num
  · show ((9143:ℝ)) ≤ (9179); norm_num
  · show ((9179:ℝ)) ≤ (9214); norm_num
  · show ((9214:ℝ)) ≤ (9250); norm_num
  · show ((9250:ℝ)) ≤ (9286); norm_num
  · show ((9286:ℝ)) ≤ (9321); norm_num
  · show ((9321:ℝ)) ≤ (9357); norm_num
  · show ((9357:ℝ)) ≤ (9393); norm_num
  · show ((9393:ℝ)) ≤ (9429); norm_num
  · show ((9429:ℝ)) ≤ (9464); norm_num
  · show ((9464:ℝ)) ≤ (9500); norm_num
  · show ((9500:ℝ)) ≤ (9536); norm_num
  · show ((9536:ℝ)) ≤ (9571); norm_num
  · show ((9571:ℝ)) ≤ (9607); norm_num
  · show ((9607:ℝ)) ≤ (9643); norm_num
  · show ((9643:ℝ)) ≤ (9679); norm_num
  · show ((9679:ℝ)) ≤ (9714); norm_num
  · show ((9714:ℝ)) ≤ (9750); norm_num
  · show ((9750:ℝ)) ≤ (9786); norm_num
  · show ((9786:ℝ)) ≤ (9821); norm_num
  · show ((9821:ℝ)) ≤ (9857); norm_num
  · show ((9857:ℝ)) ≤ (9893); norm_num
  · show ((9893:ℝ)) ≤ (9929); norm_num
  · show ((9929:ℝ)) ≤ (9964); norm_num
  · show ((9964:ℝ)) ≤ (10000); norm_num
  · show ((10000:ℝ)) ≤ (10000); norm_num
  · exact le_refl _

/-- The lower edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 9000
  | 1 => 9036
  | 2 => 9071
  | 3 => 9107
  | 4 => 9143
  | 5 => 9179
  | 6 => 36855 / 4
  | 7 => 9250
  | 8 => 9286
  | 9 => 9321
  | 10 => 9357
  | 11 => 37571 / 4
  | 12 => 9429
  | 13 => 9464
  | 14 => 9500
  | 15 => 9536
  | 16 => 9571
  | 17 => 38427 / 4
  | 18 => 9643
  | 19 => 9679
  | 20 => 9714
  | 21 => 9750
  | 22 => 9786
  | 23 => 9821
  | 24 => 9857
  | 25 => 9893
  | 26 => 9929
  | 27 => 9964
  | _ => 9964

/-- The upper edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 9036
  | 1 => 9071
  | 2 => 9107
  | 3 => 9143
  | 4 => 9179
  | 5 => 9214
  | 6 => 9250
  | 7 => 9286
  | 8 => 9321
  | 9 => 9357
  | 10 => 9393
  | 11 => 9429
  | 12 => 9464
  | 13 => 9500
  | 14 => 9536
  | 15 => 9571
  | 16 => 9607
  | 17 => 9643
  | 18 => 9679
  | 19 => 9714
  | 20 => 39001 / 4
  | 21 => 9786
  | 22 => 9821
  | 23 => 9857
  | 24 => 9893
  | 25 => 9929
  | 26 => 9964
  | 27 => 40001 / 4
  | _ => 40001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 28 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 10000` (`log 10000 ≤ 10`, `2.7^10 ≥ 10000`). -/
theorem haC_10000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 10000 := by
  have hlog : Real.log 10000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 10000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 10000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[9000, 10000]` segment's band hypothesis: every band `i < 28` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 28 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 28 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[9000, 10000]` SEGMENT: every zero with `9000 ≤ Im ≤ 10000` is on the line. -/
theorem segment_9000_10000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 10000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (9000:ℝ) ≤ ρ.im → ρ.im ≤ 10000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 9000 10000 bndSeg 28 (by norm_num) bndSeg_mono rfl rfl haC_10000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 10000 via the HEIGHT CHAIN**: `[0,9000]` ∘ `[9000,10000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_10000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands_6000 : AllZeros_h6000.BandHyp)
    (hbands_7000 : AllZeros_h7000.BandHyp)
    (hbands_8000 : AllZeros_h8000.BandHyp)
    (hbands_9000 : AllZeros_h9000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 10000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 10000 → ρ.re = 1 / 2 := by
  have hγ9000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 9000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 9000 10000
    (AllZeros_h9000.all_nontrivial_zeros_up_to_height_9000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hbands_6000
      hbands_7000
      hbands_8000
      hbands_9000
      hγ9000)
    (segment_9000_10000 hbands hγ)

end AllZeros_h10000
