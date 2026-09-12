/-  Height-chain step: all nontrivial zeta zeros up to height 12000 on Re = 1/2 --
    `AllZeros_h11000` + a `[11000, 12000]` SEGMENT certificate (28 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h11000
import RHInBoxT_1d4000000_3999999d4000000_11000_11036
import RHInBoxT_1d4000000_3999999d4000000_11036_11071
import RHInBoxT_1d4000000_3999999d4000000_11071_11107
import RHInBoxT_1d4000000_3999999d4000000_11107_11143
import RHInBoxT_1d4000000_3999999d4000000_11143_11179
import RHInBoxT_1d4000000_3999999d4000000_11179_11214
import RHInBoxT_1d4000000_3999999d4000000_11214_11250
import RHInBoxT_1d4000000_3999999d4000000_11250_11286
import RHInBoxT_1d4000000_3999999d4000000_11286_11321
import RHInBoxT_1d4000000_3999999d4000000_45283d4_11357
import RHInBoxT_1d4000000_3999999d4000000_11357_11393
import RHInBoxT_1d4000000_3999999d4000000_11393_11429
import RHInBoxT_1d4000000_3999999d4000000_11429_11464
import RHInBoxT_1d4000000_3999999d4000000_11464_11500
import RHInBoxT_1d4000000_3999999d4000000_11500_11536
import RHInBoxT_1d4000000_3999999d4000000_11536_11571
import RHInBoxT_1d4000000_3999999d4000000_11571_11607
import RHInBoxT_1d4000000_3999999d4000000_11607_11643
import RHInBoxT_1d4000000_3999999d4000000_11643_11679
import RHInBoxT_1d4000000_3999999d4000000_11679_11714
import RHInBoxT_1d4000000_3999999d4000000_11714_11750
import RHInBoxT_1d4000000_3999999d4000000_11750_11786
import RHInBoxT_1d4000000_3999999d4000000_11786_11821
import RHInBoxT_1d4000000_3999999d4000000_11821_11857
import RHInBoxT_1d4000000_3999999d4000000_11857_11893
import RHInBoxT_1d4000000_3999999d4000000_11893_11929
import RHInBoxT_1d4000000_3999999d4000000_11929_11964
import RHInBoxT_1d4000000_3999999d4000000_11964_24001d2

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h12000

/-- The 28-band NOMINAL partition of `[11000, 12000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 11000
  | 1 => 11036
  | 2 => 11071
  | 3 => 11107
  | 4 => 11143
  | 5 => 11179
  | 6 => 11214
  | 7 => 11250
  | 8 => 11286
  | 9 => 11321
  | 10 => 11357
  | 11 => 11393
  | 12 => 11429
  | 13 => 11464
  | 14 => 11500
  | 15 => 11536
  | 16 => 11571
  | 17 => 11607
  | 18 => 11643
  | 19 => 11679
  | 20 => 11714
  | 21 => 11750
  | 22 => 11786
  | 23 => 11821
  | 24 => 11857
  | 25 => 11893
  | 26 => 11929
  | 27 => 11964
  | 28 => 12000
  | _ => 12000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((11000:ℝ)) ≤ (11036); norm_num
  · show ((11036:ℝ)) ≤ (11071); norm_num
  · show ((11071:ℝ)) ≤ (11107); norm_num
  · show ((11107:ℝ)) ≤ (11143); norm_num
  · show ((11143:ℝ)) ≤ (11179); norm_num
  · show ((11179:ℝ)) ≤ (11214); norm_num
  · show ((11214:ℝ)) ≤ (11250); norm_num
  · show ((11250:ℝ)) ≤ (11286); norm_num
  · show ((11286:ℝ)) ≤ (11321); norm_num
  · show ((11321:ℝ)) ≤ (11357); norm_num
  · show ((11357:ℝ)) ≤ (11393); norm_num
  · show ((11393:ℝ)) ≤ (11429); norm_num
  · show ((11429:ℝ)) ≤ (11464); norm_num
  · show ((11464:ℝ)) ≤ (11500); norm_num
  · show ((11500:ℝ)) ≤ (11536); norm_num
  · show ((11536:ℝ)) ≤ (11571); norm_num
  · show ((11571:ℝ)) ≤ (11607); norm_num
  · show ((11607:ℝ)) ≤ (11643); norm_num
  · show ((11643:ℝ)) ≤ (11679); norm_num
  · show ((11679:ℝ)) ≤ (11714); norm_num
  · show ((11714:ℝ)) ≤ (11750); norm_num
  · show ((11750:ℝ)) ≤ (11786); norm_num
  · show ((11786:ℝ)) ≤ (11821); norm_num
  · show ((11821:ℝ)) ≤ (11857); norm_num
  · show ((11857:ℝ)) ≤ (11893); norm_num
  · show ((11893:ℝ)) ≤ (11929); norm_num
  · show ((11929:ℝ)) ≤ (11964); norm_num
  · show ((11964:ℝ)) ≤ (12000); norm_num
  · show ((12000:ℝ)) ≤ (12000); norm_num
  · exact le_refl _

/-- The lower edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 11000
  | 1 => 11036
  | 2 => 11071
  | 3 => 11107
  | 4 => 11143
  | 5 => 11179
  | 6 => 11214
  | 7 => 11250
  | 8 => 11286
  | 9 => 45283 / 4
  | 10 => 11357
  | 11 => 11393
  | 12 => 11429
  | 13 => 11464
  | 14 => 11500
  | 15 => 11536
  | 16 => 11571
  | 17 => 11607
  | 18 => 11643
  | 19 => 11679
  | 20 => 11714
  | 21 => 11750
  | 22 => 11786
  | 23 => 11821
  | 24 => 11857
  | 25 => 11893
  | 26 => 11929
  | 27 => 11964
  | _ => 11964

/-- The upper edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 11036
  | 1 => 11071
  | 2 => 11107
  | 3 => 11143
  | 4 => 11179
  | 5 => 11214
  | 6 => 11250
  | 7 => 11286
  | 8 => 11321
  | 9 => 11357
  | 10 => 11393
  | 11 => 11429
  | 12 => 11464
  | 13 => 11500
  | 14 => 11536
  | 15 => 11571
  | 16 => 11607
  | 17 => 11643
  | 18 => 11679
  | 19 => 11714
  | 20 => 11750
  | 21 => 11786
  | 22 => 11821
  | 23 => 11857
  | 24 => 11893
  | 25 => 11929
  | 26 => 11964
  | 27 => 24001 / 2
  | _ => 24001 / 2

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 28 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 12000` (`log 12000 ≤ 10`, `2.7^10 ≥ 12000`). -/
theorem haC_12000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 12000 := by
  have hlog : Real.log 12000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 12000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 12000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[11000, 12000]` segment's band hypothesis: every band `i < 28` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 28 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 28 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[11000, 12000]` SEGMENT: every zero with `11000 ≤ Im ≤ 12000` is on the line. -/
theorem segment_11000_12000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 12000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (11000:ℝ) ≤ ρ.im → ρ.im ≤ 12000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 11000 12000 bndSeg 28 (by norm_num) bndSeg_mono rfl rfl haC_12000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 12000 via the HEIGHT CHAIN**: `[0,11000]` ∘ `[11000,12000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_12000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 12000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 12000 → ρ.re = 1 / 2 := by
  have hγ11000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 11000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 11000 12000
    (AllZeros_h11000.all_nontrivial_zeros_up_to_height_11000_of_bands
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
      hγ11000)
    (segment_11000_12000 hbands hγ)

end AllZeros_h12000
