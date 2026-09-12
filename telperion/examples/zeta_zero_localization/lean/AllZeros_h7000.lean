/-  Height-chain step: all nontrivial zeta zeros up to height 7000 on Re = 1/2 --
    `AllZeros_h6000` + a `[6000, 7000]` SEGMENT certificate (26 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h6000
import RHInBoxT_1d4000000_3999999d4000000_6000_6038
import RHInBoxT_1d4000000_3999999d4000000_6038_6077
import RHInBoxT_1d4000000_3999999d4000000_6077_6115
import RHInBoxT_1d4000000_3999999d4000000_6115_6154
import RHInBoxT_1d4000000_3999999d4000000_6154_6192
import RHInBoxT_1d4000000_3999999d4000000_6192_6231
import RHInBoxT_1d4000000_3999999d4000000_6231_6269
import RHInBoxT_1d4000000_3999999d4000000_6269_6308
import RHInBoxT_1d4000000_3999999d4000000_6308_6346
import RHInBoxT_1d4000000_3999999d4000000_6346_6385
import RHInBoxT_1d4000000_3999999d4000000_25539d4_6423
import RHInBoxT_1d4000000_3999999d4000000_6423_6462
import RHInBoxT_1d4000000_3999999d4000000_6462_26001d4
import RHInBoxT_1d4000000_3999999d4000000_6500_6538
import RHInBoxT_1d4000000_3999999d4000000_6538_6577
import RHInBoxT_1d4000000_3999999d4000000_6577_6615
import RHInBoxT_1d4000000_3999999d4000000_6615_6654
import RHInBoxT_1d4000000_3999999d4000000_26615d4_6692
import RHInBoxT_1d4000000_3999999d4000000_6692_6731
import RHInBoxT_1d4000000_3999999d4000000_26923d4_6769
import RHInBoxT_1d4000000_3999999d4000000_6769_6808
import RHInBoxT_1d4000000_3999999d4000000_6808_6846
import RHInBoxT_1d4000000_3999999d4000000_6846_6885
import RHInBoxT_1d4000000_3999999d4000000_6885_6923
import RHInBoxT_1d4000000_3999999d4000000_6923_6962
import RHInBoxT_1d4000000_3999999d4000000_6962_7000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h7000

/-- The 26-band NOMINAL partition of `[6000, 7000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 6000
  | 1 => 6038
  | 2 => 6077
  | 3 => 6115
  | 4 => 6154
  | 5 => 6192
  | 6 => 6231
  | 7 => 6269
  | 8 => 6308
  | 9 => 6346
  | 10 => 6385
  | 11 => 6423
  | 12 => 6462
  | 13 => 6500
  | 14 => 6538
  | 15 => 6577
  | 16 => 6615
  | 17 => 6654
  | 18 => 6692
  | 19 => 6731
  | 20 => 6769
  | 21 => 6808
  | 22 => 6846
  | 23 => 6885
  | 24 => 6923
  | 25 => 6962
  | 26 => 7000
  | _ => 7000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((6000:ℝ)) ≤ (6038); norm_num
  · show ((6038:ℝ)) ≤ (6077); norm_num
  · show ((6077:ℝ)) ≤ (6115); norm_num
  · show ((6115:ℝ)) ≤ (6154); norm_num
  · show ((6154:ℝ)) ≤ (6192); norm_num
  · show ((6192:ℝ)) ≤ (6231); norm_num
  · show ((6231:ℝ)) ≤ (6269); norm_num
  · show ((6269:ℝ)) ≤ (6308); norm_num
  · show ((6308:ℝ)) ≤ (6346); norm_num
  · show ((6346:ℝ)) ≤ (6385); norm_num
  · show ((6385:ℝ)) ≤ (6423); norm_num
  · show ((6423:ℝ)) ≤ (6462); norm_num
  · show ((6462:ℝ)) ≤ (6500); norm_num
  · show ((6500:ℝ)) ≤ (6538); norm_num
  · show ((6538:ℝ)) ≤ (6577); norm_num
  · show ((6577:ℝ)) ≤ (6615); norm_num
  · show ((6615:ℝ)) ≤ (6654); norm_num
  · show ((6654:ℝ)) ≤ (6692); norm_num
  · show ((6692:ℝ)) ≤ (6731); norm_num
  · show ((6731:ℝ)) ≤ (6769); norm_num
  · show ((6769:ℝ)) ≤ (6808); norm_num
  · show ((6808:ℝ)) ≤ (6846); norm_num
  · show ((6846:ℝ)) ≤ (6885); norm_num
  · show ((6885:ℝ)) ≤ (6923); norm_num
  · show ((6923:ℝ)) ≤ (6962); norm_num
  · show ((6962:ℝ)) ≤ (7000); norm_num
  · show ((7000:ℝ)) ≤ (7000); norm_num
  · exact le_refl _

/-- The lower edges of the 26 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 6000
  | 1 => 6038
  | 2 => 6077
  | 3 => 6115
  | 4 => 6154
  | 5 => 6192
  | 6 => 6231
  | 7 => 6269
  | 8 => 6308
  | 9 => 6346
  | 10 => 25539 / 4
  | 11 => 6423
  | 12 => 6462
  | 13 => 6500
  | 14 => 6538
  | 15 => 6577
  | 16 => 6615
  | 17 => 26615 / 4
  | 18 => 6692
  | 19 => 26923 / 4
  | 20 => 6769
  | 21 => 6808
  | 22 => 6846
  | 23 => 6885
  | 24 => 6923
  | 25 => 6962
  | _ => 6962

/-- The upper edges of the 26 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 6038
  | 1 => 6077
  | 2 => 6115
  | 3 => 6154
  | 4 => 6192
  | 5 => 6231
  | 6 => 6269
  | 7 => 6308
  | 8 => 6346
  | 9 => 6385
  | 10 => 6423
  | 11 => 6462
  | 12 => 26001 / 4
  | 13 => 6538
  | 14 => 6577
  | 15 => 6615
  | 16 => 6654
  | 17 => 6692
  | 18 => 6731
  | 19 => 6769
  | 20 => 6808
  | 21 => 6846
  | 22 => 6885
  | 23 => 6923
  | 24 => 6962
  | 25 => 7000
  | _ => 7000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 26 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 7000` (`log 7000 ≤ 9`, `2.7^9 ≥ 7000`). -/
theorem haC_7000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 7000 := by
  have hlog : Real.log 7000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h9 : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 := pow_le_pow_left₀ (by norm_num) he1 9
    rw [h9]; nlinarith [hpow]
  have hpos : 0 < Real.log 7000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 7000
      ≤ (1 / 4000000) * 9 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[6000, 7000]` segment's band hypothesis: every band `i < 26` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 26 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 26 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[6000, 7000]` SEGMENT: every zero with `6000 ≤ Im ≤ 7000` is on the line. -/
theorem segment_6000_7000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 7000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (6000:ℝ) ≤ ρ.im → ρ.im ≤ 7000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 6000 7000 bndSeg 26 (by norm_num) bndSeg_mono rfl rfl haC_7000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 7000 via the HEIGHT CHAIN**: `[0,6000]` ∘ `[6000,7000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_7000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands_6000 : AllZeros_h6000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 7000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 7000 → ρ.re = 1 / 2 := by
  have hγ6000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 6000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 6000 7000
    (AllZeros_h6000.all_nontrivial_zeros_up_to_height_6000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hbands_6000
      hγ6000)
    (segment_6000_7000 hbands hγ)

end AllZeros_h7000
