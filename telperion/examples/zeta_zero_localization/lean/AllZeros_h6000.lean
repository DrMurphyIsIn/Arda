/-  Height-chain step: all nontrivial zeta zeros up to height 6000 on Re = 1/2 --
    `AllZeros_h5000` + a `[5000, 6000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h5000
import RHInBoxT_1d4000000_3999999d4000000_5000_5040
import RHInBoxT_1d4000000_3999999d4000000_5040_5080
import RHInBoxT_1d4000000_3999999d4000000_5080_5120
import RHInBoxT_1d4000000_3999999d4000000_5120_20641d4
import RHInBoxT_1d4000000_3999999d4000000_5160_5200
import RHInBoxT_1d4000000_3999999d4000000_5200_5240
import RHInBoxT_1d4000000_3999999d4000000_5240_5280
import RHInBoxT_1d4000000_3999999d4000000_5280_5320
import RHInBoxT_1d4000000_3999999d4000000_5320_5360
import RHInBoxT_1d4000000_3999999d4000000_5360_5400
import RHInBoxT_1d4000000_3999999d4000000_5400_5440
import RHInBoxT_1d4000000_3999999d4000000_5440_5480
import RHInBoxT_1d4000000_3999999d4000000_5480_5520
import RHInBoxT_1d4000000_3999999d4000000_5520_5560
import RHInBoxT_1d4000000_3999999d4000000_5560_5600
import RHInBoxT_1d4000000_3999999d4000000_5600_5640
import RHInBoxT_1d4000000_3999999d4000000_5640_5680
import RHInBoxT_1d4000000_3999999d4000000_5680_5720
import RHInBoxT_1d4000000_3999999d4000000_5720_5760
import RHInBoxT_1d4000000_3999999d4000000_5760_23201d4
import RHInBoxT_1d4000000_3999999d4000000_5800_5840
import RHInBoxT_1d4000000_3999999d4000000_5840_5880
import RHInBoxT_1d4000000_3999999d4000000_5880_23681d4
import RHInBoxT_1d4000000_3999999d4000000_5920_5960
import RHInBoxT_1d4000000_3999999d4000000_5960_6000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h6000

/-- The 25-band NOMINAL partition of `[5000, 6000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 5000
  | 1 => 5040
  | 2 => 5080
  | 3 => 5120
  | 4 => 5160
  | 5 => 5200
  | 6 => 5240
  | 7 => 5280
  | 8 => 5320
  | 9 => 5360
  | 10 => 5400
  | 11 => 5440
  | 12 => 5480
  | 13 => 5520
  | 14 => 5560
  | 15 => 5600
  | 16 => 5640
  | 17 => 5680
  | 18 => 5720
  | 19 => 5760
  | 20 => 5800
  | 21 => 5840
  | 22 => 5880
  | 23 => 5920
  | 24 => 5960
  | 25 => 6000
  | _ => 6000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((5000:ℝ)) ≤ (5040); norm_num
  · show ((5040:ℝ)) ≤ (5080); norm_num
  · show ((5080:ℝ)) ≤ (5120); norm_num
  · show ((5120:ℝ)) ≤ (5160); norm_num
  · show ((5160:ℝ)) ≤ (5200); norm_num
  · show ((5200:ℝ)) ≤ (5240); norm_num
  · show ((5240:ℝ)) ≤ (5280); norm_num
  · show ((5280:ℝ)) ≤ (5320); norm_num
  · show ((5320:ℝ)) ≤ (5360); norm_num
  · show ((5360:ℝ)) ≤ (5400); norm_num
  · show ((5400:ℝ)) ≤ (5440); norm_num
  · show ((5440:ℝ)) ≤ (5480); norm_num
  · show ((5480:ℝ)) ≤ (5520); norm_num
  · show ((5520:ℝ)) ≤ (5560); norm_num
  · show ((5560:ℝ)) ≤ (5600); norm_num
  · show ((5600:ℝ)) ≤ (5640); norm_num
  · show ((5640:ℝ)) ≤ (5680); norm_num
  · show ((5680:ℝ)) ≤ (5720); norm_num
  · show ((5720:ℝ)) ≤ (5760); norm_num
  · show ((5760:ℝ)) ≤ (5800); norm_num
  · show ((5800:ℝ)) ≤ (5840); norm_num
  · show ((5840:ℝ)) ≤ (5880); norm_num
  · show ((5880:ℝ)) ≤ (5920); norm_num
  · show ((5920:ℝ)) ≤ (5960); norm_num
  · show ((5960:ℝ)) ≤ (6000); norm_num
  · show ((6000:ℝ)) ≤ (6000); norm_num
  · exact le_refl _

/-- The lower edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 5000
  | 1 => 5040
  | 2 => 5080
  | 3 => 5120
  | 4 => 5160
  | 5 => 5200
  | 6 => 5240
  | 7 => 5280
  | 8 => 5320
  | 9 => 5360
  | 10 => 5400
  | 11 => 5440
  | 12 => 5480
  | 13 => 5520
  | 14 => 5560
  | 15 => 5600
  | 16 => 5640
  | 17 => 5680
  | 18 => 5720
  | 19 => 5760
  | 20 => 5800
  | 21 => 5840
  | 22 => 5880
  | 23 => 5920
  | 24 => 5960
  | _ => 5960

/-- The upper edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 5040
  | 1 => 5080
  | 2 => 5120
  | 3 => 20641 / 4
  | 4 => 5200
  | 5 => 5240
  | 6 => 5280
  | 7 => 5320
  | 8 => 5360
  | 9 => 5400
  | 10 => 5440
  | 11 => 5480
  | 12 => 5520
  | 13 => 5560
  | 14 => 5600
  | 15 => 5640
  | 16 => 5680
  | 17 => 5720
  | 18 => 5760
  | 19 => 23201 / 4
  | 20 => 5840
  | 21 => 5880
  | 22 => 23681 / 4
  | 23 => 5960
  | 24 => 6000
  | _ => 6000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 25 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 6000` (`log 6000 ≤ 9`, `2.7^9 ≥ 6000`). -/
theorem haC_6000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 6000 := by
  have hlog : Real.log 6000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h9 : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 := pow_le_pow_left₀ (by norm_num) he1 9
    rw [h9]; nlinarith [hpow]
  have hpos : 0 < Real.log 6000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 6000
      ≤ (1 / 4000000) * 9 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[5000, 6000]` segment's band hypothesis: every band `i < 25` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 25 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 25 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[5000, 6000]` SEGMENT: every zero with `5000 ≤ Im ≤ 6000` is on the line. -/
theorem segment_5000_6000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 6000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (5000:ℝ) ≤ ρ.im → ρ.im ≤ 6000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 5000 6000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_6000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 6000 via the HEIGHT CHAIN**: `[0,5000]` ∘ `[5000,6000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_6000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 6000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 6000 → ρ.re = 1 / 2 := by
  have hγ5000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 5000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 5000 6000
    (AllZeros_h5000.all_nontrivial_zeros_up_to_height_5000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hγ5000)
    (segment_5000_6000 hbands hγ)

end AllZeros_h6000
