/-  Height-chain step: all nontrivial zeta zeros up to height 3000 on Re = 1/2 --
    `AllZeros_h2000` + a `[2000, 3000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h2000
import RHInBoxT_1d4000000_3999999d4000000_2000_2040
import RHInBoxT_1d4000000_3999999d4000000_2040_2080
import RHInBoxT_1d4000000_3999999d4000000_2080_2120
import RHInBoxT_1d4000000_3999999d4000000_2120_2160
import RHInBoxT_1d4000000_3999999d4000000_2160_2200
import RHInBoxT_1d4000000_3999999d4000000_2200_8961d4
import RHInBoxT_1d4000000_3999999d4000000_2240_2280
import RHInBoxT_1d4000000_3999999d4000000_2280_2320
import RHInBoxT_1d4000000_3999999d4000000_2320_2360
import RHInBoxT_1d4000000_3999999d4000000_2360_2400
import RHInBoxT_1d4000000_3999999d4000000_2400_2440
import RHInBoxT_1d4000000_3999999d4000000_9759d4_2480
import RHInBoxT_1d4000000_3999999d4000000_9919d4_2520
import RHInBoxT_1d4000000_3999999d4000000_2520_2560
import RHInBoxT_1d4000000_3999999d4000000_2560_2600
import RHInBoxT_1d4000000_3999999d4000000_2600_10561d4
import RHInBoxT_1d4000000_3999999d4000000_2640_10721d4
import RHInBoxT_1d4000000_3999999d4000000_2680_2720
import RHInBoxT_1d4000000_3999999d4000000_2720_2760
import RHInBoxT_1d4000000_3999999d4000000_2760_11201d4
import RHInBoxT_1d4000000_3999999d4000000_2800_2840
import RHInBoxT_1d4000000_3999999d4000000_2840_2880
import RHInBoxT_1d4000000_3999999d4000000_2880_2920
import RHInBoxT_1d4000000_3999999d4000000_2920_11841d4
import RHInBoxT_1d4000000_3999999d4000000_2960_3000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h3000

/-- The 25-band NOMINAL partition of `[2000, 3000]`. -/
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
  | _ => 3000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
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
  · show ((3000:ℝ)) ≤ (3000); norm_num
  · exact le_refl _

/-- The lower edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
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
  | 11 => 9759 / 4
  | 12 => 9919 / 4
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
  | _ => 2960

/-- The upper edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 2040
  | 1 => 2080
  | 2 => 2120
  | 3 => 2160
  | 4 => 2200
  | 5 => 8961 / 4
  | 6 => 2280
  | 7 => 2320
  | 8 => 2360
  | 9 => 2400
  | 10 => 2440
  | 11 => 2480
  | 12 => 2520
  | 13 => 2560
  | 14 => 2600
  | 15 => 10561 / 4
  | 16 => 10721 / 4
  | 17 => 2720
  | 18 => 2760
  | 19 => 11201 / 4
  | 20 => 2840
  | 21 => 2880
  | 22 => 2920
  | 23 => 11841 / 4
  | 24 => 3000
  | _ => 3000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 25 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 3000` (`log 3000 ≤ 9`, `2.7^9 ≥ 3000`). -/
theorem haC_3000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 3000 := by
  have hlog : Real.log 3000 ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h9 : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 := pow_le_pow_left₀ (by norm_num) he1 9
    rw [h9]; nlinarith [hpow]
  have hpos : 0 < Real.log 3000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 3000
      ≤ (1 / 4000000) * 9 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[2000, 3000]` segment's band hypothesis: every band `i < 25` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 25 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 25 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[2000, 3000]` SEGMENT: every zero with `2000 ≤ Im ≤ 3000` is on the line. -/
theorem segment_2000_3000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 3000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (2000:ℝ) ≤ ρ.im → ρ.im ≤ 3000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 2000 3000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_3000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 3000 via the HEIGHT CHAIN**: `[0,2000]` ∘ `[2000,3000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_3000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 3000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 3000 → ρ.re = 1 / 2 := by
  have hγ2000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 2000 3000
    (AllZeros_h2000.all_nontrivial_zeros_up_to_height_2000_of_bands
      hbands_1000
      hbands_2000
      hγ2000)
    (segment_2000_3000 hbands hγ)

end AllZeros_h3000
