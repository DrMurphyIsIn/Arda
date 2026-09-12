/-  Height-chain step: all nontrivial zeta zeros up to height 5000 on Re = 1/2 --
    `AllZeros_h4000` + a `[4000, 5000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
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

/-- The 25-band NOMINAL partition of `[4000, 5000]`. -/
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

/-- The lower edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 4000
  | 1 => 4040
  | 2 => 4080
  | 3 => 4120
  | 4 => 16639 / 4
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
  | _ => 4960

/-- The upper edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 4040
  | 1 => 4080
  | 2 => 4120
  | 3 => 4160
  | 4 => 4200
  | 5 => 4240
  | 6 => 4280
  | 7 => 4320
  | 8 => 4360
  | 9 => 4400
  | 10 => 4440
  | 11 => 4480
  | 12 => 4520
  | 13 => 4560
  | 14 => 4600
  | 15 => 4640
  | 16 => 4680
  | 17 => 4720
  | 18 => 4760
  | 19 => 4800
  | 20 => 4840
  | 21 => 19521 / 4
  | 22 => 4920
  | 23 => 4960
  | 24 => 5000
  | _ => 5000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 25 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

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

/-- The `[4000, 5000]` segment's band hypothesis: every band `i < 25` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 25 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 25 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[4000, 5000]` SEGMENT: every zero with `4000 ≤ Im ≤ 5000` is on the line. -/
theorem segment_4000_5000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 5000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (4000:ℝ) ≤ ρ.im → ρ.im ≤ 5000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 4000 5000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_5000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 5000 via the HEIGHT CHAIN**: `[0,4000]` ∘ `[4000,5000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_5000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 5000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 5000 → ρ.re = 1 / 2 := by
  have hγ4000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 4000 5000
    (AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hγ4000)
    (segment_4000_5000 hbands hγ)

end AllZeros_h5000
