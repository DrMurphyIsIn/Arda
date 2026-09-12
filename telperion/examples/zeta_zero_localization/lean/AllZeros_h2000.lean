/-  Height-chain step: all nontrivial zeta zeros up to height 2000 on Re = 1/2 --
    `AllZeros_h1000` + a `[1000, 2000]` SEGMENT certificate (25 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
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

/-- The 25-band NOMINAL partition of `[1000, 2000]`. -/
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

/-- The lower edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 1000
  | 1 => 1040
  | 2 => 1080
  | 3 => 1120
  | 4 => 1160
  | 5 => 1200
  | 6 => 1240
  | 7 => 1280
  | 8 => 5279 / 4
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
  | 23 => 7679 / 4
  | 24 => 1960
  | _ => 1960

/-- The upper edges of the 25 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 1040
  | 1 => 1080
  | 2 => 1120
  | 3 => 1160
  | 4 => 1200
  | 5 => 1240
  | 6 => 1280
  | 7 => 1320
  | 8 => 1360
  | 9 => 1400
  | 10 => 1440
  | 11 => 1480
  | 12 => 1520
  | 13 => 1560
  | 14 => 6401 / 4
  | 15 => 1640
  | 16 => 6721 / 4
  | 17 => 1720
  | 18 => 1760
  | 19 => 7201 / 4
  | 20 => 1840
  | 21 => 1880
  | 22 => 1920
  | 23 => 1960
  | 24 => 2000
  | _ => 2000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 25 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

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

/-- The `[1000, 2000]` segment's band hypothesis: every band `i < 25` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 25 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 25 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[1000, 2000]` SEGMENT: every zero with `1000 ≤ Im ≤ 2000` is on the line. -/
theorem segment_1000_2000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (1000:ℝ) ≤ ρ.im → ρ.im ≤ 2000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 1000 2000 bndSeg 25 (by norm_num) bndSeg_mono rfl rfl haC_2000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 2000 via the HEIGHT CHAIN**: `[0,1000]` ∘ `[1000,2000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_2000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → ρ.re = 1 / 2 := by
  have hγ1000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 1000 2000
    (AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands
      hbands_1000
      hγ1000)
    (segment_1000_2000 hbands hγ)

end AllZeros_h2000
