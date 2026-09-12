/-  Height-chain step: all nontrivial zeta zeros up to height 16000 on Re = 1/2 --
    `AllZeros_h15000` + a `[15000, 16000]` SEGMENT certificate (30 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h15000
import RHInBoxT_1d4000000_3999999d4000000_15000_15033
import RHInBoxT_1d4000000_3999999d4000000_15033_15067
import RHInBoxT_1d4000000_3999999d4000000_15067_15100
import RHInBoxT_1d4000000_3999999d4000000_15100_15133
import RHInBoxT_1d4000000_3999999d4000000_15133_15167
import RHInBoxT_1d4000000_3999999d4000000_60667d4_15200
import RHInBoxT_1d4000000_3999999d4000000_15200_15233
import RHInBoxT_1d4000000_3999999d4000000_15233_15267
import RHInBoxT_1d4000000_3999999d4000000_61067d4_15300
import RHInBoxT_1d4000000_3999999d4000000_15300_15333
import RHInBoxT_1d4000000_3999999d4000000_15333_15367
import RHInBoxT_1d4000000_3999999d4000000_15367_15400
import RHInBoxT_1d4000000_3999999d4000000_61599d4_15433
import RHInBoxT_1d4000000_3999999d4000000_15433_15467
import RHInBoxT_1d4000000_3999999d4000000_15467_15500
import RHInBoxT_1d4000000_3999999d4000000_15500_15533
import RHInBoxT_1d4000000_3999999d4000000_62131d4_15567
import RHInBoxT_1d4000000_3999999d4000000_15567_15600
import RHInBoxT_1d4000000_3999999d4000000_15600_62533d4
import RHInBoxT_1d4000000_3999999d4000000_15633_15667
import RHInBoxT_1d4000000_3999999d4000000_15667_15700
import RHInBoxT_1d4000000_3999999d4000000_15700_15733
import RHInBoxT_1d4000000_3999999d4000000_62931d4_15767
import RHInBoxT_1d4000000_3999999d4000000_15767_63201d4
import RHInBoxT_1d4000000_3999999d4000000_15800_15833
import RHInBoxT_1d4000000_3999999d4000000_15833_15867
import RHInBoxT_1d4000000_3999999d4000000_15867_15900
import RHInBoxT_1d4000000_3999999d4000000_15900_15933
import RHInBoxT_1d4000000_3999999d4000000_15933_15967
import RHInBoxT_1d4000000_3999999d4000000_15967_16000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h16000

/-- The 30-band NOMINAL partition of `[15000, 16000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 15000
  | 1 => 15033
  | 2 => 15067
  | 3 => 15100
  | 4 => 15133
  | 5 => 15167
  | 6 => 15200
  | 7 => 15233
  | 8 => 15267
  | 9 => 15300
  | 10 => 15333
  | 11 => 15367
  | 12 => 15400
  | 13 => 15433
  | 14 => 15467
  | 15 => 15500
  | 16 => 15533
  | 17 => 15567
  | 18 => 15600
  | 19 => 15633
  | 20 => 15667
  | 21 => 15700
  | 22 => 15733
  | 23 => 15767
  | 24 => 15800
  | 25 => 15833
  | 26 => 15867
  | 27 => 15900
  | 28 => 15933
  | 29 => 15967
  | 30 => 16000
  | _ => 16000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((15000:ℝ)) ≤ (15033); norm_num
  · show ((15033:ℝ)) ≤ (15067); norm_num
  · show ((15067:ℝ)) ≤ (15100); norm_num
  · show ((15100:ℝ)) ≤ (15133); norm_num
  · show ((15133:ℝ)) ≤ (15167); norm_num
  · show ((15167:ℝ)) ≤ (15200); norm_num
  · show ((15200:ℝ)) ≤ (15233); norm_num
  · show ((15233:ℝ)) ≤ (15267); norm_num
  · show ((15267:ℝ)) ≤ (15300); norm_num
  · show ((15300:ℝ)) ≤ (15333); norm_num
  · show ((15333:ℝ)) ≤ (15367); norm_num
  · show ((15367:ℝ)) ≤ (15400); norm_num
  · show ((15400:ℝ)) ≤ (15433); norm_num
  · show ((15433:ℝ)) ≤ (15467); norm_num
  · show ((15467:ℝ)) ≤ (15500); norm_num
  · show ((15500:ℝ)) ≤ (15533); norm_num
  · show ((15533:ℝ)) ≤ (15567); norm_num
  · show ((15567:ℝ)) ≤ (15600); norm_num
  · show ((15600:ℝ)) ≤ (15633); norm_num
  · show ((15633:ℝ)) ≤ (15667); norm_num
  · show ((15667:ℝ)) ≤ (15700); norm_num
  · show ((15700:ℝ)) ≤ (15733); norm_num
  · show ((15733:ℝ)) ≤ (15767); norm_num
  · show ((15767:ℝ)) ≤ (15800); norm_num
  · show ((15800:ℝ)) ≤ (15833); norm_num
  · show ((15833:ℝ)) ≤ (15867); norm_num
  · show ((15867:ℝ)) ≤ (15900); norm_num
  · show ((15900:ℝ)) ≤ (15933); norm_num
  · show ((15933:ℝ)) ≤ (15967); norm_num
  · show ((15967:ℝ)) ≤ (16000); norm_num
  · show ((16000:ℝ)) ≤ (16000); norm_num
  · exact le_refl _

/-- The lower edges of the 30 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 15000
  | 1 => 15033
  | 2 => 15067
  | 3 => 15100
  | 4 => 15133
  | 5 => 60667 / 4
  | 6 => 15200
  | 7 => 15233
  | 8 => 61067 / 4
  | 9 => 15300
  | 10 => 15333
  | 11 => 15367
  | 12 => 61599 / 4
  | 13 => 15433
  | 14 => 15467
  | 15 => 15500
  | 16 => 62131 / 4
  | 17 => 15567
  | 18 => 15600
  | 19 => 15633
  | 20 => 15667
  | 21 => 15700
  | 22 => 62931 / 4
  | 23 => 15767
  | 24 => 15800
  | 25 => 15833
  | 26 => 15867
  | 27 => 15900
  | 28 => 15933
  | 29 => 15967
  | _ => 15967

/-- The upper edges of the 30 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 15033
  | 1 => 15067
  | 2 => 15100
  | 3 => 15133
  | 4 => 15167
  | 5 => 15200
  | 6 => 15233
  | 7 => 15267
  | 8 => 15300
  | 9 => 15333
  | 10 => 15367
  | 11 => 15400
  | 12 => 15433
  | 13 => 15467
  | 14 => 15500
  | 15 => 15533
  | 16 => 15567
  | 17 => 15600
  | 18 => 62533 / 4
  | 19 => 15667
  | 20 => 15700
  | 21 => 15733
  | 22 => 15767
  | 23 => 63201 / 4
  | 24 => 15833
  | 25 => 15867
  | 26 => 15900
  | 27 => 15933
  | 28 => 15967
  | 29 => 16000
  | _ => 16000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 30 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 16000` (`log 16000 ≤ 10`, `2.7^10 ≥ 16000`). -/
theorem haC_16000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 16000 := by
  have hlog : Real.log 16000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 16000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 16000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[15000, 16000]` segment's band hypothesis: every band `i < 30` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 30 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 30 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[15000, 16000]` SEGMENT: every zero with `15000 ≤ Im ≤ 16000` is on the line. -/
theorem segment_15000_16000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 16000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (15000:ℝ) ≤ ρ.im → ρ.im ≤ 16000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 15000 16000 bndSeg 30 (by norm_num) bndSeg_mono rfl rfl haC_16000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 16000 via the HEIGHT CHAIN**: `[0,15000]` ∘ `[15000,16000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_16000_of_bands
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
    (hbands_13000 : AllZeros_h13000.BandHyp)
    (hbands_14000 : AllZeros_h14000.BandHyp)
    (hbands_15000 : AllZeros_h15000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 16000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 16000 → ρ.re = 1 / 2 := by
  have hγ15000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 15000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 15000 16000
    (AllZeros_h15000.all_nontrivial_zeros_up_to_height_15000_of_bands
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
      hbands_13000
      hbands_14000
      hbands_15000
      hγ15000)
    (segment_15000_16000 hbands hγ)

end AllZeros_h16000
