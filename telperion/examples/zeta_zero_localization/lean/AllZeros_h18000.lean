/-  Height-chain step: all nontrivial zeta zeros up to height 18000 on Re = 1/2 --
    `AllZeros_h17000` + a `[17000, 18000]` SEGMENT certificate (30 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h17000
import RHInBoxT_1d4000000_3999999d4000000_17000_17033
import RHInBoxT_1d4000000_3999999d4000000_17033_17067
import RHInBoxT_1d4000000_3999999d4000000_68267d4_17100
import RHInBoxT_1d4000000_3999999d4000000_17100_68533d4
import RHInBoxT_1d4000000_3999999d4000000_17133_17167
import RHInBoxT_1d4000000_3999999d4000000_17167_17200
import RHInBoxT_1d4000000_3999999d4000000_17200_17233
import RHInBoxT_1d4000000_3999999d4000000_17233_17267
import RHInBoxT_1d4000000_3999999d4000000_17267_17300
import RHInBoxT_1d4000000_3999999d4000000_17300_17333
import RHInBoxT_1d4000000_3999999d4000000_69331d4_17367
import RHInBoxT_1d4000000_3999999d4000000_17367_17400
import RHInBoxT_1d4000000_3999999d4000000_17400_17433
import RHInBoxT_1d4000000_3999999d4000000_17433_17467
import RHInBoxT_1d4000000_3999999d4000000_17467_17500
import RHInBoxT_1d4000000_3999999d4000000_17500_17533
import RHInBoxT_1d4000000_3999999d4000000_17533_17567
import RHInBoxT_1d4000000_3999999d4000000_17567_17600
import RHInBoxT_1d4000000_3999999d4000000_70399d4_17633
import RHInBoxT_1d4000000_3999999d4000000_17633_17667
import RHInBoxT_1d4000000_3999999d4000000_17667_70801d4
import RHInBoxT_1d4000000_3999999d4000000_17700_17733
import RHInBoxT_1d4000000_3999999d4000000_17733_17767
import RHInBoxT_1d4000000_3999999d4000000_71067d4_17800
import RHInBoxT_1d4000000_3999999d4000000_17800_17833
import RHInBoxT_1d4000000_3999999d4000000_17833_17867
import RHInBoxT_1d4000000_3999999d4000000_17867_17900
import RHInBoxT_1d4000000_3999999d4000000_17900_17933
import RHInBoxT_1d4000000_3999999d4000000_17933_71869d4
import RHInBoxT_1d4000000_3999999d4000000_17967_18000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h18000

/-- The 30-band NOMINAL partition of `[17000, 18000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 17000
  | 1 => 17033
  | 2 => 17067
  | 3 => 17100
  | 4 => 17133
  | 5 => 17167
  | 6 => 17200
  | 7 => 17233
  | 8 => 17267
  | 9 => 17300
  | 10 => 17333
  | 11 => 17367
  | 12 => 17400
  | 13 => 17433
  | 14 => 17467
  | 15 => 17500
  | 16 => 17533
  | 17 => 17567
  | 18 => 17600
  | 19 => 17633
  | 20 => 17667
  | 21 => 17700
  | 22 => 17733
  | 23 => 17767
  | 24 => 17800
  | 25 => 17833
  | 26 => 17867
  | 27 => 17900
  | 28 => 17933
  | 29 => 17967
  | 30 => 18000
  | _ => 18000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((17000:ℝ)) ≤ (17033); norm_num
  · show ((17033:ℝ)) ≤ (17067); norm_num
  · show ((17067:ℝ)) ≤ (17100); norm_num
  · show ((17100:ℝ)) ≤ (17133); norm_num
  · show ((17133:ℝ)) ≤ (17167); norm_num
  · show ((17167:ℝ)) ≤ (17200); norm_num
  · show ((17200:ℝ)) ≤ (17233); norm_num
  · show ((17233:ℝ)) ≤ (17267); norm_num
  · show ((17267:ℝ)) ≤ (17300); norm_num
  · show ((17300:ℝ)) ≤ (17333); norm_num
  · show ((17333:ℝ)) ≤ (17367); norm_num
  · show ((17367:ℝ)) ≤ (17400); norm_num
  · show ((17400:ℝ)) ≤ (17433); norm_num
  · show ((17433:ℝ)) ≤ (17467); norm_num
  · show ((17467:ℝ)) ≤ (17500); norm_num
  · show ((17500:ℝ)) ≤ (17533); norm_num
  · show ((17533:ℝ)) ≤ (17567); norm_num
  · show ((17567:ℝ)) ≤ (17600); norm_num
  · show ((17600:ℝ)) ≤ (17633); norm_num
  · show ((17633:ℝ)) ≤ (17667); norm_num
  · show ((17667:ℝ)) ≤ (17700); norm_num
  · show ((17700:ℝ)) ≤ (17733); norm_num
  · show ((17733:ℝ)) ≤ (17767); norm_num
  · show ((17767:ℝ)) ≤ (17800); norm_num
  · show ((17800:ℝ)) ≤ (17833); norm_num
  · show ((17833:ℝ)) ≤ (17867); norm_num
  · show ((17867:ℝ)) ≤ (17900); norm_num
  · show ((17900:ℝ)) ≤ (17933); norm_num
  · show ((17933:ℝ)) ≤ (17967); norm_num
  · show ((17967:ℝ)) ≤ (18000); norm_num
  · show ((18000:ℝ)) ≤ (18000); norm_num
  · exact le_refl _

/-- The lower edges of the 30 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 17000
  | 1 => 17033
  | 2 => 68267 / 4
  | 3 => 17100
  | 4 => 17133
  | 5 => 17167
  | 6 => 17200
  | 7 => 17233
  | 8 => 17267
  | 9 => 17300
  | 10 => 69331 / 4
  | 11 => 17367
  | 12 => 17400
  | 13 => 17433
  | 14 => 17467
  | 15 => 17500
  | 16 => 17533
  | 17 => 17567
  | 18 => 70399 / 4
  | 19 => 17633
  | 20 => 17667
  | 21 => 17700
  | 22 => 17733
  | 23 => 71067 / 4
  | 24 => 17800
  | 25 => 17833
  | 26 => 17867
  | 27 => 17900
  | 28 => 17933
  | 29 => 17967
  | _ => 17967

/-- The upper edges of the 30 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 17033
  | 1 => 17067
  | 2 => 17100
  | 3 => 68533 / 4
  | 4 => 17167
  | 5 => 17200
  | 6 => 17233
  | 7 => 17267
  | 8 => 17300
  | 9 => 17333
  | 10 => 17367
  | 11 => 17400
  | 12 => 17433
  | 13 => 17467
  | 14 => 17500
  | 15 => 17533
  | 16 => 17567
  | 17 => 17600
  | 18 => 17633
  | 19 => 17667
  | 20 => 70801 / 4
  | 21 => 17733
  | 22 => 17767
  | 23 => 17800
  | 24 => 17833
  | 25 => 17867
  | 26 => 17900
  | 27 => 17933
  | 28 => 71869 / 4
  | 29 => 18000
  | _ => 18000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 30 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 18000` (`log 18000 ≤ 10`, `2.7^10 ≥ 18000`). -/
theorem haC_18000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 18000 := by
  have hlog : Real.log 18000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 18000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 18000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[17000, 18000]` segment's band hypothesis: every band `i < 30` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 30 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 30 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[17000, 18000]` SEGMENT: every zero with `17000 ≤ Im ≤ 18000` is on the line. -/
theorem segment_17000_18000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 18000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (17000:ℝ) ≤ ρ.im → ρ.im ≤ 18000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 17000 18000 bndSeg 30 (by norm_num) bndSeg_mono rfl rfl haC_18000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 18000 via the HEIGHT CHAIN**: `[0,17000]` ∘ `[17000,18000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_18000_of_bands
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
    (hbands_16000 : AllZeros_h16000.BandHyp)
    (hbands_17000 : AllZeros_h17000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 18000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 18000 → ρ.re = 1 / 2 := by
  have hγ17000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 17000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 17000 18000
    (AllZeros_h17000.all_nontrivial_zeros_up_to_height_17000_of_bands
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
      hbands_16000
      hbands_17000
      hγ17000)
    (segment_17000_18000 hbands hγ)

end AllZeros_h18000
