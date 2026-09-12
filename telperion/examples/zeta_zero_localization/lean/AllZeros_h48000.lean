/-  Height-chain step: all nontrivial zeta zeros up to height 48000 on Re = 1/2 --
    `AllZeros_h47000` + a `[47000, 48000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h47000
import RHInBoxT_1d4000000_3999999d4000000_47000_47029
import RHInBoxT_1d4000000_3999999d4000000_47029_188237d4
import RHInBoxT_1d4000000_3999999d4000000_47059_47088
import RHInBoxT_1d4000000_3999999d4000000_188351d4_47118
import RHInBoxT_1d4000000_3999999d4000000_47118_47147
import RHInBoxT_1d4000000_3999999d4000000_188587d4_47176
import RHInBoxT_1d4000000_3999999d4000000_188703d4_47206
import RHInBoxT_1d4000000_3999999d4000000_47206_94471d2
import RHInBoxT_1d4000000_3999999d4000000_47235_47265
import RHInBoxT_1d4000000_3999999d4000000_47265_47294
import RHInBoxT_1d4000000_3999999d4000000_47294_47324
import RHInBoxT_1d4000000_3999999d4000000_47324_47353
import RHInBoxT_1d4000000_3999999d4000000_47353_47382
import RHInBoxT_1d4000000_3999999d4000000_47382_47412
import RHInBoxT_1d4000000_3999999d4000000_47412_47441
import RHInBoxT_1d4000000_3999999d4000000_47441_47471
import RHInBoxT_1d4000000_3999999d4000000_47471_47500
import RHInBoxT_1d4000000_3999999d4000000_47500_47529
import RHInBoxT_1d4000000_3999999d4000000_47529_47559
import RHInBoxT_1d4000000_3999999d4000000_47559_47588
import RHInBoxT_1d4000000_3999999d4000000_190351d4_47618
import RHInBoxT_1d4000000_3999999d4000000_47618_47647
import RHInBoxT_1d4000000_3999999d4000000_47647_47676
import RHInBoxT_1d4000000_3999999d4000000_47676_47706
import RHInBoxT_1d4000000_3999999d4000000_190823d4_47735
import RHInBoxT_1d4000000_3999999d4000000_47735_47765
import RHInBoxT_1d4000000_3999999d4000000_47765_47794
import RHInBoxT_1d4000000_3999999d4000000_191175d4_47824
import RHInBoxT_1d4000000_3999999d4000000_47824_47853
import RHInBoxT_1d4000000_3999999d4000000_47853_47882
import RHInBoxT_1d4000000_3999999d4000000_47882_47912
import RHInBoxT_1d4000000_3999999d4000000_47912_47941
import RHInBoxT_1d4000000_3999999d4000000_47941_47971
import RHInBoxT_1d4000000_3999999d4000000_47971_48000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h48000

/-- The 34-band NOMINAL partition of `[47000, 48000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 47000
  | 1 => 47029
  | 2 => 47059
  | 3 => 47088
  | 4 => 47118
  | 5 => 47147
  | 6 => 47176
  | 7 => 47206
  | 8 => 47235
  | 9 => 47265
  | 10 => 47294
  | 11 => 47324
  | 12 => 47353
  | 13 => 47382
  | 14 => 47412
  | 15 => 47441
  | 16 => 47471
  | 17 => 47500
  | 18 => 47529
  | 19 => 47559
  | 20 => 47588
  | 21 => 47618
  | 22 => 47647
  | 23 => 47676
  | 24 => 47706
  | 25 => 47735
  | 26 => 47765
  | 27 => 47794
  | 28 => 47824
  | 29 => 47853
  | 30 => 47882
  | 31 => 47912
  | 32 => 47941
  | 33 => 47971
  | 34 => 48000
  | _ => 48000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((47000:ℝ)) ≤ (47029); norm_num
  · show ((47029:ℝ)) ≤ (47059); norm_num
  · show ((47059:ℝ)) ≤ (47088); norm_num
  · show ((47088:ℝ)) ≤ (47118); norm_num
  · show ((47118:ℝ)) ≤ (47147); norm_num
  · show ((47147:ℝ)) ≤ (47176); norm_num
  · show ((47176:ℝ)) ≤ (47206); norm_num
  · show ((47206:ℝ)) ≤ (47235); norm_num
  · show ((47235:ℝ)) ≤ (47265); norm_num
  · show ((47265:ℝ)) ≤ (47294); norm_num
  · show ((47294:ℝ)) ≤ (47324); norm_num
  · show ((47324:ℝ)) ≤ (47353); norm_num
  · show ((47353:ℝ)) ≤ (47382); norm_num
  · show ((47382:ℝ)) ≤ (47412); norm_num
  · show ((47412:ℝ)) ≤ (47441); norm_num
  · show ((47441:ℝ)) ≤ (47471); norm_num
  · show ((47471:ℝ)) ≤ (47500); norm_num
  · show ((47500:ℝ)) ≤ (47529); norm_num
  · show ((47529:ℝ)) ≤ (47559); norm_num
  · show ((47559:ℝ)) ≤ (47588); norm_num
  · show ((47588:ℝ)) ≤ (47618); norm_num
  · show ((47618:ℝ)) ≤ (47647); norm_num
  · show ((47647:ℝ)) ≤ (47676); norm_num
  · show ((47676:ℝ)) ≤ (47706); norm_num
  · show ((47706:ℝ)) ≤ (47735); norm_num
  · show ((47735:ℝ)) ≤ (47765); norm_num
  · show ((47765:ℝ)) ≤ (47794); norm_num
  · show ((47794:ℝ)) ≤ (47824); norm_num
  · show ((47824:ℝ)) ≤ (47853); norm_num
  · show ((47853:ℝ)) ≤ (47882); norm_num
  · show ((47882:ℝ)) ≤ (47912); norm_num
  · show ((47912:ℝ)) ≤ (47941); norm_num
  · show ((47941:ℝ)) ≤ (47971); norm_num
  · show ((47971:ℝ)) ≤ (48000); norm_num
  · show ((48000:ℝ)) ≤ (48000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 47000
  | 1 => 47029
  | 2 => 47059
  | 3 => 188351 / 4
  | 4 => 47118
  | 5 => 188587 / 4
  | 6 => 188703 / 4
  | 7 => 47206
  | 8 => 47235
  | 9 => 47265
  | 10 => 47294
  | 11 => 47324
  | 12 => 47353
  | 13 => 47382
  | 14 => 47412
  | 15 => 47441
  | 16 => 47471
  | 17 => 47500
  | 18 => 47529
  | 19 => 47559
  | 20 => 190351 / 4
  | 21 => 47618
  | 22 => 47647
  | 23 => 47676
  | 24 => 190823 / 4
  | 25 => 47735
  | 26 => 47765
  | 27 => 191175 / 4
  | 28 => 47824
  | 29 => 47853
  | 30 => 47882
  | 31 => 47912
  | 32 => 47941
  | 33 => 47971
  | _ => 47971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 47029
  | 1 => 188237 / 4
  | 2 => 47088
  | 3 => 47118
  | 4 => 47147
  | 5 => 47176
  | 6 => 47206
  | 7 => 94471 / 2
  | 8 => 47265
  | 9 => 47294
  | 10 => 47324
  | 11 => 47353
  | 12 => 47382
  | 13 => 47412
  | 14 => 47441
  | 15 => 47471
  | 16 => 47500
  | 17 => 47529
  | 18 => 47559
  | 19 => 47588
  | 20 => 47618
  | 21 => 47647
  | 22 => 47676
  | 23 => 47706
  | 24 => 47735
  | 25 => 47765
  | 26 => 47794
  | 27 => 47824
  | 28 => 47853
  | 29 => 47882
  | 30 => 47912
  | 31 => 47941
  | 32 => 47971
  | 33 => 48000
  | _ => 48000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 48000` (`log 48000 ≤ 11`, `2.7^11 ≥ 48000`). -/
theorem haC_48000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 48000 := by
  have hlog : Real.log 48000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 48000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 48000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[47000, 48000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[47000, 48000]` SEGMENT: every zero with `47000 ≤ Im ≤ 48000` is on the line. -/
theorem segment_47000_48000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 48000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (47000:ℝ) ≤ ρ.im → ρ.im ≤ 48000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 47000 48000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_48000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 48000 via the HEIGHT CHAIN**: `[0,47000]` ∘ `[47000,48000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_48000_of_bands
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
    (hbands_18000 : AllZeros_h18000.BandHyp)
    (hbands_19000 : AllZeros_h19000.BandHyp)
    (hbands_20000 : AllZeros_h20000.BandHyp)
    (hbands_21000 : AllZeros_h21000.BandHyp)
    (hbands_22000 : AllZeros_h22000.BandHyp)
    (hbands_23000 : AllZeros_h23000.BandHyp)
    (hbands_24000 : AllZeros_h24000.BandHyp)
    (hbands_25000 : AllZeros_h25000.BandHyp)
    (hbands_26000 : AllZeros_h26000.BandHyp)
    (hbands_27000 : AllZeros_h27000.BandHyp)
    (hbands_28000 : AllZeros_h28000.BandHyp)
    (hbands_29000 : AllZeros_h29000.BandHyp)
    (hbands_30000 : AllZeros_h30000.BandHyp)
    (hbands_31000 : AllZeros_h31000.BandHyp)
    (hbands_32000 : AllZeros_h32000.BandHyp)
    (hbands_33000 : AllZeros_h33000.BandHyp)
    (hbands_34000 : AllZeros_h34000.BandHyp)
    (hbands_35000 : AllZeros_h35000.BandHyp)
    (hbands_36000 : AllZeros_h36000.BandHyp)
    (hbands_37000 : AllZeros_h37000.BandHyp)
    (hbands_38000 : AllZeros_h38000.BandHyp)
    (hbands_39000 : AllZeros_h39000.BandHyp)
    (hbands_40000 : AllZeros_h40000.BandHyp)
    (hbands_41000 : AllZeros_h41000.BandHyp)
    (hbands_42000 : AllZeros_h42000.BandHyp)
    (hbands_43000 : AllZeros_h43000.BandHyp)
    (hbands_44000 : AllZeros_h44000.BandHyp)
    (hbands_45000 : AllZeros_h45000.BandHyp)
    (hbands_46000 : AllZeros_h46000.BandHyp)
    (hbands_47000 : AllZeros_h47000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 48000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 48000 → ρ.re = 1 / 2 := by
  have hγ47000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 47000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 47000 48000
    (AllZeros_h47000.all_nontrivial_zeros_up_to_height_47000_of_bands
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
      hbands_18000
      hbands_19000
      hbands_20000
      hbands_21000
      hbands_22000
      hbands_23000
      hbands_24000
      hbands_25000
      hbands_26000
      hbands_27000
      hbands_28000
      hbands_29000
      hbands_30000
      hbands_31000
      hbands_32000
      hbands_33000
      hbands_34000
      hbands_35000
      hbands_36000
      hbands_37000
      hbands_38000
      hbands_39000
      hbands_40000
      hbands_41000
      hbands_42000
      hbands_43000
      hbands_44000
      hbands_45000
      hbands_46000
      hbands_47000
      hγ47000)
    (segment_47000_48000 hbands hγ)

end AllZeros_h48000
