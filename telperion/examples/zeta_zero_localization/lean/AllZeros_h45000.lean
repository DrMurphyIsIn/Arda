/-  Height-chain step: all nontrivial zeta zeros up to height 45000 on Re = 1/2 --
    `AllZeros_h44000` + a `[44000, 45000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h44000
import RHInBoxT_1d4000000_3999999d4000000_44000_44029
import RHInBoxT_1d4000000_3999999d4000000_44029_44059
import RHInBoxT_1d4000000_3999999d4000000_44059_44088
import RHInBoxT_1d4000000_3999999d4000000_44088_44118
import RHInBoxT_1d4000000_3999999d4000000_44118_44147
import RHInBoxT_1d4000000_3999999d4000000_44147_44176
import RHInBoxT_1d4000000_3999999d4000000_176703d4_44206
import RHInBoxT_1d4000000_3999999d4000000_44206_176941d4
import RHInBoxT_1d4000000_3999999d4000000_44235_44265
import RHInBoxT_1d4000000_3999999d4000000_44265_44294
import RHInBoxT_1d4000000_3999999d4000000_44294_177297d4
import RHInBoxT_1d4000000_3999999d4000000_44324_44353
import RHInBoxT_1d4000000_3999999d4000000_44353_44382
import RHInBoxT_1d4000000_3999999d4000000_177527d4_44412
import RHInBoxT_1d4000000_3999999d4000000_44412_44441
import RHInBoxT_1d4000000_3999999d4000000_44441_44471
import RHInBoxT_1d4000000_3999999d4000000_44471_44500
import RHInBoxT_1d4000000_3999999d4000000_44500_44529
import RHInBoxT_1d4000000_3999999d4000000_178115d4_44559
import RHInBoxT_1d4000000_3999999d4000000_44559_44588
import RHInBoxT_1d4000000_3999999d4000000_44588_44618
import RHInBoxT_1d4000000_3999999d4000000_44618_178589d4
import RHInBoxT_1d4000000_3999999d4000000_44647_44676
import RHInBoxT_1d4000000_3999999d4000000_44676_44706
import RHInBoxT_1d4000000_3999999d4000000_44706_44735
import RHInBoxT_1d4000000_3999999d4000000_44735_44765
import RHInBoxT_1d4000000_3999999d4000000_44765_179177d4
import RHInBoxT_1d4000000_3999999d4000000_44794_44824
import RHInBoxT_1d4000000_3999999d4000000_44824_44853
import RHInBoxT_1d4000000_3999999d4000000_179411d4_44882
import RHInBoxT_1d4000000_3999999d4000000_44882_44912
import RHInBoxT_1d4000000_3999999d4000000_44912_44941
import RHInBoxT_1d4000000_3999999d4000000_44941_44971
import RHInBoxT_1d4000000_3999999d4000000_44971_45000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h45000

/-- The 34-band NOMINAL partition of `[44000, 45000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 44000
  | 1 => 44029
  | 2 => 44059
  | 3 => 44088
  | 4 => 44118
  | 5 => 44147
  | 6 => 44176
  | 7 => 44206
  | 8 => 44235
  | 9 => 44265
  | 10 => 44294
  | 11 => 44324
  | 12 => 44353
  | 13 => 44382
  | 14 => 44412
  | 15 => 44441
  | 16 => 44471
  | 17 => 44500
  | 18 => 44529
  | 19 => 44559
  | 20 => 44588
  | 21 => 44618
  | 22 => 44647
  | 23 => 44676
  | 24 => 44706
  | 25 => 44735
  | 26 => 44765
  | 27 => 44794
  | 28 => 44824
  | 29 => 44853
  | 30 => 44882
  | 31 => 44912
  | 32 => 44941
  | 33 => 44971
  | 34 => 45000
  | _ => 45000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((44000:ℝ)) ≤ (44029); norm_num
  · show ((44029:ℝ)) ≤ (44059); norm_num
  · show ((44059:ℝ)) ≤ (44088); norm_num
  · show ((44088:ℝ)) ≤ (44118); norm_num
  · show ((44118:ℝ)) ≤ (44147); norm_num
  · show ((44147:ℝ)) ≤ (44176); norm_num
  · show ((44176:ℝ)) ≤ (44206); norm_num
  · show ((44206:ℝ)) ≤ (44235); norm_num
  · show ((44235:ℝ)) ≤ (44265); norm_num
  · show ((44265:ℝ)) ≤ (44294); norm_num
  · show ((44294:ℝ)) ≤ (44324); norm_num
  · show ((44324:ℝ)) ≤ (44353); norm_num
  · show ((44353:ℝ)) ≤ (44382); norm_num
  · show ((44382:ℝ)) ≤ (44412); norm_num
  · show ((44412:ℝ)) ≤ (44441); norm_num
  · show ((44441:ℝ)) ≤ (44471); norm_num
  · show ((44471:ℝ)) ≤ (44500); norm_num
  · show ((44500:ℝ)) ≤ (44529); norm_num
  · show ((44529:ℝ)) ≤ (44559); norm_num
  · show ((44559:ℝ)) ≤ (44588); norm_num
  · show ((44588:ℝ)) ≤ (44618); norm_num
  · show ((44618:ℝ)) ≤ (44647); norm_num
  · show ((44647:ℝ)) ≤ (44676); norm_num
  · show ((44676:ℝ)) ≤ (44706); norm_num
  · show ((44706:ℝ)) ≤ (44735); norm_num
  · show ((44735:ℝ)) ≤ (44765); norm_num
  · show ((44765:ℝ)) ≤ (44794); norm_num
  · show ((44794:ℝ)) ≤ (44824); norm_num
  · show ((44824:ℝ)) ≤ (44853); norm_num
  · show ((44853:ℝ)) ≤ (44882); norm_num
  · show ((44882:ℝ)) ≤ (44912); norm_num
  · show ((44912:ℝ)) ≤ (44941); norm_num
  · show ((44941:ℝ)) ≤ (44971); norm_num
  · show ((44971:ℝ)) ≤ (45000); norm_num
  · show ((45000:ℝ)) ≤ (45000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 44000
  | 1 => 44029
  | 2 => 44059
  | 3 => 44088
  | 4 => 44118
  | 5 => 44147
  | 6 => 176703 / 4
  | 7 => 44206
  | 8 => 44235
  | 9 => 44265
  | 10 => 44294
  | 11 => 44324
  | 12 => 44353
  | 13 => 177527 / 4
  | 14 => 44412
  | 15 => 44441
  | 16 => 44471
  | 17 => 44500
  | 18 => 178115 / 4
  | 19 => 44559
  | 20 => 44588
  | 21 => 44618
  | 22 => 44647
  | 23 => 44676
  | 24 => 44706
  | 25 => 44735
  | 26 => 44765
  | 27 => 44794
  | 28 => 44824
  | 29 => 179411 / 4
  | 30 => 44882
  | 31 => 44912
  | 32 => 44941
  | 33 => 44971
  | _ => 44971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 44029
  | 1 => 44059
  | 2 => 44088
  | 3 => 44118
  | 4 => 44147
  | 5 => 44176
  | 6 => 44206
  | 7 => 176941 / 4
  | 8 => 44265
  | 9 => 44294
  | 10 => 177297 / 4
  | 11 => 44353
  | 12 => 44382
  | 13 => 44412
  | 14 => 44441
  | 15 => 44471
  | 16 => 44500
  | 17 => 44529
  | 18 => 44559
  | 19 => 44588
  | 20 => 44618
  | 21 => 178589 / 4
  | 22 => 44676
  | 23 => 44706
  | 24 => 44735
  | 25 => 44765
  | 26 => 179177 / 4
  | 27 => 44824
  | 28 => 44853
  | 29 => 44882
  | 30 => 44912
  | 31 => 44941
  | 32 => 44971
  | 33 => 45000
  | _ => 45000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 45000` (`log 45000 ≤ 11`, `2.7^11 ≥ 45000`). -/
theorem haC_45000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 45000 := by
  have hlog : Real.log 45000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 45000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 45000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[44000, 45000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[44000, 45000]` SEGMENT: every zero with `44000 ≤ Im ≤ 45000` is on the line. -/
theorem segment_44000_45000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 45000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (44000:ℝ) ≤ ρ.im → ρ.im ≤ 45000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 44000 45000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_45000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 45000 via the HEIGHT CHAIN**: `[0,44000]` ∘ `[44000,45000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_45000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 45000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 45000 → ρ.re = 1 / 2 := by
  have hγ44000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 44000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 44000 45000
    (AllZeros_h44000.all_nontrivial_zeros_up_to_height_44000_of_bands
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
      hγ44000)
    (segment_44000_45000 hbands hγ)

end AllZeros_h45000
