/-  Height-chain step: all nontrivial zeta zeros up to height 42000 on Re = 1/2 --
    `AllZeros_h41000` + a `[41000, 42000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h41000
import RHInBoxT_1d4000000_3999999d4000000_41000_41029
import RHInBoxT_1d4000000_3999999d4000000_41029_41059
import RHInBoxT_1d4000000_3999999d4000000_164235d4_41088
import RHInBoxT_1d4000000_3999999d4000000_41088_41118
import RHInBoxT_1d4000000_3999999d4000000_41118_41147
import RHInBoxT_1d4000000_3999999d4000000_41147_41176
import RHInBoxT_1d4000000_3999999d4000000_41176_41206
import RHInBoxT_1d4000000_3999999d4000000_41206_41235
import RHInBoxT_1d4000000_3999999d4000000_41235_41265
import RHInBoxT_1d4000000_3999999d4000000_41265_41294
import RHInBoxT_1d4000000_3999999d4000000_41294_41324
import RHInBoxT_1d4000000_3999999d4000000_41324_41353
import RHInBoxT_1d4000000_3999999d4000000_165411d4_41382
import RHInBoxT_1d4000000_3999999d4000000_41382_41412
import RHInBoxT_1d4000000_3999999d4000000_41412_165765d4
import RHInBoxT_1d4000000_3999999d4000000_41441_41471
import RHInBoxT_1d4000000_3999999d4000000_41471_41500
import RHInBoxT_1d4000000_3999999d4000000_41500_41529
import RHInBoxT_1d4000000_3999999d4000000_166115d4_41559
import RHInBoxT_1d4000000_3999999d4000000_41559_41588
import RHInBoxT_1d4000000_3999999d4000000_41588_41618
import RHInBoxT_1d4000000_3999999d4000000_41618_41647
import RHInBoxT_1d4000000_3999999d4000000_41647_41676
import RHInBoxT_1d4000000_3999999d4000000_41676_166825d4
import RHInBoxT_1d4000000_3999999d4000000_41706_41735
import RHInBoxT_1d4000000_3999999d4000000_41735_41765
import RHInBoxT_1d4000000_3999999d4000000_41765_41794
import RHInBoxT_1d4000000_3999999d4000000_41794_41824
import RHInBoxT_1d4000000_3999999d4000000_41824_41853
import RHInBoxT_1d4000000_3999999d4000000_41853_41882
import RHInBoxT_1d4000000_3999999d4000000_41882_41912
import RHInBoxT_1d4000000_3999999d4000000_41912_41941
import RHInBoxT_1d4000000_3999999d4000000_41941_41971
import RHInBoxT_1d4000000_3999999d4000000_41971_42000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h42000

/-- The 34-band NOMINAL partition of `[41000, 42000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 41000
  | 1 => 41029
  | 2 => 41059
  | 3 => 41088
  | 4 => 41118
  | 5 => 41147
  | 6 => 41176
  | 7 => 41206
  | 8 => 41235
  | 9 => 41265
  | 10 => 41294
  | 11 => 41324
  | 12 => 41353
  | 13 => 41382
  | 14 => 41412
  | 15 => 41441
  | 16 => 41471
  | 17 => 41500
  | 18 => 41529
  | 19 => 41559
  | 20 => 41588
  | 21 => 41618
  | 22 => 41647
  | 23 => 41676
  | 24 => 41706
  | 25 => 41735
  | 26 => 41765
  | 27 => 41794
  | 28 => 41824
  | 29 => 41853
  | 30 => 41882
  | 31 => 41912
  | 32 => 41941
  | 33 => 41971
  | 34 => 42000
  | _ => 42000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((41000:ℝ)) ≤ (41029); norm_num
  · show ((41029:ℝ)) ≤ (41059); norm_num
  · show ((41059:ℝ)) ≤ (41088); norm_num
  · show ((41088:ℝ)) ≤ (41118); norm_num
  · show ((41118:ℝ)) ≤ (41147); norm_num
  · show ((41147:ℝ)) ≤ (41176); norm_num
  · show ((41176:ℝ)) ≤ (41206); norm_num
  · show ((41206:ℝ)) ≤ (41235); norm_num
  · show ((41235:ℝ)) ≤ (41265); norm_num
  · show ((41265:ℝ)) ≤ (41294); norm_num
  · show ((41294:ℝ)) ≤ (41324); norm_num
  · show ((41324:ℝ)) ≤ (41353); norm_num
  · show ((41353:ℝ)) ≤ (41382); norm_num
  · show ((41382:ℝ)) ≤ (41412); norm_num
  · show ((41412:ℝ)) ≤ (41441); norm_num
  · show ((41441:ℝ)) ≤ (41471); norm_num
  · show ((41471:ℝ)) ≤ (41500); norm_num
  · show ((41500:ℝ)) ≤ (41529); norm_num
  · show ((41529:ℝ)) ≤ (41559); norm_num
  · show ((41559:ℝ)) ≤ (41588); norm_num
  · show ((41588:ℝ)) ≤ (41618); norm_num
  · show ((41618:ℝ)) ≤ (41647); norm_num
  · show ((41647:ℝ)) ≤ (41676); norm_num
  · show ((41676:ℝ)) ≤ (41706); norm_num
  · show ((41706:ℝ)) ≤ (41735); norm_num
  · show ((41735:ℝ)) ≤ (41765); norm_num
  · show ((41765:ℝ)) ≤ (41794); norm_num
  · show ((41794:ℝ)) ≤ (41824); norm_num
  · show ((41824:ℝ)) ≤ (41853); norm_num
  · show ((41853:ℝ)) ≤ (41882); norm_num
  · show ((41882:ℝ)) ≤ (41912); norm_num
  · show ((41912:ℝ)) ≤ (41941); norm_num
  · show ((41941:ℝ)) ≤ (41971); norm_num
  · show ((41971:ℝ)) ≤ (42000); norm_num
  · show ((42000:ℝ)) ≤ (42000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 41000
  | 1 => 41029
  | 2 => 164235 / 4
  | 3 => 41088
  | 4 => 41118
  | 5 => 41147
  | 6 => 41176
  | 7 => 41206
  | 8 => 41235
  | 9 => 41265
  | 10 => 41294
  | 11 => 41324
  | 12 => 165411 / 4
  | 13 => 41382
  | 14 => 41412
  | 15 => 41441
  | 16 => 41471
  | 17 => 41500
  | 18 => 166115 / 4
  | 19 => 41559
  | 20 => 41588
  | 21 => 41618
  | 22 => 41647
  | 23 => 41676
  | 24 => 41706
  | 25 => 41735
  | 26 => 41765
  | 27 => 41794
  | 28 => 41824
  | 29 => 41853
  | 30 => 41882
  | 31 => 41912
  | 32 => 41941
  | 33 => 41971
  | _ => 41971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 41029
  | 1 => 41059
  | 2 => 41088
  | 3 => 41118
  | 4 => 41147
  | 5 => 41176
  | 6 => 41206
  | 7 => 41235
  | 8 => 41265
  | 9 => 41294
  | 10 => 41324
  | 11 => 41353
  | 12 => 41382
  | 13 => 41412
  | 14 => 165765 / 4
  | 15 => 41471
  | 16 => 41500
  | 17 => 41529
  | 18 => 41559
  | 19 => 41588
  | 20 => 41618
  | 21 => 41647
  | 22 => 41676
  | 23 => 166825 / 4
  | 24 => 41735
  | 25 => 41765
  | 26 => 41794
  | 27 => 41824
  | 28 => 41853
  | 29 => 41882
  | 30 => 41912
  | 31 => 41941
  | 32 => 41971
  | 33 => 42000
  | _ => 42000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 42000` (`log 42000 ≤ 11`, `2.7^11 ≥ 42000`). -/
theorem haC_42000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 42000 := by
  have hlog : Real.log 42000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 42000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 42000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[41000, 42000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[41000, 42000]` SEGMENT: every zero with `41000 ≤ Im ≤ 42000` is on the line. -/
theorem segment_41000_42000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 42000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (41000:ℝ) ≤ ρ.im → ρ.im ≤ 42000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 41000 42000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_42000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 42000 via the HEIGHT CHAIN**: `[0,41000]` ∘ `[41000,42000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_42000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 42000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 42000 → ρ.re = 1 / 2 := by
  have hγ41000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 41000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 41000 42000
    (AllZeros_h41000.all_nontrivial_zeros_up_to_height_41000_of_bands
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
      hγ41000)
    (segment_41000_42000 hbands hγ)

end AllZeros_h42000
