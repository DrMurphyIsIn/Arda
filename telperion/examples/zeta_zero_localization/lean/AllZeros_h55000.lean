/-  Height-chain step: all nontrivial zeta zeros up to height 55000 on Re = 1/2 --
    `AllZeros_h54000` + a `[54000, 55000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h54000
import RHInBoxT_1d4000000_3999999d4000000_54000_54029
import RHInBoxT_1d4000000_3999999d4000000_54029_54057
import RHInBoxT_1d4000000_3999999d4000000_54057_54086
import RHInBoxT_1d4000000_3999999d4000000_54086_54114
import RHInBoxT_1d4000000_3999999d4000000_54114_54143
import RHInBoxT_1d4000000_3999999d4000000_54143_54171
import RHInBoxT_1d4000000_3999999d4000000_54171_54200
import RHInBoxT_1d4000000_3999999d4000000_54200_54229
import RHInBoxT_1d4000000_3999999d4000000_54229_54257
import RHInBoxT_1d4000000_3999999d4000000_54257_217145d4
import RHInBoxT_1d4000000_3999999d4000000_54286_54314
import RHInBoxT_1d4000000_3999999d4000000_54314_217373d4
import RHInBoxT_1d4000000_3999999d4000000_54343_54371
import RHInBoxT_1d4000000_3999999d4000000_54371_54400
import RHInBoxT_1d4000000_3999999d4000000_54400_54429
import RHInBoxT_1d4000000_3999999d4000000_54429_217829d4
import RHInBoxT_1d4000000_3999999d4000000_54457_54486
import RHInBoxT_1d4000000_3999999d4000000_54486_54514
import RHInBoxT_1d4000000_3999999d4000000_54514_54543
import RHInBoxT_1d4000000_3999999d4000000_54543_54571
import RHInBoxT_1d4000000_3999999d4000000_54571_54600
import RHInBoxT_1d4000000_3999999d4000000_54600_54629
import RHInBoxT_1d4000000_3999999d4000000_109257d2_54657
import RHInBoxT_1d4000000_3999999d4000000_54657_54686
import RHInBoxT_1d4000000_3999999d4000000_54686_54714
import RHInBoxT_1d4000000_3999999d4000000_54714_54743
import RHInBoxT_1d4000000_3999999d4000000_54743_54771
import RHInBoxT_1d4000000_3999999d4000000_54771_219201d4
import RHInBoxT_1d4000000_3999999d4000000_54800_54829
import RHInBoxT_1d4000000_3999999d4000000_54829_219429d4
import RHInBoxT_1d4000000_3999999d4000000_54857_54886
import RHInBoxT_1d4000000_3999999d4000000_54886_54914
import RHInBoxT_1d4000000_3999999d4000000_54914_219773d4
import RHInBoxT_1d4000000_3999999d4000000_54943_54971
import RHInBoxT_1d4000000_3999999d4000000_219883d4_55000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h55000

/-- The 35-band NOMINAL partition of `[54000, 55000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 54000
  | 1 => 54029
  | 2 => 54057
  | 3 => 54086
  | 4 => 54114
  | 5 => 54143
  | 6 => 54171
  | 7 => 54200
  | 8 => 54229
  | 9 => 54257
  | 10 => 54286
  | 11 => 54314
  | 12 => 54343
  | 13 => 54371
  | 14 => 54400
  | 15 => 54429
  | 16 => 54457
  | 17 => 54486
  | 18 => 54514
  | 19 => 54543
  | 20 => 54571
  | 21 => 54600
  | 22 => 54629
  | 23 => 54657
  | 24 => 54686
  | 25 => 54714
  | 26 => 54743
  | 27 => 54771
  | 28 => 54800
  | 29 => 54829
  | 30 => 54857
  | 31 => 54886
  | 32 => 54914
  | 33 => 54943
  | 34 => 54971
  | 35 => 55000
  | _ => 55000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((54000:ℝ)) ≤ (54029); norm_num
  · show ((54029:ℝ)) ≤ (54057); norm_num
  · show ((54057:ℝ)) ≤ (54086); norm_num
  · show ((54086:ℝ)) ≤ (54114); norm_num
  · show ((54114:ℝ)) ≤ (54143); norm_num
  · show ((54143:ℝ)) ≤ (54171); norm_num
  · show ((54171:ℝ)) ≤ (54200); norm_num
  · show ((54200:ℝ)) ≤ (54229); norm_num
  · show ((54229:ℝ)) ≤ (54257); norm_num
  · show ((54257:ℝ)) ≤ (54286); norm_num
  · show ((54286:ℝ)) ≤ (54314); norm_num
  · show ((54314:ℝ)) ≤ (54343); norm_num
  · show ((54343:ℝ)) ≤ (54371); norm_num
  · show ((54371:ℝ)) ≤ (54400); norm_num
  · show ((54400:ℝ)) ≤ (54429); norm_num
  · show ((54429:ℝ)) ≤ (54457); norm_num
  · show ((54457:ℝ)) ≤ (54486); norm_num
  · show ((54486:ℝ)) ≤ (54514); norm_num
  · show ((54514:ℝ)) ≤ (54543); norm_num
  · show ((54543:ℝ)) ≤ (54571); norm_num
  · show ((54571:ℝ)) ≤ (54600); norm_num
  · show ((54600:ℝ)) ≤ (54629); norm_num
  · show ((54629:ℝ)) ≤ (54657); norm_num
  · show ((54657:ℝ)) ≤ (54686); norm_num
  · show ((54686:ℝ)) ≤ (54714); norm_num
  · show ((54714:ℝ)) ≤ (54743); norm_num
  · show ((54743:ℝ)) ≤ (54771); norm_num
  · show ((54771:ℝ)) ≤ (54800); norm_num
  · show ((54800:ℝ)) ≤ (54829); norm_num
  · show ((54829:ℝ)) ≤ (54857); norm_num
  · show ((54857:ℝ)) ≤ (54886); norm_num
  · show ((54886:ℝ)) ≤ (54914); norm_num
  · show ((54914:ℝ)) ≤ (54943); norm_num
  · show ((54943:ℝ)) ≤ (54971); norm_num
  · show ((54971:ℝ)) ≤ (55000); norm_num
  · show ((55000:ℝ)) ≤ (55000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 54000
  | 1 => 54029
  | 2 => 54057
  | 3 => 54086
  | 4 => 54114
  | 5 => 54143
  | 6 => 54171
  | 7 => 54200
  | 8 => 54229
  | 9 => 54257
  | 10 => 54286
  | 11 => 54314
  | 12 => 54343
  | 13 => 54371
  | 14 => 54400
  | 15 => 54429
  | 16 => 54457
  | 17 => 54486
  | 18 => 54514
  | 19 => 54543
  | 20 => 54571
  | 21 => 54600
  | 22 => 109257 / 2
  | 23 => 54657
  | 24 => 54686
  | 25 => 54714
  | 26 => 54743
  | 27 => 54771
  | 28 => 54800
  | 29 => 54829
  | 30 => 54857
  | 31 => 54886
  | 32 => 54914
  | 33 => 54943
  | 34 => 219883 / 4
  | _ => 219883 / 4

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 54029
  | 1 => 54057
  | 2 => 54086
  | 3 => 54114
  | 4 => 54143
  | 5 => 54171
  | 6 => 54200
  | 7 => 54229
  | 8 => 54257
  | 9 => 217145 / 4
  | 10 => 54314
  | 11 => 217373 / 4
  | 12 => 54371
  | 13 => 54400
  | 14 => 54429
  | 15 => 217829 / 4
  | 16 => 54486
  | 17 => 54514
  | 18 => 54543
  | 19 => 54571
  | 20 => 54600
  | 21 => 54629
  | 22 => 54657
  | 23 => 54686
  | 24 => 54714
  | 25 => 54743
  | 26 => 54771
  | 27 => 219201 / 4
  | 28 => 54829
  | 29 => 219429 / 4
  | 30 => 54886
  | 31 => 54914
  | 32 => 219773 / 4
  | 33 => 54971
  | 34 => 55000
  | _ => 55000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 55000` (`log 55000 ≤ 11`, `2.7^11 ≥ 55000`). -/
theorem haC_55000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 55000 := by
  have hlog : Real.log 55000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 55000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 55000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[54000, 55000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[54000, 55000]` SEGMENT: every zero with `54000 ≤ Im ≤ 55000` is on the line. -/
theorem segment_54000_55000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 55000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (54000:ℝ) ≤ ρ.im → ρ.im ≤ 55000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 54000 55000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_55000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 55000 via the HEIGHT CHAIN**: `[0,54000]` ∘ `[54000,55000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_55000_of_bands
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
    (hbands_48000 : AllZeros_h48000.BandHyp)
    (hbands_49000 : AllZeros_h49000.BandHyp)
    (hbands_50000 : AllZeros_h50000.BandHyp)
    (hbands_51000 : AllZeros_h51000.BandHyp)
    (hbands_52000 : AllZeros_h52000.BandHyp)
    (hbands_53000 : AllZeros_h53000.BandHyp)
    (hbands_54000 : AllZeros_h54000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 55000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 55000 → ρ.re = 1 / 2 := by
  have hγ54000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 54000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 54000 55000
    (AllZeros_h54000.all_nontrivial_zeros_up_to_height_54000_of_bands
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
      hbands_48000
      hbands_49000
      hbands_50000
      hbands_51000
      hbands_52000
      hbands_53000
      hbands_54000
      hγ54000)
    (segment_54000_55000 hbands hγ)

end AllZeros_h55000
