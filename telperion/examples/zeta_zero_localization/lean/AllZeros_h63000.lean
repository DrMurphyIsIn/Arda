/-  Height-chain step: all nontrivial zeta zeros up to height 63000 on Re = 1/2 --
    `AllZeros_h62000` + a `[62000, 63000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h62000
import RHInBoxT_1d4000000_3999999d4000000_62000_62029
import RHInBoxT_1d4000000_3999999d4000000_62029_62057
import RHInBoxT_1d4000000_3999999d4000000_62057_248345d4
import RHInBoxT_1d4000000_3999999d4000000_62086_62114
import RHInBoxT_1d4000000_3999999d4000000_248455d4_62143
import RHInBoxT_1d4000000_3999999d4000000_62143_62171
import RHInBoxT_1d4000000_3999999d4000000_62171_62200
import RHInBoxT_1d4000000_3999999d4000000_62200_62229
import RHInBoxT_1d4000000_3999999d4000000_62229_62257
import RHInBoxT_1d4000000_3999999d4000000_62257_249145d4
import RHInBoxT_1d4000000_3999999d4000000_62286_249257d4
import RHInBoxT_1d4000000_3999999d4000000_62314_62343
import RHInBoxT_1d4000000_3999999d4000000_62343_62371
import RHInBoxT_1d4000000_3999999d4000000_62371_62400
import RHInBoxT_1d4000000_3999999d4000000_62400_62429
import RHInBoxT_1d4000000_3999999d4000000_62429_62457
import RHInBoxT_1d4000000_3999999d4000000_62457_62486
import RHInBoxT_1d4000000_3999999d4000000_62486_62514
import RHInBoxT_1d4000000_3999999d4000000_62514_62543
import RHInBoxT_1d4000000_3999999d4000000_62543_62571
import RHInBoxT_1d4000000_3999999d4000000_62571_62600
import RHInBoxT_1d4000000_3999999d4000000_62600_62629
import RHInBoxT_1d4000000_3999999d4000000_250515d4_125315d2
import RHInBoxT_1d4000000_3999999d4000000_62657_62686
import RHInBoxT_1d4000000_3999999d4000000_62686_62714
import RHInBoxT_1d4000000_3999999d4000000_62714_62743
import RHInBoxT_1d4000000_3999999d4000000_62743_62771
import RHInBoxT_1d4000000_3999999d4000000_62771_62800
import RHInBoxT_1d4000000_3999999d4000000_62800_62829
import RHInBoxT_1d4000000_3999999d4000000_62829_251429d4
import RHInBoxT_1d4000000_3999999d4000000_62857_62886
import RHInBoxT_1d4000000_3999999d4000000_62886_62914
import RHInBoxT_1d4000000_3999999d4000000_62914_251773d4
import RHInBoxT_1d4000000_3999999d4000000_62943_62971
import RHInBoxT_1d4000000_3999999d4000000_62971_63000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h63000

/-- The 35-band NOMINAL partition of `[62000, 63000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 62000
  | 1 => 62029
  | 2 => 62057
  | 3 => 62086
  | 4 => 62114
  | 5 => 62143
  | 6 => 62171
  | 7 => 62200
  | 8 => 62229
  | 9 => 62257
  | 10 => 62286
  | 11 => 62314
  | 12 => 62343
  | 13 => 62371
  | 14 => 62400
  | 15 => 62429
  | 16 => 62457
  | 17 => 62486
  | 18 => 62514
  | 19 => 62543
  | 20 => 62571
  | 21 => 62600
  | 22 => 62629
  | 23 => 62657
  | 24 => 62686
  | 25 => 62714
  | 26 => 62743
  | 27 => 62771
  | 28 => 62800
  | 29 => 62829
  | 30 => 62857
  | 31 => 62886
  | 32 => 62914
  | 33 => 62943
  | 34 => 62971
  | 35 => 63000
  | _ => 63000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((62000:ℝ)) ≤ (62029); norm_num
  · show ((62029:ℝ)) ≤ (62057); norm_num
  · show ((62057:ℝ)) ≤ (62086); norm_num
  · show ((62086:ℝ)) ≤ (62114); norm_num
  · show ((62114:ℝ)) ≤ (62143); norm_num
  · show ((62143:ℝ)) ≤ (62171); norm_num
  · show ((62171:ℝ)) ≤ (62200); norm_num
  · show ((62200:ℝ)) ≤ (62229); norm_num
  · show ((62229:ℝ)) ≤ (62257); norm_num
  · show ((62257:ℝ)) ≤ (62286); norm_num
  · show ((62286:ℝ)) ≤ (62314); norm_num
  · show ((62314:ℝ)) ≤ (62343); norm_num
  · show ((62343:ℝ)) ≤ (62371); norm_num
  · show ((62371:ℝ)) ≤ (62400); norm_num
  · show ((62400:ℝ)) ≤ (62429); norm_num
  · show ((62429:ℝ)) ≤ (62457); norm_num
  · show ((62457:ℝ)) ≤ (62486); norm_num
  · show ((62486:ℝ)) ≤ (62514); norm_num
  · show ((62514:ℝ)) ≤ (62543); norm_num
  · show ((62543:ℝ)) ≤ (62571); norm_num
  · show ((62571:ℝ)) ≤ (62600); norm_num
  · show ((62600:ℝ)) ≤ (62629); norm_num
  · show ((62629:ℝ)) ≤ (62657); norm_num
  · show ((62657:ℝ)) ≤ (62686); norm_num
  · show ((62686:ℝ)) ≤ (62714); norm_num
  · show ((62714:ℝ)) ≤ (62743); norm_num
  · show ((62743:ℝ)) ≤ (62771); norm_num
  · show ((62771:ℝ)) ≤ (62800); norm_num
  · show ((62800:ℝ)) ≤ (62829); norm_num
  · show ((62829:ℝ)) ≤ (62857); norm_num
  · show ((62857:ℝ)) ≤ (62886); norm_num
  · show ((62886:ℝ)) ≤ (62914); norm_num
  · show ((62914:ℝ)) ≤ (62943); norm_num
  · show ((62943:ℝ)) ≤ (62971); norm_num
  · show ((62971:ℝ)) ≤ (63000); norm_num
  · show ((63000:ℝ)) ≤ (63000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 62000
  | 1 => 62029
  | 2 => 62057
  | 3 => 62086
  | 4 => 248455 / 4
  | 5 => 62143
  | 6 => 62171
  | 7 => 62200
  | 8 => 62229
  | 9 => 62257
  | 10 => 62286
  | 11 => 62314
  | 12 => 62343
  | 13 => 62371
  | 14 => 62400
  | 15 => 62429
  | 16 => 62457
  | 17 => 62486
  | 18 => 62514
  | 19 => 62543
  | 20 => 62571
  | 21 => 62600
  | 22 => 250515 / 4
  | 23 => 62657
  | 24 => 62686
  | 25 => 62714
  | 26 => 62743
  | 27 => 62771
  | 28 => 62800
  | 29 => 62829
  | 30 => 62857
  | 31 => 62886
  | 32 => 62914
  | 33 => 62943
  | 34 => 62971
  | _ => 62971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 62029
  | 1 => 62057
  | 2 => 248345 / 4
  | 3 => 62114
  | 4 => 62143
  | 5 => 62171
  | 6 => 62200
  | 7 => 62229
  | 8 => 62257
  | 9 => 249145 / 4
  | 10 => 249257 / 4
  | 11 => 62343
  | 12 => 62371
  | 13 => 62400
  | 14 => 62429
  | 15 => 62457
  | 16 => 62486
  | 17 => 62514
  | 18 => 62543
  | 19 => 62571
  | 20 => 62600
  | 21 => 62629
  | 22 => 125315 / 2
  | 23 => 62686
  | 24 => 62714
  | 25 => 62743
  | 26 => 62771
  | 27 => 62800
  | 28 => 62829
  | 29 => 251429 / 4
  | 30 => 62886
  | 31 => 62914
  | 32 => 251773 / 4
  | 33 => 62971
  | 34 => 63000
  | _ => 63000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 63000` (`log 63000 ≤ 12`, `2.7^12 ≥ 63000`). -/
theorem haC_63000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 63000 := by
  have hlog : Real.log 63000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 63000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 63000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[62000, 63000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[62000, 63000]` SEGMENT: every zero with `62000 ≤ Im ≤ 63000` is on the line. -/
theorem segment_62000_63000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 63000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (62000:ℝ) ≤ ρ.im → ρ.im ≤ 63000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 62000 63000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_63000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 63000 via the HEIGHT CHAIN**: `[0,62000]` ∘ `[62000,63000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_63000_of_bands
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
    (hbands_55000 : AllZeros_h55000.BandHyp)
    (hbands_56000 : AllZeros_h56000.BandHyp)
    (hbands_57000 : AllZeros_h57000.BandHyp)
    (hbands_58000 : AllZeros_h58000.BandHyp)
    (hbands_59000 : AllZeros_h59000.BandHyp)
    (hbands_60000 : AllZeros_h60000.BandHyp)
    (hbands_61000 : AllZeros_h61000.BandHyp)
    (hbands_62000 : AllZeros_h62000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 63000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 63000 → ρ.re = 1 / 2 := by
  have hγ62000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 62000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 62000 63000
    (AllZeros_h62000.all_nontrivial_zeros_up_to_height_62000_of_bands
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
      hbands_55000
      hbands_56000
      hbands_57000
      hbands_58000
      hbands_59000
      hbands_60000
      hbands_61000
      hbands_62000
      hγ62000)
    (segment_62000_63000 hbands hγ)

end AllZeros_h63000
