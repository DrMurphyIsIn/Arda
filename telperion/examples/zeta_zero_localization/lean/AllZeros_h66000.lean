/-  Height-chain step: all nontrivial zeta zeros up to height 66000 on Re = 1/2 --
    `AllZeros_h65000` + a `[65000, 66000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h65000
import RHInBoxT_1d4000000_3999999d4000000_65000_65029
import RHInBoxT_1d4000000_3999999d4000000_65029_65057
import RHInBoxT_1d4000000_3999999d4000000_65057_65086
import RHInBoxT_1d4000000_3999999d4000000_65086_65114
import RHInBoxT_1d4000000_3999999d4000000_65114_65143
import RHInBoxT_1d4000000_3999999d4000000_260571d4_65171
import RHInBoxT_1d4000000_3999999d4000000_65171_65200
import RHInBoxT_1d4000000_3999999d4000000_260799d4_260917d4
import RHInBoxT_1d4000000_3999999d4000000_65229_65257
import RHInBoxT_1d4000000_3999999d4000000_65257_65286
import RHInBoxT_1d4000000_3999999d4000000_261143d4_65314
import RHInBoxT_1d4000000_3999999d4000000_65314_65343
import RHInBoxT_1d4000000_3999999d4000000_65343_65371
import RHInBoxT_1d4000000_3999999d4000000_65371_65400
import RHInBoxT_1d4000000_3999999d4000000_65400_65429
import RHInBoxT_1d4000000_3999999d4000000_65429_65457
import RHInBoxT_1d4000000_3999999d4000000_65457_65486
import RHInBoxT_1d4000000_3999999d4000000_65486_65514
import RHInBoxT_1d4000000_3999999d4000000_65514_65543
import RHInBoxT_1d4000000_3999999d4000000_65543_65571
import RHInBoxT_1d4000000_3999999d4000000_65571_262401d4
import RHInBoxT_1d4000000_3999999d4000000_65600_65629
import RHInBoxT_1d4000000_3999999d4000000_65629_65657
import RHInBoxT_1d4000000_3999999d4000000_65657_65686
import RHInBoxT_1d4000000_3999999d4000000_262743d4_65714
import RHInBoxT_1d4000000_3999999d4000000_262855d4_65743
import RHInBoxT_1d4000000_3999999d4000000_65743_65771
import RHInBoxT_1d4000000_3999999d4000000_65771_65800
import RHInBoxT_1d4000000_3999999d4000000_65800_65829
import RHInBoxT_1d4000000_3999999d4000000_65829_65857
import RHInBoxT_1d4000000_3999999d4000000_263427d4_65886
import RHInBoxT_1d4000000_3999999d4000000_65886_65914
import RHInBoxT_1d4000000_3999999d4000000_65914_263773d4
import RHInBoxT_1d4000000_3999999d4000000_65943_65971
import RHInBoxT_1d4000000_3999999d4000000_65971_66000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h66000

/-- The 35-band NOMINAL partition of `[65000, 66000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 65000
  | 1 => 65029
  | 2 => 65057
  | 3 => 65086
  | 4 => 65114
  | 5 => 65143
  | 6 => 65171
  | 7 => 65200
  | 8 => 65229
  | 9 => 65257
  | 10 => 65286
  | 11 => 65314
  | 12 => 65343
  | 13 => 65371
  | 14 => 65400
  | 15 => 65429
  | 16 => 65457
  | 17 => 65486
  | 18 => 65514
  | 19 => 65543
  | 20 => 65571
  | 21 => 65600
  | 22 => 65629
  | 23 => 65657
  | 24 => 65686
  | 25 => 65714
  | 26 => 65743
  | 27 => 65771
  | 28 => 65800
  | 29 => 65829
  | 30 => 65857
  | 31 => 65886
  | 32 => 65914
  | 33 => 65943
  | 34 => 65971
  | 35 => 66000
  | _ => 66000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((65000:ℝ)) ≤ (65029); norm_num
  · show ((65029:ℝ)) ≤ (65057); norm_num
  · show ((65057:ℝ)) ≤ (65086); norm_num
  · show ((65086:ℝ)) ≤ (65114); norm_num
  · show ((65114:ℝ)) ≤ (65143); norm_num
  · show ((65143:ℝ)) ≤ (65171); norm_num
  · show ((65171:ℝ)) ≤ (65200); norm_num
  · show ((65200:ℝ)) ≤ (65229); norm_num
  · show ((65229:ℝ)) ≤ (65257); norm_num
  · show ((65257:ℝ)) ≤ (65286); norm_num
  · show ((65286:ℝ)) ≤ (65314); norm_num
  · show ((65314:ℝ)) ≤ (65343); norm_num
  · show ((65343:ℝ)) ≤ (65371); norm_num
  · show ((65371:ℝ)) ≤ (65400); norm_num
  · show ((65400:ℝ)) ≤ (65429); norm_num
  · show ((65429:ℝ)) ≤ (65457); norm_num
  · show ((65457:ℝ)) ≤ (65486); norm_num
  · show ((65486:ℝ)) ≤ (65514); norm_num
  · show ((65514:ℝ)) ≤ (65543); norm_num
  · show ((65543:ℝ)) ≤ (65571); norm_num
  · show ((65571:ℝ)) ≤ (65600); norm_num
  · show ((65600:ℝ)) ≤ (65629); norm_num
  · show ((65629:ℝ)) ≤ (65657); norm_num
  · show ((65657:ℝ)) ≤ (65686); norm_num
  · show ((65686:ℝ)) ≤ (65714); norm_num
  · show ((65714:ℝ)) ≤ (65743); norm_num
  · show ((65743:ℝ)) ≤ (65771); norm_num
  · show ((65771:ℝ)) ≤ (65800); norm_num
  · show ((65800:ℝ)) ≤ (65829); norm_num
  · show ((65829:ℝ)) ≤ (65857); norm_num
  · show ((65857:ℝ)) ≤ (65886); norm_num
  · show ((65886:ℝ)) ≤ (65914); norm_num
  · show ((65914:ℝ)) ≤ (65943); norm_num
  · show ((65943:ℝ)) ≤ (65971); norm_num
  · show ((65971:ℝ)) ≤ (66000); norm_num
  · show ((66000:ℝ)) ≤ (66000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 65000
  | 1 => 65029
  | 2 => 65057
  | 3 => 65086
  | 4 => 65114
  | 5 => 260571 / 4
  | 6 => 65171
  | 7 => 260799 / 4
  | 8 => 65229
  | 9 => 65257
  | 10 => 261143 / 4
  | 11 => 65314
  | 12 => 65343
  | 13 => 65371
  | 14 => 65400
  | 15 => 65429
  | 16 => 65457
  | 17 => 65486
  | 18 => 65514
  | 19 => 65543
  | 20 => 65571
  | 21 => 65600
  | 22 => 65629
  | 23 => 65657
  | 24 => 262743 / 4
  | 25 => 262855 / 4
  | 26 => 65743
  | 27 => 65771
  | 28 => 65800
  | 29 => 65829
  | 30 => 263427 / 4
  | 31 => 65886
  | 32 => 65914
  | 33 => 65943
  | 34 => 65971
  | _ => 65971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 65029
  | 1 => 65057
  | 2 => 65086
  | 3 => 65114
  | 4 => 65143
  | 5 => 65171
  | 6 => 65200
  | 7 => 260917 / 4
  | 8 => 65257
  | 9 => 65286
  | 10 => 65314
  | 11 => 65343
  | 12 => 65371
  | 13 => 65400
  | 14 => 65429
  | 15 => 65457
  | 16 => 65486
  | 17 => 65514
  | 18 => 65543
  | 19 => 65571
  | 20 => 262401 / 4
  | 21 => 65629
  | 22 => 65657
  | 23 => 65686
  | 24 => 65714
  | 25 => 65743
  | 26 => 65771
  | 27 => 65800
  | 28 => 65829
  | 29 => 65857
  | 30 => 65886
  | 31 => 65914
  | 32 => 263773 / 4
  | 33 => 65971
  | 34 => 66000
  | _ => 66000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 66000` (`log 66000 ≤ 12`, `2.7^12 ≥ 66000`). -/
theorem haC_66000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 66000 := by
  have hlog : Real.log 66000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 66000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 66000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[65000, 66000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[65000, 66000]` SEGMENT: every zero with `65000 ≤ Im ≤ 66000` is on the line. -/
theorem segment_65000_66000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 66000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (65000:ℝ) ≤ ρ.im → ρ.im ≤ 66000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 65000 66000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_66000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 66000 via the HEIGHT CHAIN**: `[0,65000]` ∘ `[65000,66000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_66000_of_bands
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
    (hbands_63000 : AllZeros_h63000.BandHyp)
    (hbands_64000 : AllZeros_h64000.BandHyp)
    (hbands_65000 : AllZeros_h65000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 66000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 66000 → ρ.re = 1 / 2 := by
  have hγ65000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 65000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 65000 66000
    (AllZeros_h65000.all_nontrivial_zeros_up_to_height_65000_of_bands
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
      hbands_63000
      hbands_64000
      hbands_65000
      hγ65000)
    (segment_65000_66000 hbands hγ)

end AllZeros_h66000
