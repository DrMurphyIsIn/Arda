/-  Height-chain step: all nontrivial zeta zeros up to height 54000 on Re = 1/2 --
    `AllZeros_h53000` + a `[53000, 54000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h53000
import RHInBoxT_1d4000000_3999999d4000000_53000_53029
import RHInBoxT_1d4000000_3999999d4000000_53029_212229d4
import RHInBoxT_1d4000000_3999999d4000000_53057_53086
import RHInBoxT_1d4000000_3999999d4000000_53086_53114
import RHInBoxT_1d4000000_3999999d4000000_53114_53143
import RHInBoxT_1d4000000_3999999d4000000_53143_53171
import RHInBoxT_1d4000000_3999999d4000000_53171_53200
import RHInBoxT_1d4000000_3999999d4000000_53200_53229
import RHInBoxT_1d4000000_3999999d4000000_212915d4_53257
import RHInBoxT_1d4000000_3999999d4000000_53257_53286
import RHInBoxT_1d4000000_3999999d4000000_53286_53314
import RHInBoxT_1d4000000_3999999d4000000_53314_53343
import RHInBoxT_1d4000000_3999999d4000000_213371d4_53371
import RHInBoxT_1d4000000_3999999d4000000_53371_53400
import RHInBoxT_1d4000000_3999999d4000000_53400_53429
import RHInBoxT_1d4000000_3999999d4000000_53429_53457
import RHInBoxT_1d4000000_3999999d4000000_53457_53486
import RHInBoxT_1d4000000_3999999d4000000_53486_53514
import RHInBoxT_1d4000000_3999999d4000000_214055d4_53543
import RHInBoxT_1d4000000_3999999d4000000_53543_53571
import RHInBoxT_1d4000000_3999999d4000000_53571_53600
import RHInBoxT_1d4000000_3999999d4000000_53600_53629
import RHInBoxT_1d4000000_3999999d4000000_53629_53657
import RHInBoxT_1d4000000_3999999d4000000_53657_53686
import RHInBoxT_1d4000000_3999999d4000000_53686_53714
import RHInBoxT_1d4000000_3999999d4000000_53714_53743
import RHInBoxT_1d4000000_3999999d4000000_53743_53771
import RHInBoxT_1d4000000_3999999d4000000_53771_53800
import RHInBoxT_1d4000000_3999999d4000000_215199d4_53829
import RHInBoxT_1d4000000_3999999d4000000_53829_53857
import RHInBoxT_1d4000000_3999999d4000000_215427d4_53886
import RHInBoxT_1d4000000_3999999d4000000_53886_53914
import RHInBoxT_1d4000000_3999999d4000000_53914_53943
import RHInBoxT_1d4000000_3999999d4000000_53943_53971
import RHInBoxT_1d4000000_3999999d4000000_53971_54000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h54000

/-- The 35-band NOMINAL partition of `[53000, 54000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 53000
  | 1 => 53029
  | 2 => 53057
  | 3 => 53086
  | 4 => 53114
  | 5 => 53143
  | 6 => 53171
  | 7 => 53200
  | 8 => 53229
  | 9 => 53257
  | 10 => 53286
  | 11 => 53314
  | 12 => 53343
  | 13 => 53371
  | 14 => 53400
  | 15 => 53429
  | 16 => 53457
  | 17 => 53486
  | 18 => 53514
  | 19 => 53543
  | 20 => 53571
  | 21 => 53600
  | 22 => 53629
  | 23 => 53657
  | 24 => 53686
  | 25 => 53714
  | 26 => 53743
  | 27 => 53771
  | 28 => 53800
  | 29 => 53829
  | 30 => 53857
  | 31 => 53886
  | 32 => 53914
  | 33 => 53943
  | 34 => 53971
  | 35 => 54000
  | _ => 54000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((53000:ℝ)) ≤ (53029); norm_num
  · show ((53029:ℝ)) ≤ (53057); norm_num
  · show ((53057:ℝ)) ≤ (53086); norm_num
  · show ((53086:ℝ)) ≤ (53114); norm_num
  · show ((53114:ℝ)) ≤ (53143); norm_num
  · show ((53143:ℝ)) ≤ (53171); norm_num
  · show ((53171:ℝ)) ≤ (53200); norm_num
  · show ((53200:ℝ)) ≤ (53229); norm_num
  · show ((53229:ℝ)) ≤ (53257); norm_num
  · show ((53257:ℝ)) ≤ (53286); norm_num
  · show ((53286:ℝ)) ≤ (53314); norm_num
  · show ((53314:ℝ)) ≤ (53343); norm_num
  · show ((53343:ℝ)) ≤ (53371); norm_num
  · show ((53371:ℝ)) ≤ (53400); norm_num
  · show ((53400:ℝ)) ≤ (53429); norm_num
  · show ((53429:ℝ)) ≤ (53457); norm_num
  · show ((53457:ℝ)) ≤ (53486); norm_num
  · show ((53486:ℝ)) ≤ (53514); norm_num
  · show ((53514:ℝ)) ≤ (53543); norm_num
  · show ((53543:ℝ)) ≤ (53571); norm_num
  · show ((53571:ℝ)) ≤ (53600); norm_num
  · show ((53600:ℝ)) ≤ (53629); norm_num
  · show ((53629:ℝ)) ≤ (53657); norm_num
  · show ((53657:ℝ)) ≤ (53686); norm_num
  · show ((53686:ℝ)) ≤ (53714); norm_num
  · show ((53714:ℝ)) ≤ (53743); norm_num
  · show ((53743:ℝ)) ≤ (53771); norm_num
  · show ((53771:ℝ)) ≤ (53800); norm_num
  · show ((53800:ℝ)) ≤ (53829); norm_num
  · show ((53829:ℝ)) ≤ (53857); norm_num
  · show ((53857:ℝ)) ≤ (53886); norm_num
  · show ((53886:ℝ)) ≤ (53914); norm_num
  · show ((53914:ℝ)) ≤ (53943); norm_num
  · show ((53943:ℝ)) ≤ (53971); norm_num
  · show ((53971:ℝ)) ≤ (54000); norm_num
  · show ((54000:ℝ)) ≤ (54000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 53000
  | 1 => 53029
  | 2 => 53057
  | 3 => 53086
  | 4 => 53114
  | 5 => 53143
  | 6 => 53171
  | 7 => 53200
  | 8 => 212915 / 4
  | 9 => 53257
  | 10 => 53286
  | 11 => 53314
  | 12 => 213371 / 4
  | 13 => 53371
  | 14 => 53400
  | 15 => 53429
  | 16 => 53457
  | 17 => 53486
  | 18 => 214055 / 4
  | 19 => 53543
  | 20 => 53571
  | 21 => 53600
  | 22 => 53629
  | 23 => 53657
  | 24 => 53686
  | 25 => 53714
  | 26 => 53743
  | 27 => 53771
  | 28 => 215199 / 4
  | 29 => 53829
  | 30 => 215427 / 4
  | 31 => 53886
  | 32 => 53914
  | 33 => 53943
  | 34 => 53971
  | _ => 53971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 53029
  | 1 => 212229 / 4
  | 2 => 53086
  | 3 => 53114
  | 4 => 53143
  | 5 => 53171
  | 6 => 53200
  | 7 => 53229
  | 8 => 53257
  | 9 => 53286
  | 10 => 53314
  | 11 => 53343
  | 12 => 53371
  | 13 => 53400
  | 14 => 53429
  | 15 => 53457
  | 16 => 53486
  | 17 => 53514
  | 18 => 53543
  | 19 => 53571
  | 20 => 53600
  | 21 => 53629
  | 22 => 53657
  | 23 => 53686
  | 24 => 53714
  | 25 => 53743
  | 26 => 53771
  | 27 => 53800
  | 28 => 53829
  | 29 => 53857
  | 30 => 53886
  | 31 => 53914
  | 32 => 53943
  | 33 => 53971
  | 34 => 54000
  | _ => 54000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 54000` (`log 54000 ≤ 11`, `2.7^11 ≥ 54000`). -/
theorem haC_54000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 54000 := by
  have hlog : Real.log 54000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 54000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 54000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[53000, 54000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[53000, 54000]` SEGMENT: every zero with `53000 ≤ Im ≤ 54000` is on the line. -/
theorem segment_53000_54000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 54000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (53000:ℝ) ≤ ρ.im → ρ.im ≤ 54000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 53000 54000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_54000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 54000 via the HEIGHT CHAIN**: `[0,53000]` ∘ `[53000,54000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_54000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 54000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 54000 → ρ.re = 1 / 2 := by
  have hγ53000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 53000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 53000 54000
    (AllZeros_h53000.all_nontrivial_zeros_up_to_height_53000_of_bands
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
      hγ53000)
    (segment_53000_54000 hbands hγ)

end AllZeros_h54000
