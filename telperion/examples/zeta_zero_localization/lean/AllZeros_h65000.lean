/-  Height-chain step: all nontrivial zeta zeros up to height 65000 on Re = 1/2 --
    `AllZeros_h64000` + a `[64000, 65000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h64000
import RHInBoxT_1d4000000_3999999d4000000_64000_64029
import RHInBoxT_1d4000000_3999999d4000000_64029_64057
import RHInBoxT_1d4000000_3999999d4000000_64057_64086
import RHInBoxT_1d4000000_3999999d4000000_64086_64114
import RHInBoxT_1d4000000_3999999d4000000_64114_256573d4
import RHInBoxT_1d4000000_3999999d4000000_64143_64171
import RHInBoxT_1d4000000_3999999d4000000_64171_64200
import RHInBoxT_1d4000000_3999999d4000000_64200_64229
import RHInBoxT_1d4000000_3999999d4000000_64229_64257
import RHInBoxT_1d4000000_3999999d4000000_64257_64286
import RHInBoxT_1d4000000_3999999d4000000_64286_64314
import RHInBoxT_1d4000000_3999999d4000000_257255d4_64343
import RHInBoxT_1d4000000_3999999d4000000_64343_257485d4
import RHInBoxT_1d4000000_3999999d4000000_64371_64400
import RHInBoxT_1d4000000_3999999d4000000_257599d4_64429
import RHInBoxT_1d4000000_3999999d4000000_64429_64457
import RHInBoxT_1d4000000_3999999d4000000_64457_64486
import RHInBoxT_1d4000000_3999999d4000000_64486_64514
import RHInBoxT_1d4000000_3999999d4000000_64514_64543
import RHInBoxT_1d4000000_3999999d4000000_64543_64571
import RHInBoxT_1d4000000_3999999d4000000_64571_64600
import RHInBoxT_1d4000000_3999999d4000000_64600_64629
import RHInBoxT_1d4000000_3999999d4000000_64629_64657
import RHInBoxT_1d4000000_3999999d4000000_64657_64686
import RHInBoxT_1d4000000_3999999d4000000_64686_64714
import RHInBoxT_1d4000000_3999999d4000000_64714_64743
import RHInBoxT_1d4000000_3999999d4000000_64743_64771
import RHInBoxT_1d4000000_3999999d4000000_64771_64800
import RHInBoxT_1d4000000_3999999d4000000_64800_64829
import RHInBoxT_1d4000000_3999999d4000000_64829_64857
import RHInBoxT_1d4000000_3999999d4000000_64857_64886
import RHInBoxT_1d4000000_3999999d4000000_64886_64914
import RHInBoxT_1d4000000_3999999d4000000_64914_64943
import RHInBoxT_1d4000000_3999999d4000000_64943_259885d4
import RHInBoxT_1d4000000_3999999d4000000_64971_260001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h65000

/-- The 35-band NOMINAL partition of `[64000, 65000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 64000
  | 1 => 64029
  | 2 => 64057
  | 3 => 64086
  | 4 => 64114
  | 5 => 64143
  | 6 => 64171
  | 7 => 64200
  | 8 => 64229
  | 9 => 64257
  | 10 => 64286
  | 11 => 64314
  | 12 => 64343
  | 13 => 64371
  | 14 => 64400
  | 15 => 64429
  | 16 => 64457
  | 17 => 64486
  | 18 => 64514
  | 19 => 64543
  | 20 => 64571
  | 21 => 64600
  | 22 => 64629
  | 23 => 64657
  | 24 => 64686
  | 25 => 64714
  | 26 => 64743
  | 27 => 64771
  | 28 => 64800
  | 29 => 64829
  | 30 => 64857
  | 31 => 64886
  | 32 => 64914
  | 33 => 64943
  | 34 => 64971
  | 35 => 65000
  | _ => 65000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((64000:ℝ)) ≤ (64029); norm_num
  · show ((64029:ℝ)) ≤ (64057); norm_num
  · show ((64057:ℝ)) ≤ (64086); norm_num
  · show ((64086:ℝ)) ≤ (64114); norm_num
  · show ((64114:ℝ)) ≤ (64143); norm_num
  · show ((64143:ℝ)) ≤ (64171); norm_num
  · show ((64171:ℝ)) ≤ (64200); norm_num
  · show ((64200:ℝ)) ≤ (64229); norm_num
  · show ((64229:ℝ)) ≤ (64257); norm_num
  · show ((64257:ℝ)) ≤ (64286); norm_num
  · show ((64286:ℝ)) ≤ (64314); norm_num
  · show ((64314:ℝ)) ≤ (64343); norm_num
  · show ((64343:ℝ)) ≤ (64371); norm_num
  · show ((64371:ℝ)) ≤ (64400); norm_num
  · show ((64400:ℝ)) ≤ (64429); norm_num
  · show ((64429:ℝ)) ≤ (64457); norm_num
  · show ((64457:ℝ)) ≤ (64486); norm_num
  · show ((64486:ℝ)) ≤ (64514); norm_num
  · show ((64514:ℝ)) ≤ (64543); norm_num
  · show ((64543:ℝ)) ≤ (64571); norm_num
  · show ((64571:ℝ)) ≤ (64600); norm_num
  · show ((64600:ℝ)) ≤ (64629); norm_num
  · show ((64629:ℝ)) ≤ (64657); norm_num
  · show ((64657:ℝ)) ≤ (64686); norm_num
  · show ((64686:ℝ)) ≤ (64714); norm_num
  · show ((64714:ℝ)) ≤ (64743); norm_num
  · show ((64743:ℝ)) ≤ (64771); norm_num
  · show ((64771:ℝ)) ≤ (64800); norm_num
  · show ((64800:ℝ)) ≤ (64829); norm_num
  · show ((64829:ℝ)) ≤ (64857); norm_num
  · show ((64857:ℝ)) ≤ (64886); norm_num
  · show ((64886:ℝ)) ≤ (64914); norm_num
  · show ((64914:ℝ)) ≤ (64943); norm_num
  · show ((64943:ℝ)) ≤ (64971); norm_num
  · show ((64971:ℝ)) ≤ (65000); norm_num
  · show ((65000:ℝ)) ≤ (65000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 64000
  | 1 => 64029
  | 2 => 64057
  | 3 => 64086
  | 4 => 64114
  | 5 => 64143
  | 6 => 64171
  | 7 => 64200
  | 8 => 64229
  | 9 => 64257
  | 10 => 64286
  | 11 => 257255 / 4
  | 12 => 64343
  | 13 => 64371
  | 14 => 257599 / 4
  | 15 => 64429
  | 16 => 64457
  | 17 => 64486
  | 18 => 64514
  | 19 => 64543
  | 20 => 64571
  | 21 => 64600
  | 22 => 64629
  | 23 => 64657
  | 24 => 64686
  | 25 => 64714
  | 26 => 64743
  | 27 => 64771
  | 28 => 64800
  | 29 => 64829
  | 30 => 64857
  | 31 => 64886
  | 32 => 64914
  | 33 => 64943
  | 34 => 64971
  | _ => 64971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 64029
  | 1 => 64057
  | 2 => 64086
  | 3 => 64114
  | 4 => 256573 / 4
  | 5 => 64171
  | 6 => 64200
  | 7 => 64229
  | 8 => 64257
  | 9 => 64286
  | 10 => 64314
  | 11 => 64343
  | 12 => 257485 / 4
  | 13 => 64400
  | 14 => 64429
  | 15 => 64457
  | 16 => 64486
  | 17 => 64514
  | 18 => 64543
  | 19 => 64571
  | 20 => 64600
  | 21 => 64629
  | 22 => 64657
  | 23 => 64686
  | 24 => 64714
  | 25 => 64743
  | 26 => 64771
  | 27 => 64800
  | 28 => 64829
  | 29 => 64857
  | 30 => 64886
  | 31 => 64914
  | 32 => 64943
  | 33 => 259885 / 4
  | 34 => 260001 / 4
  | _ => 260001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 65000` (`log 65000 ≤ 12`, `2.7^12 ≥ 65000`). -/
theorem haC_65000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 65000 := by
  have hlog : Real.log 65000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 65000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 65000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[64000, 65000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[64000, 65000]` SEGMENT: every zero with `64000 ≤ Im ≤ 65000` is on the line. -/
theorem segment_64000_65000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 65000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (64000:ℝ) ≤ ρ.im → ρ.im ≤ 65000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 64000 65000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_65000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 65000 via the HEIGHT CHAIN**: `[0,64000]` ∘ `[64000,65000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_65000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 65000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 65000 → ρ.re = 1 / 2 := by
  have hγ64000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 64000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 64000 65000
    (AllZeros_h64000.all_nontrivial_zeros_up_to_height_64000_of_bands
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
      hγ64000)
    (segment_64000_65000 hbands hγ)

end AllZeros_h65000
