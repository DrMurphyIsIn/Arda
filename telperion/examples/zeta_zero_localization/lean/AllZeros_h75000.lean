/-  Height-chain step: all nontrivial zeta zeros up to height 75000 on Re = 1/2 --
    `AllZeros_h74000` + a `[74000, 75000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h74000
import RHInBoxT_1d4000000_3999999d4000000_74000_74028
import RHInBoxT_1d4000000_3999999d4000000_74028_74056
import RHInBoxT_1d4000000_3999999d4000000_74056_74083
import RHInBoxT_1d4000000_3999999d4000000_74083_74111
import RHInBoxT_1d4000000_3999999d4000000_74111_74139
import RHInBoxT_1d4000000_3999999d4000000_296555d4_74167
import RHInBoxT_1d4000000_3999999d4000000_74167_74194
import RHInBoxT_1d4000000_3999999d4000000_74194_74222
import RHInBoxT_1d4000000_3999999d4000000_74222_74250
import RHInBoxT_1d4000000_3999999d4000000_74250_74278
import RHInBoxT_1d4000000_3999999d4000000_74278_74306
import RHInBoxT_1d4000000_3999999d4000000_74306_74333
import RHInBoxT_1d4000000_3999999d4000000_74333_297445d4
import RHInBoxT_1d4000000_3999999d4000000_74361_297557d4
import RHInBoxT_1d4000000_3999999d4000000_74389_74417
import RHInBoxT_1d4000000_3999999d4000000_74417_74444
import RHInBoxT_1d4000000_3999999d4000000_297775d4_74472
import RHInBoxT_1d4000000_3999999d4000000_74472_74500
import RHInBoxT_1d4000000_3999999d4000000_74500_298113d4
import RHInBoxT_1d4000000_3999999d4000000_74528_74556
import RHInBoxT_1d4000000_3999999d4000000_298223d4_74583
import RHInBoxT_1d4000000_3999999d4000000_74583_74611
import RHInBoxT_1d4000000_3999999d4000000_74611_74639
import RHInBoxT_1d4000000_3999999d4000000_74639_74667
import RHInBoxT_1d4000000_3999999d4000000_74667_74694
import RHInBoxT_1d4000000_3999999d4000000_74694_74722
import RHInBoxT_1d4000000_3999999d4000000_74722_74750
import RHInBoxT_1d4000000_3999999d4000000_298999d4_74778
import RHInBoxT_1d4000000_3999999d4000000_74778_299225d4
import RHInBoxT_1d4000000_3999999d4000000_74806_299333d4
import RHInBoxT_1d4000000_3999999d4000000_74833_74861
import RHInBoxT_1d4000000_3999999d4000000_74861_74889
import RHInBoxT_1d4000000_3999999d4000000_74889_74917
import RHInBoxT_1d4000000_3999999d4000000_74917_74944
import RHInBoxT_1d4000000_3999999d4000000_74944_74972
import RHInBoxT_1d4000000_3999999d4000000_74972_75000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h75000

/-- The 36-band NOMINAL partition of `[74000, 75000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 74000
  | 1 => 74028
  | 2 => 74056
  | 3 => 74083
  | 4 => 74111
  | 5 => 74139
  | 6 => 74167
  | 7 => 74194
  | 8 => 74222
  | 9 => 74250
  | 10 => 74278
  | 11 => 74306
  | 12 => 74333
  | 13 => 74361
  | 14 => 74389
  | 15 => 74417
  | 16 => 74444
  | 17 => 74472
  | 18 => 74500
  | 19 => 74528
  | 20 => 74556
  | 21 => 74583
  | 22 => 74611
  | 23 => 74639
  | 24 => 74667
  | 25 => 74694
  | 26 => 74722
  | 27 => 74750
  | 28 => 74778
  | 29 => 74806
  | 30 => 74833
  | 31 => 74861
  | 32 => 74889
  | 33 => 74917
  | 34 => 74944
  | 35 => 74972
  | 36 => 75000
  | _ => 75000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((74000:ℝ)) ≤ (74028); norm_num
  · show ((74028:ℝ)) ≤ (74056); norm_num
  · show ((74056:ℝ)) ≤ (74083); norm_num
  · show ((74083:ℝ)) ≤ (74111); norm_num
  · show ((74111:ℝ)) ≤ (74139); norm_num
  · show ((74139:ℝ)) ≤ (74167); norm_num
  · show ((74167:ℝ)) ≤ (74194); norm_num
  · show ((74194:ℝ)) ≤ (74222); norm_num
  · show ((74222:ℝ)) ≤ (74250); norm_num
  · show ((74250:ℝ)) ≤ (74278); norm_num
  · show ((74278:ℝ)) ≤ (74306); norm_num
  · show ((74306:ℝ)) ≤ (74333); norm_num
  · show ((74333:ℝ)) ≤ (74361); norm_num
  · show ((74361:ℝ)) ≤ (74389); norm_num
  · show ((74389:ℝ)) ≤ (74417); norm_num
  · show ((74417:ℝ)) ≤ (74444); norm_num
  · show ((74444:ℝ)) ≤ (74472); norm_num
  · show ((74472:ℝ)) ≤ (74500); norm_num
  · show ((74500:ℝ)) ≤ (74528); norm_num
  · show ((74528:ℝ)) ≤ (74556); norm_num
  · show ((74556:ℝ)) ≤ (74583); norm_num
  · show ((74583:ℝ)) ≤ (74611); norm_num
  · show ((74611:ℝ)) ≤ (74639); norm_num
  · show ((74639:ℝ)) ≤ (74667); norm_num
  · show ((74667:ℝ)) ≤ (74694); norm_num
  · show ((74694:ℝ)) ≤ (74722); norm_num
  · show ((74722:ℝ)) ≤ (74750); norm_num
  · show ((74750:ℝ)) ≤ (74778); norm_num
  · show ((74778:ℝ)) ≤ (74806); norm_num
  · show ((74806:ℝ)) ≤ (74833); norm_num
  · show ((74833:ℝ)) ≤ (74861); norm_num
  · show ((74861:ℝ)) ≤ (74889); norm_num
  · show ((74889:ℝ)) ≤ (74917); norm_num
  · show ((74917:ℝ)) ≤ (74944); norm_num
  · show ((74944:ℝ)) ≤ (74972); norm_num
  · show ((74972:ℝ)) ≤ (75000); norm_num
  · show ((75000:ℝ)) ≤ (75000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 74000
  | 1 => 74028
  | 2 => 74056
  | 3 => 74083
  | 4 => 74111
  | 5 => 296555 / 4
  | 6 => 74167
  | 7 => 74194
  | 8 => 74222
  | 9 => 74250
  | 10 => 74278
  | 11 => 74306
  | 12 => 74333
  | 13 => 74361
  | 14 => 74389
  | 15 => 74417
  | 16 => 297775 / 4
  | 17 => 74472
  | 18 => 74500
  | 19 => 74528
  | 20 => 298223 / 4
  | 21 => 74583
  | 22 => 74611
  | 23 => 74639
  | 24 => 74667
  | 25 => 74694
  | 26 => 74722
  | 27 => 298999 / 4
  | 28 => 74778
  | 29 => 74806
  | 30 => 74833
  | 31 => 74861
  | 32 => 74889
  | 33 => 74917
  | 34 => 74944
  | 35 => 74972
  | _ => 74972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 74028
  | 1 => 74056
  | 2 => 74083
  | 3 => 74111
  | 4 => 74139
  | 5 => 74167
  | 6 => 74194
  | 7 => 74222
  | 8 => 74250
  | 9 => 74278
  | 10 => 74306
  | 11 => 74333
  | 12 => 297445 / 4
  | 13 => 297557 / 4
  | 14 => 74417
  | 15 => 74444
  | 16 => 74472
  | 17 => 74500
  | 18 => 298113 / 4
  | 19 => 74556
  | 20 => 74583
  | 21 => 74611
  | 22 => 74639
  | 23 => 74667
  | 24 => 74694
  | 25 => 74722
  | 26 => 74750
  | 27 => 74778
  | 28 => 299225 / 4
  | 29 => 299333 / 4
  | 30 => 74861
  | 31 => 74889
  | 32 => 74917
  | 33 => 74944
  | 34 => 74972
  | 35 => 75000
  | _ => 75000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 75000` (`log 75000 ≤ 12`, `2.7^12 ≥ 75000`). -/
theorem haC_75000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 75000 := by
  have hlog : Real.log 75000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 75000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 75000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[74000, 75000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[74000, 75000]` SEGMENT: every zero with `74000 ≤ Im ≤ 75000` is on the line. -/
theorem segment_74000_75000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 75000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (74000:ℝ) ≤ ρ.im → ρ.im ≤ 75000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 74000 75000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_75000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 75000 via the HEIGHT CHAIN**: `[0,74000]` ∘ `[74000,75000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_75000_of_bands
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
    (hbands_66000 : AllZeros_h66000.BandHyp)
    (hbands_67000 : AllZeros_h67000.BandHyp)
    (hbands_68000 : AllZeros_h68000.BandHyp)
    (hbands_69000 : AllZeros_h69000.BandHyp)
    (hbands_70000 : AllZeros_h70000.BandHyp)
    (hbands_71000 : AllZeros_h71000.BandHyp)
    (hbands_72000 : AllZeros_h72000.BandHyp)
    (hbands_73000 : AllZeros_h73000.BandHyp)
    (hbands_74000 : AllZeros_h74000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 75000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 75000 → ρ.re = 1 / 2 := by
  have hγ74000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 74000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 74000 75000
    (AllZeros_h74000.all_nontrivial_zeros_up_to_height_74000_of_bands
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
      hbands_66000
      hbands_67000
      hbands_68000
      hbands_69000
      hbands_70000
      hbands_71000
      hbands_72000
      hbands_73000
      hbands_74000
      hγ74000)
    (segment_74000_75000 hbands hγ)

end AllZeros_h75000
