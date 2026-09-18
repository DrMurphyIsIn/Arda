/-  Height-chain step: all nontrivial zeta zeros up to height 79000 on Re = 1/2 --
    `AllZeros_h78000` + a `[78000, 79000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h78000
import RHInBoxT_1d4000000_3999999d4000000_78000_78028
import RHInBoxT_1d4000000_3999999d4000000_78028_78056
import RHInBoxT_1d4000000_3999999d4000000_78056_78083
import RHInBoxT_1d4000000_3999999d4000000_78083_78111
import RHInBoxT_1d4000000_3999999d4000000_78111_78139
import RHInBoxT_1d4000000_3999999d4000000_312555d4_312669d4
import RHInBoxT_1d4000000_3999999d4000000_78167_78194
import RHInBoxT_1d4000000_3999999d4000000_78194_78222
import RHInBoxT_1d4000000_3999999d4000000_78222_78250
import RHInBoxT_1d4000000_3999999d4000000_78250_78278
import RHInBoxT_1d4000000_3999999d4000000_78278_78306
import RHInBoxT_1d4000000_3999999d4000000_313223d4_78333
import RHInBoxT_1d4000000_3999999d4000000_78333_78361
import RHInBoxT_1d4000000_3999999d4000000_78361_156779d2
import RHInBoxT_1d4000000_3999999d4000000_78389_78417
import RHInBoxT_1d4000000_3999999d4000000_313667d4_78444
import RHInBoxT_1d4000000_3999999d4000000_78444_313889d4
import RHInBoxT_1d4000000_3999999d4000000_78472_78500
import RHInBoxT_1d4000000_3999999d4000000_78500_78528
import RHInBoxT_1d4000000_3999999d4000000_78528_78556
import RHInBoxT_1d4000000_3999999d4000000_78556_78583
import RHInBoxT_1d4000000_3999999d4000000_78583_78611
import RHInBoxT_1d4000000_3999999d4000000_78611_78639
import RHInBoxT_1d4000000_3999999d4000000_78639_314669d4
import RHInBoxT_1d4000000_3999999d4000000_78667_78694
import RHInBoxT_1d4000000_3999999d4000000_78694_78722
import RHInBoxT_1d4000000_3999999d4000000_314887d4_78750
import RHInBoxT_1d4000000_3999999d4000000_78750_78778
import RHInBoxT_1d4000000_3999999d4000000_78778_78806
import RHInBoxT_1d4000000_3999999d4000000_78806_78833
import RHInBoxT_1d4000000_3999999d4000000_78833_78861
import RHInBoxT_1d4000000_3999999d4000000_78861_78889
import RHInBoxT_1d4000000_3999999d4000000_78889_78917
import RHInBoxT_1d4000000_3999999d4000000_78917_78944
import RHInBoxT_1d4000000_3999999d4000000_78944_78972
import RHInBoxT_1d4000000_3999999d4000000_315887d4_79000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h79000

/-- The 36-band NOMINAL partition of `[78000, 79000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 78000
  | 1 => 78028
  | 2 => 78056
  | 3 => 78083
  | 4 => 78111
  | 5 => 78139
  | 6 => 78167
  | 7 => 78194
  | 8 => 78222
  | 9 => 78250
  | 10 => 78278
  | 11 => 78306
  | 12 => 78333
  | 13 => 78361
  | 14 => 78389
  | 15 => 78417
  | 16 => 78444
  | 17 => 78472
  | 18 => 78500
  | 19 => 78528
  | 20 => 78556
  | 21 => 78583
  | 22 => 78611
  | 23 => 78639
  | 24 => 78667
  | 25 => 78694
  | 26 => 78722
  | 27 => 78750
  | 28 => 78778
  | 29 => 78806
  | 30 => 78833
  | 31 => 78861
  | 32 => 78889
  | 33 => 78917
  | 34 => 78944
  | 35 => 78972
  | 36 => 79000
  | _ => 79000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((78000:ℝ)) ≤ (78028); norm_num
  · show ((78028:ℝ)) ≤ (78056); norm_num
  · show ((78056:ℝ)) ≤ (78083); norm_num
  · show ((78083:ℝ)) ≤ (78111); norm_num
  · show ((78111:ℝ)) ≤ (78139); norm_num
  · show ((78139:ℝ)) ≤ (78167); norm_num
  · show ((78167:ℝ)) ≤ (78194); norm_num
  · show ((78194:ℝ)) ≤ (78222); norm_num
  · show ((78222:ℝ)) ≤ (78250); norm_num
  · show ((78250:ℝ)) ≤ (78278); norm_num
  · show ((78278:ℝ)) ≤ (78306); norm_num
  · show ((78306:ℝ)) ≤ (78333); norm_num
  · show ((78333:ℝ)) ≤ (78361); norm_num
  · show ((78361:ℝ)) ≤ (78389); norm_num
  · show ((78389:ℝ)) ≤ (78417); norm_num
  · show ((78417:ℝ)) ≤ (78444); norm_num
  · show ((78444:ℝ)) ≤ (78472); norm_num
  · show ((78472:ℝ)) ≤ (78500); norm_num
  · show ((78500:ℝ)) ≤ (78528); norm_num
  · show ((78528:ℝ)) ≤ (78556); norm_num
  · show ((78556:ℝ)) ≤ (78583); norm_num
  · show ((78583:ℝ)) ≤ (78611); norm_num
  · show ((78611:ℝ)) ≤ (78639); norm_num
  · show ((78639:ℝ)) ≤ (78667); norm_num
  · show ((78667:ℝ)) ≤ (78694); norm_num
  · show ((78694:ℝ)) ≤ (78722); norm_num
  · show ((78722:ℝ)) ≤ (78750); norm_num
  · show ((78750:ℝ)) ≤ (78778); norm_num
  · show ((78778:ℝ)) ≤ (78806); norm_num
  · show ((78806:ℝ)) ≤ (78833); norm_num
  · show ((78833:ℝ)) ≤ (78861); norm_num
  · show ((78861:ℝ)) ≤ (78889); norm_num
  · show ((78889:ℝ)) ≤ (78917); norm_num
  · show ((78917:ℝ)) ≤ (78944); norm_num
  · show ((78944:ℝ)) ≤ (78972); norm_num
  · show ((78972:ℝ)) ≤ (79000); norm_num
  · show ((79000:ℝ)) ≤ (79000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 78000
  | 1 => 78028
  | 2 => 78056
  | 3 => 78083
  | 4 => 78111
  | 5 => 312555 / 4
  | 6 => 78167
  | 7 => 78194
  | 8 => 78222
  | 9 => 78250
  | 10 => 78278
  | 11 => 313223 / 4
  | 12 => 78333
  | 13 => 78361
  | 14 => 78389
  | 15 => 313667 / 4
  | 16 => 78444
  | 17 => 78472
  | 18 => 78500
  | 19 => 78528
  | 20 => 78556
  | 21 => 78583
  | 22 => 78611
  | 23 => 78639
  | 24 => 78667
  | 25 => 78694
  | 26 => 314887 / 4
  | 27 => 78750
  | 28 => 78778
  | 29 => 78806
  | 30 => 78833
  | 31 => 78861
  | 32 => 78889
  | 33 => 78917
  | 34 => 78944
  | 35 => 315887 / 4
  | _ => 315887 / 4

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 78028
  | 1 => 78056
  | 2 => 78083
  | 3 => 78111
  | 4 => 78139
  | 5 => 312669 / 4
  | 6 => 78194
  | 7 => 78222
  | 8 => 78250
  | 9 => 78278
  | 10 => 78306
  | 11 => 78333
  | 12 => 78361
  | 13 => 156779 / 2
  | 14 => 78417
  | 15 => 78444
  | 16 => 313889 / 4
  | 17 => 78500
  | 18 => 78528
  | 19 => 78556
  | 20 => 78583
  | 21 => 78611
  | 22 => 78639
  | 23 => 314669 / 4
  | 24 => 78694
  | 25 => 78722
  | 26 => 78750
  | 27 => 78778
  | 28 => 78806
  | 29 => 78833
  | 30 => 78861
  | 31 => 78889
  | 32 => 78917
  | 33 => 78944
  | 34 => 78972
  | 35 => 79000
  | _ => 79000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 79000` (`log 79000 ≤ 12`, `2.7^12 ≥ 79000`). -/
theorem haC_79000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 79000 := by
  have hlog : Real.log 79000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 79000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 79000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[78000, 79000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[78000, 79000]` SEGMENT: every zero with `78000 ≤ Im ≤ 79000` is on the line. -/
theorem segment_78000_79000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 79000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (78000:ℝ) ≤ ρ.im → ρ.im ≤ 79000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 78000 79000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_79000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 79000 via the HEIGHT CHAIN**: `[0,78000]` ∘ `[78000,79000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_79000_of_bands
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
    (hbands_75000 : AllZeros_h75000.BandHyp)
    (hbands_76000 : AllZeros_h76000.BandHyp)
    (hbands_77000 : AllZeros_h77000.BandHyp)
    (hbands_78000 : AllZeros_h78000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 79000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 79000 → ρ.re = 1 / 2 := by
  have hγ78000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 78000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 78000 79000
    (AllZeros_h78000.all_nontrivial_zeros_up_to_height_78000_of_bands
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
      hbands_75000
      hbands_76000
      hbands_77000
      hbands_78000
      hγ78000)
    (segment_78000_79000 hbands hγ)

end AllZeros_h79000
