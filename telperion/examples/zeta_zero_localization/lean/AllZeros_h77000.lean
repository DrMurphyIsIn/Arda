/-  Height-chain step: all nontrivial zeta zeros up to height 77000 on Re = 1/2 --
    `AllZeros_h76000` + a `[76000, 77000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h76000
import RHInBoxT_1d4000000_3999999d4000000_76000_76028
import RHInBoxT_1d4000000_3999999d4000000_76028_76056
import RHInBoxT_1d4000000_3999999d4000000_304223d4_76083
import RHInBoxT_1d4000000_3999999d4000000_76083_76111
import RHInBoxT_1d4000000_3999999d4000000_76111_76139
import RHInBoxT_1d4000000_3999999d4000000_76139_76167
import RHInBoxT_1d4000000_3999999d4000000_76167_76194
import RHInBoxT_1d4000000_3999999d4000000_76194_76222
import RHInBoxT_1d4000000_3999999d4000000_76222_76250
import RHInBoxT_1d4000000_3999999d4000000_76250_76278
import RHInBoxT_1d4000000_3999999d4000000_76278_76306
import RHInBoxT_1d4000000_3999999d4000000_76306_305333d4
import RHInBoxT_1d4000000_3999999d4000000_76333_76361
import RHInBoxT_1d4000000_3999999d4000000_76361_76389
import RHInBoxT_1d4000000_3999999d4000000_76389_76417
import RHInBoxT_1d4000000_3999999d4000000_305667d4_76444
import RHInBoxT_1d4000000_3999999d4000000_76444_76472
import RHInBoxT_1d4000000_3999999d4000000_76472_76500
import RHInBoxT_1d4000000_3999999d4000000_76500_76528
import RHInBoxT_1d4000000_3999999d4000000_306111d4_76556
import RHInBoxT_1d4000000_3999999d4000000_306223d4_76583
import RHInBoxT_1d4000000_3999999d4000000_76583_76611
import RHInBoxT_1d4000000_3999999d4000000_306443d4_76639
import RHInBoxT_1d4000000_3999999d4000000_76639_76667
import RHInBoxT_1d4000000_3999999d4000000_76667_306777d4
import RHInBoxT_1d4000000_3999999d4000000_76694_76722
import RHInBoxT_1d4000000_3999999d4000000_76722_76750
import RHInBoxT_1d4000000_3999999d4000000_76750_76778
import RHInBoxT_1d4000000_3999999d4000000_307111d4_76806
import RHInBoxT_1d4000000_3999999d4000000_76806_76833
import RHInBoxT_1d4000000_3999999d4000000_76833_307445d4
import RHInBoxT_1d4000000_3999999d4000000_76861_76889
import RHInBoxT_1d4000000_3999999d4000000_76889_76917
import RHInBoxT_1d4000000_3999999d4000000_76917_76944
import RHInBoxT_1d4000000_3999999d4000000_76944_76972
import RHInBoxT_1d4000000_3999999d4000000_76972_77000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h77000

/-- The 36-band NOMINAL partition of `[76000, 77000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 76000
  | 1 => 76028
  | 2 => 76056
  | 3 => 76083
  | 4 => 76111
  | 5 => 76139
  | 6 => 76167
  | 7 => 76194
  | 8 => 76222
  | 9 => 76250
  | 10 => 76278
  | 11 => 76306
  | 12 => 76333
  | 13 => 76361
  | 14 => 76389
  | 15 => 76417
  | 16 => 76444
  | 17 => 76472
  | 18 => 76500
  | 19 => 76528
  | 20 => 76556
  | 21 => 76583
  | 22 => 76611
  | 23 => 76639
  | 24 => 76667
  | 25 => 76694
  | 26 => 76722
  | 27 => 76750
  | 28 => 76778
  | 29 => 76806
  | 30 => 76833
  | 31 => 76861
  | 32 => 76889
  | 33 => 76917
  | 34 => 76944
  | 35 => 76972
  | 36 => 77000
  | _ => 77000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((76000:ℝ)) ≤ (76028); norm_num
  · show ((76028:ℝ)) ≤ (76056); norm_num
  · show ((76056:ℝ)) ≤ (76083); norm_num
  · show ((76083:ℝ)) ≤ (76111); norm_num
  · show ((76111:ℝ)) ≤ (76139); norm_num
  · show ((76139:ℝ)) ≤ (76167); norm_num
  · show ((76167:ℝ)) ≤ (76194); norm_num
  · show ((76194:ℝ)) ≤ (76222); norm_num
  · show ((76222:ℝ)) ≤ (76250); norm_num
  · show ((76250:ℝ)) ≤ (76278); norm_num
  · show ((76278:ℝ)) ≤ (76306); norm_num
  · show ((76306:ℝ)) ≤ (76333); norm_num
  · show ((76333:ℝ)) ≤ (76361); norm_num
  · show ((76361:ℝ)) ≤ (76389); norm_num
  · show ((76389:ℝ)) ≤ (76417); norm_num
  · show ((76417:ℝ)) ≤ (76444); norm_num
  · show ((76444:ℝ)) ≤ (76472); norm_num
  · show ((76472:ℝ)) ≤ (76500); norm_num
  · show ((76500:ℝ)) ≤ (76528); norm_num
  · show ((76528:ℝ)) ≤ (76556); norm_num
  · show ((76556:ℝ)) ≤ (76583); norm_num
  · show ((76583:ℝ)) ≤ (76611); norm_num
  · show ((76611:ℝ)) ≤ (76639); norm_num
  · show ((76639:ℝ)) ≤ (76667); norm_num
  · show ((76667:ℝ)) ≤ (76694); norm_num
  · show ((76694:ℝ)) ≤ (76722); norm_num
  · show ((76722:ℝ)) ≤ (76750); norm_num
  · show ((76750:ℝ)) ≤ (76778); norm_num
  · show ((76778:ℝ)) ≤ (76806); norm_num
  · show ((76806:ℝ)) ≤ (76833); norm_num
  · show ((76833:ℝ)) ≤ (76861); norm_num
  · show ((76861:ℝ)) ≤ (76889); norm_num
  · show ((76889:ℝ)) ≤ (76917); norm_num
  · show ((76917:ℝ)) ≤ (76944); norm_num
  · show ((76944:ℝ)) ≤ (76972); norm_num
  · show ((76972:ℝ)) ≤ (77000); norm_num
  · show ((77000:ℝ)) ≤ (77000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 76000
  | 1 => 76028
  | 2 => 304223 / 4
  | 3 => 76083
  | 4 => 76111
  | 5 => 76139
  | 6 => 76167
  | 7 => 76194
  | 8 => 76222
  | 9 => 76250
  | 10 => 76278
  | 11 => 76306
  | 12 => 76333
  | 13 => 76361
  | 14 => 76389
  | 15 => 305667 / 4
  | 16 => 76444
  | 17 => 76472
  | 18 => 76500
  | 19 => 306111 / 4
  | 20 => 306223 / 4
  | 21 => 76583
  | 22 => 306443 / 4
  | 23 => 76639
  | 24 => 76667
  | 25 => 76694
  | 26 => 76722
  | 27 => 76750
  | 28 => 307111 / 4
  | 29 => 76806
  | 30 => 76833
  | 31 => 76861
  | 32 => 76889
  | 33 => 76917
  | 34 => 76944
  | 35 => 76972
  | _ => 76972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 76028
  | 1 => 76056
  | 2 => 76083
  | 3 => 76111
  | 4 => 76139
  | 5 => 76167
  | 6 => 76194
  | 7 => 76222
  | 8 => 76250
  | 9 => 76278
  | 10 => 76306
  | 11 => 305333 / 4
  | 12 => 76361
  | 13 => 76389
  | 14 => 76417
  | 15 => 76444
  | 16 => 76472
  | 17 => 76500
  | 18 => 76528
  | 19 => 76556
  | 20 => 76583
  | 21 => 76611
  | 22 => 76639
  | 23 => 76667
  | 24 => 306777 / 4
  | 25 => 76722
  | 26 => 76750
  | 27 => 76778
  | 28 => 76806
  | 29 => 76833
  | 30 => 307445 / 4
  | 31 => 76889
  | 32 => 76917
  | 33 => 76944
  | 34 => 76972
  | 35 => 77000
  | _ => 77000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 77000` (`log 77000 ≤ 12`, `2.7^12 ≥ 77000`). -/
theorem haC_77000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 77000 := by
  have hlog : Real.log 77000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 77000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 77000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[76000, 77000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[76000, 77000]` SEGMENT: every zero with `76000 ≤ Im ≤ 77000` is on the line. -/
theorem segment_76000_77000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 77000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (76000:ℝ) ≤ ρ.im → ρ.im ≤ 77000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 76000 77000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_77000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 77000 via the HEIGHT CHAIN**: `[0,76000]` ∘ `[76000,77000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_77000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 77000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 77000 → ρ.re = 1 / 2 := by
  have hγ76000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 76000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 76000 77000
    (AllZeros_h76000.all_nontrivial_zeros_up_to_height_76000_of_bands
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
      hγ76000)
    (segment_76000_77000 hbands hγ)

end AllZeros_h77000
