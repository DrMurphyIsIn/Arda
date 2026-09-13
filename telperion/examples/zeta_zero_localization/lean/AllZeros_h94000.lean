/-  Height-chain step: all nontrivial zeta zeros up to height 94000 on Re = 1/2 --
    `AllZeros_h93000` + a `[93000, 94000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h93000
import RHInBoxT_1d4000000_3999999d4000000_93000_93028
import RHInBoxT_1d4000000_3999999d4000000_93028_93056
import RHInBoxT_1d4000000_3999999d4000000_93056_93083
import RHInBoxT_1d4000000_3999999d4000000_93083_93111
import RHInBoxT_1d4000000_3999999d4000000_93111_93139
import RHInBoxT_1d4000000_3999999d4000000_93139_93167
import RHInBoxT_1d4000000_3999999d4000000_93167_372777d4
import RHInBoxT_1d4000000_3999999d4000000_93194_93222
import RHInBoxT_1d4000000_3999999d4000000_93222_93250
import RHInBoxT_1d4000000_3999999d4000000_93250_93278
import RHInBoxT_1d4000000_3999999d4000000_93278_93306
import RHInBoxT_1d4000000_3999999d4000000_93306_93333
import RHInBoxT_1d4000000_3999999d4000000_93333_93361
import RHInBoxT_1d4000000_3999999d4000000_93361_93389
import RHInBoxT_1d4000000_3999999d4000000_373555d4_373669d4
import RHInBoxT_1d4000000_3999999d4000000_93417_93444
import RHInBoxT_1d4000000_3999999d4000000_373775d4_373889d4
import RHInBoxT_1d4000000_3999999d4000000_93472_93500
import RHInBoxT_1d4000000_3999999d4000000_93500_93528
import RHInBoxT_1d4000000_3999999d4000000_93528_374225d4
import RHInBoxT_1d4000000_3999999d4000000_93556_374333d4
import RHInBoxT_1d4000000_3999999d4000000_93583_93611
import RHInBoxT_1d4000000_3999999d4000000_93611_93639
import RHInBoxT_1d4000000_3999999d4000000_93639_93667
import RHInBoxT_1d4000000_3999999d4000000_93667_93694
import RHInBoxT_1d4000000_3999999d4000000_93694_374889d4
import RHInBoxT_1d4000000_3999999d4000000_93722_93750
import RHInBoxT_1d4000000_3999999d4000000_93750_93778
import RHInBoxT_1d4000000_3999999d4000000_93778_93806
import RHInBoxT_1d4000000_3999999d4000000_93806_93833
import RHInBoxT_1d4000000_3999999d4000000_93833_375445d4
import RHInBoxT_1d4000000_3999999d4000000_93861_375557d4
import RHInBoxT_1d4000000_3999999d4000000_375555d4_93917
import RHInBoxT_1d4000000_3999999d4000000_93917_93944
import RHInBoxT_1d4000000_3999999d4000000_93944_93972
import RHInBoxT_1d4000000_3999999d4000000_93972_94000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h94000

/-- The 36-band NOMINAL partition of `[93000, 94000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 93000
  | 1 => 93028
  | 2 => 93056
  | 3 => 93083
  | 4 => 93111
  | 5 => 93139
  | 6 => 93167
  | 7 => 93194
  | 8 => 93222
  | 9 => 93250
  | 10 => 93278
  | 11 => 93306
  | 12 => 93333
  | 13 => 93361
  | 14 => 93389
  | 15 => 93417
  | 16 => 93444
  | 17 => 93472
  | 18 => 93500
  | 19 => 93528
  | 20 => 93556
  | 21 => 93583
  | 22 => 93611
  | 23 => 93639
  | 24 => 93667
  | 25 => 93694
  | 26 => 93722
  | 27 => 93750
  | 28 => 93778
  | 29 => 93806
  | 30 => 93833
  | 31 => 93861
  | 32 => 93889
  | 33 => 93917
  | 34 => 93944
  | 35 => 93972
  | 36 => 94000
  | _ => 94000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((93000:ℝ)) ≤ (93028); norm_num
  · show ((93028:ℝ)) ≤ (93056); norm_num
  · show ((93056:ℝ)) ≤ (93083); norm_num
  · show ((93083:ℝ)) ≤ (93111); norm_num
  · show ((93111:ℝ)) ≤ (93139); norm_num
  · show ((93139:ℝ)) ≤ (93167); norm_num
  · show ((93167:ℝ)) ≤ (93194); norm_num
  · show ((93194:ℝ)) ≤ (93222); norm_num
  · show ((93222:ℝ)) ≤ (93250); norm_num
  · show ((93250:ℝ)) ≤ (93278); norm_num
  · show ((93278:ℝ)) ≤ (93306); norm_num
  · show ((93306:ℝ)) ≤ (93333); norm_num
  · show ((93333:ℝ)) ≤ (93361); norm_num
  · show ((93361:ℝ)) ≤ (93389); norm_num
  · show ((93389:ℝ)) ≤ (93417); norm_num
  · show ((93417:ℝ)) ≤ (93444); norm_num
  · show ((93444:ℝ)) ≤ (93472); norm_num
  · show ((93472:ℝ)) ≤ (93500); norm_num
  · show ((93500:ℝ)) ≤ (93528); norm_num
  · show ((93528:ℝ)) ≤ (93556); norm_num
  · show ((93556:ℝ)) ≤ (93583); norm_num
  · show ((93583:ℝ)) ≤ (93611); norm_num
  · show ((93611:ℝ)) ≤ (93639); norm_num
  · show ((93639:ℝ)) ≤ (93667); norm_num
  · show ((93667:ℝ)) ≤ (93694); norm_num
  · show ((93694:ℝ)) ≤ (93722); norm_num
  · show ((93722:ℝ)) ≤ (93750); norm_num
  · show ((93750:ℝ)) ≤ (93778); norm_num
  · show ((93778:ℝ)) ≤ (93806); norm_num
  · show ((93806:ℝ)) ≤ (93833); norm_num
  · show ((93833:ℝ)) ≤ (93861); norm_num
  · show ((93861:ℝ)) ≤ (93889); norm_num
  · show ((93889:ℝ)) ≤ (93917); norm_num
  · show ((93917:ℝ)) ≤ (93944); norm_num
  · show ((93944:ℝ)) ≤ (93972); norm_num
  · show ((93972:ℝ)) ≤ (94000); norm_num
  · show ((94000:ℝ)) ≤ (94000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 93000
  | 1 => 93028
  | 2 => 93056
  | 3 => 93083
  | 4 => 93111
  | 5 => 93139
  | 6 => 93167
  | 7 => 93194
  | 8 => 93222
  | 9 => 93250
  | 10 => 93278
  | 11 => 93306
  | 12 => 93333
  | 13 => 93361
  | 14 => 373555 / 4
  | 15 => 93417
  | 16 => 373775 / 4
  | 17 => 93472
  | 18 => 93500
  | 19 => 93528
  | 20 => 93556
  | 21 => 93583
  | 22 => 93611
  | 23 => 93639
  | 24 => 93667
  | 25 => 93694
  | 26 => 93722
  | 27 => 93750
  | 28 => 93778
  | 29 => 93806
  | 30 => 93833
  | 31 => 93861
  | 32 => 375555 / 4
  | 33 => 93917
  | 34 => 93944
  | 35 => 93972
  | _ => 93972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 93028
  | 1 => 93056
  | 2 => 93083
  | 3 => 93111
  | 4 => 93139
  | 5 => 93167
  | 6 => 372777 / 4
  | 7 => 93222
  | 8 => 93250
  | 9 => 93278
  | 10 => 93306
  | 11 => 93333
  | 12 => 93361
  | 13 => 93389
  | 14 => 373669 / 4
  | 15 => 93444
  | 16 => 373889 / 4
  | 17 => 93500
  | 18 => 93528
  | 19 => 374225 / 4
  | 20 => 374333 / 4
  | 21 => 93611
  | 22 => 93639
  | 23 => 93667
  | 24 => 93694
  | 25 => 374889 / 4
  | 26 => 93750
  | 27 => 93778
  | 28 => 93806
  | 29 => 93833
  | 30 => 375445 / 4
  | 31 => 375557 / 4
  | 32 => 93917
  | 33 => 93944
  | 34 => 93972
  | 35 => 94000
  | _ => 94000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 94000` (`log 94000 ≤ 12`, `2.7^12 ≥ 94000`). -/
theorem haC_94000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 94000 := by
  have hlog : Real.log 94000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 94000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 94000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[93000, 94000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[93000, 94000]` SEGMENT: every zero with `93000 ≤ Im ≤ 94000` is on the line. -/
theorem segment_93000_94000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 94000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (93000:ℝ) ≤ ρ.im → ρ.im ≤ 94000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 93000 94000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_94000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 94000 via the HEIGHT CHAIN**: `[0,93000]` ∘ `[93000,94000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_94000_of_bands
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
    (hbands_79000 : AllZeros_h79000.BandHyp)
    (hbands_80000 : AllZeros_h80000.BandHyp)
    (hbands_81000 : AllZeros_h81000.BandHyp)
    (hbands_82000 : AllZeros_h82000.BandHyp)
    (hbands_83000 : AllZeros_h83000.BandHyp)
    (hbands_84000 : AllZeros_h84000.BandHyp)
    (hbands_85000 : AllZeros_h85000.BandHyp)
    (hbands_86000 : AllZeros_h86000.BandHyp)
    (hbands_87000 : AllZeros_h87000.BandHyp)
    (hbands_88000 : AllZeros_h88000.BandHyp)
    (hbands_89000 : AllZeros_h89000.BandHyp)
    (hbands_90000 : AllZeros_h90000.BandHyp)
    (hbands_91000 : AllZeros_h91000.BandHyp)
    (hbands_92000 : AllZeros_h92000.BandHyp)
    (hbands_93000 : AllZeros_h93000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 94000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 94000 → ρ.re = 1 / 2 := by
  have hγ93000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 93000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 93000 94000
    (AllZeros_h93000.all_nontrivial_zeros_up_to_height_93000_of_bands
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
      hbands_79000
      hbands_80000
      hbands_81000
      hbands_82000
      hbands_83000
      hbands_84000
      hbands_85000
      hbands_86000
      hbands_87000
      hbands_88000
      hbands_89000
      hbands_90000
      hbands_91000
      hbands_92000
      hbands_93000
      hγ93000)
    (segment_93000_94000 hbands hγ)

end AllZeros_h94000
