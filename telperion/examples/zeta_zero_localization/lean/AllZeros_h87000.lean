/-  Height-chain step: all nontrivial zeta zeros up to height 87000 on Re = 1/2 --
    `AllZeros_h86000` + a `[86000, 87000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h86000
import RHInBoxT_1d4000000_3999999d4000000_343999d4_86028
import RHInBoxT_1d4000000_3999999d4000000_86028_344225d4
import RHInBoxT_1d4000000_3999999d4000000_86056_86083
import RHInBoxT_1d4000000_3999999d4000000_86083_86111
import RHInBoxT_1d4000000_3999999d4000000_86111_86139
import RHInBoxT_1d4000000_3999999d4000000_86139_86167
import RHInBoxT_1d4000000_3999999d4000000_86167_86194
import RHInBoxT_1d4000000_3999999d4000000_86194_86222
import RHInBoxT_1d4000000_3999999d4000000_344887d4_345001d4
import RHInBoxT_1d4000000_3999999d4000000_86250_86278
import RHInBoxT_1d4000000_3999999d4000000_86278_86306
import RHInBoxT_1d4000000_3999999d4000000_86306_86333
import RHInBoxT_1d4000000_3999999d4000000_86333_86361
import RHInBoxT_1d4000000_3999999d4000000_345443d4_86389
import RHInBoxT_1d4000000_3999999d4000000_86389_86417
import RHInBoxT_1d4000000_3999999d4000000_86417_86444
import RHInBoxT_1d4000000_3999999d4000000_86444_86472
import RHInBoxT_1d4000000_3999999d4000000_345887d4_86500
import RHInBoxT_1d4000000_3999999d4000000_86500_86528
import RHInBoxT_1d4000000_3999999d4000000_86528_86556
import RHInBoxT_1d4000000_3999999d4000000_86556_86583
import RHInBoxT_1d4000000_3999999d4000000_86583_86611
import RHInBoxT_1d4000000_3999999d4000000_86611_86639
import RHInBoxT_1d4000000_3999999d4000000_86639_86667
import RHInBoxT_1d4000000_3999999d4000000_86667_346777d4
import RHInBoxT_1d4000000_3999999d4000000_86694_86722
import RHInBoxT_1d4000000_3999999d4000000_86722_86750
import RHInBoxT_1d4000000_3999999d4000000_86750_86778
import RHInBoxT_1d4000000_3999999d4000000_86778_86806
import RHInBoxT_1d4000000_3999999d4000000_86806_86833
import RHInBoxT_1d4000000_3999999d4000000_86833_86861
import RHInBoxT_1d4000000_3999999d4000000_86861_86889
import RHInBoxT_1d4000000_3999999d4000000_86889_86917
import RHInBoxT_1d4000000_3999999d4000000_86917_86944
import RHInBoxT_1d4000000_3999999d4000000_86944_86972
import RHInBoxT_1d4000000_3999999d4000000_86972_87000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h87000

/-- The 36-band NOMINAL partition of `[86000, 87000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 86000
  | 1 => 86028
  | 2 => 86056
  | 3 => 86083
  | 4 => 86111
  | 5 => 86139
  | 6 => 86167
  | 7 => 86194
  | 8 => 86222
  | 9 => 86250
  | 10 => 86278
  | 11 => 86306
  | 12 => 86333
  | 13 => 86361
  | 14 => 86389
  | 15 => 86417
  | 16 => 86444
  | 17 => 86472
  | 18 => 86500
  | 19 => 86528
  | 20 => 86556
  | 21 => 86583
  | 22 => 86611
  | 23 => 86639
  | 24 => 86667
  | 25 => 86694
  | 26 => 86722
  | 27 => 86750
  | 28 => 86778
  | 29 => 86806
  | 30 => 86833
  | 31 => 86861
  | 32 => 86889
  | 33 => 86917
  | 34 => 86944
  | 35 => 86972
  | 36 => 87000
  | _ => 87000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((86000:ℝ)) ≤ (86028); norm_num
  · show ((86028:ℝ)) ≤ (86056); norm_num
  · show ((86056:ℝ)) ≤ (86083); norm_num
  · show ((86083:ℝ)) ≤ (86111); norm_num
  · show ((86111:ℝ)) ≤ (86139); norm_num
  · show ((86139:ℝ)) ≤ (86167); norm_num
  · show ((86167:ℝ)) ≤ (86194); norm_num
  · show ((86194:ℝ)) ≤ (86222); norm_num
  · show ((86222:ℝ)) ≤ (86250); norm_num
  · show ((86250:ℝ)) ≤ (86278); norm_num
  · show ((86278:ℝ)) ≤ (86306); norm_num
  · show ((86306:ℝ)) ≤ (86333); norm_num
  · show ((86333:ℝ)) ≤ (86361); norm_num
  · show ((86361:ℝ)) ≤ (86389); norm_num
  · show ((86389:ℝ)) ≤ (86417); norm_num
  · show ((86417:ℝ)) ≤ (86444); norm_num
  · show ((86444:ℝ)) ≤ (86472); norm_num
  · show ((86472:ℝ)) ≤ (86500); norm_num
  · show ((86500:ℝ)) ≤ (86528); norm_num
  · show ((86528:ℝ)) ≤ (86556); norm_num
  · show ((86556:ℝ)) ≤ (86583); norm_num
  · show ((86583:ℝ)) ≤ (86611); norm_num
  · show ((86611:ℝ)) ≤ (86639); norm_num
  · show ((86639:ℝ)) ≤ (86667); norm_num
  · show ((86667:ℝ)) ≤ (86694); norm_num
  · show ((86694:ℝ)) ≤ (86722); norm_num
  · show ((86722:ℝ)) ≤ (86750); norm_num
  · show ((86750:ℝ)) ≤ (86778); norm_num
  · show ((86778:ℝ)) ≤ (86806); norm_num
  · show ((86806:ℝ)) ≤ (86833); norm_num
  · show ((86833:ℝ)) ≤ (86861); norm_num
  · show ((86861:ℝ)) ≤ (86889); norm_num
  · show ((86889:ℝ)) ≤ (86917); norm_num
  · show ((86917:ℝ)) ≤ (86944); norm_num
  · show ((86944:ℝ)) ≤ (86972); norm_num
  · show ((86972:ℝ)) ≤ (87000); norm_num
  · show ((87000:ℝ)) ≤ (87000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 343999 / 4
  | 1 => 86028
  | 2 => 86056
  | 3 => 86083
  | 4 => 86111
  | 5 => 86139
  | 6 => 86167
  | 7 => 86194
  | 8 => 344887 / 4
  | 9 => 86250
  | 10 => 86278
  | 11 => 86306
  | 12 => 86333
  | 13 => 345443 / 4
  | 14 => 86389
  | 15 => 86417
  | 16 => 86444
  | 17 => 345887 / 4
  | 18 => 86500
  | 19 => 86528
  | 20 => 86556
  | 21 => 86583
  | 22 => 86611
  | 23 => 86639
  | 24 => 86667
  | 25 => 86694
  | 26 => 86722
  | 27 => 86750
  | 28 => 86778
  | 29 => 86806
  | 30 => 86833
  | 31 => 86861
  | 32 => 86889
  | 33 => 86917
  | 34 => 86944
  | 35 => 86972
  | _ => 86972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 86028
  | 1 => 344225 / 4
  | 2 => 86083
  | 3 => 86111
  | 4 => 86139
  | 5 => 86167
  | 6 => 86194
  | 7 => 86222
  | 8 => 345001 / 4
  | 9 => 86278
  | 10 => 86306
  | 11 => 86333
  | 12 => 86361
  | 13 => 86389
  | 14 => 86417
  | 15 => 86444
  | 16 => 86472
  | 17 => 86500
  | 18 => 86528
  | 19 => 86556
  | 20 => 86583
  | 21 => 86611
  | 22 => 86639
  | 23 => 86667
  | 24 => 346777 / 4
  | 25 => 86722
  | 26 => 86750
  | 27 => 86778
  | 28 => 86806
  | 29 => 86833
  | 30 => 86861
  | 31 => 86889
  | 32 => 86917
  | 33 => 86944
  | 34 => 86972
  | 35 => 87000
  | _ => 87000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 87000` (`log 87000 ≤ 12`, `2.7^12 ≥ 87000`). -/
theorem haC_87000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 87000 := by
  have hlog : Real.log 87000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 87000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 87000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[86000, 87000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[86000, 87000]` SEGMENT: every zero with `86000 ≤ Im ≤ 87000` is on the line. -/
theorem segment_86000_87000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 87000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (86000:ℝ) ≤ ρ.im → ρ.im ≤ 87000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 86000 87000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_87000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 87000 via the HEIGHT CHAIN**: `[0,86000]` ∘ `[86000,87000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_87000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 87000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 87000 → ρ.re = 1 / 2 := by
  have hγ86000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 86000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 86000 87000
    (AllZeros_h86000.all_nontrivial_zeros_up_to_height_86000_of_bands
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
      hγ86000)
    (segment_86000_87000 hbands hγ)

end AllZeros_h87000
