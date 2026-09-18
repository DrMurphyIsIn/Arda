/-  Height-chain step: all nontrivial zeta zeros up to height 81000 on Re = 1/2 --
    `AllZeros_h80000` + a `[80000, 81000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h80000
import RHInBoxT_1d4000000_3999999d4000000_80000_80028
import RHInBoxT_1d4000000_3999999d4000000_80028_320225d4
import RHInBoxT_1d4000000_3999999d4000000_80056_80083
import RHInBoxT_1d4000000_3999999d4000000_80083_80111
import RHInBoxT_1d4000000_3999999d4000000_320443d4_80139
import RHInBoxT_1d4000000_3999999d4000000_80139_320669d4
import RHInBoxT_1d4000000_3999999d4000000_80167_80194
import RHInBoxT_1d4000000_3999999d4000000_80194_80222
import RHInBoxT_1d4000000_3999999d4000000_80222_80250
import RHInBoxT_1d4000000_3999999d4000000_80250_80278
import RHInBoxT_1d4000000_3999999d4000000_80278_80306
import RHInBoxT_1d4000000_3999999d4000000_80306_321333d4
import RHInBoxT_1d4000000_3999999d4000000_80333_80361
import RHInBoxT_1d4000000_3999999d4000000_80361_80389
import RHInBoxT_1d4000000_3999999d4000000_80389_321669d4
import RHInBoxT_1d4000000_3999999d4000000_80417_80444
import RHInBoxT_1d4000000_3999999d4000000_80444_80472
import RHInBoxT_1d4000000_3999999d4000000_80472_80500
import RHInBoxT_1d4000000_3999999d4000000_80500_80528
import RHInBoxT_1d4000000_3999999d4000000_161055d2_80556
import RHInBoxT_1d4000000_3999999d4000000_80556_80583
import RHInBoxT_1d4000000_3999999d4000000_322331d4_80611
import RHInBoxT_1d4000000_3999999d4000000_80611_80639
import RHInBoxT_1d4000000_3999999d4000000_80639_80667
import RHInBoxT_1d4000000_3999999d4000000_322667d4_322777d4
import RHInBoxT_1d4000000_3999999d4000000_80694_80722
import RHInBoxT_1d4000000_3999999d4000000_80722_80750
import RHInBoxT_1d4000000_3999999d4000000_80750_80778
import RHInBoxT_1d4000000_3999999d4000000_323111d4_80806
import RHInBoxT_1d4000000_3999999d4000000_80806_80833
import RHInBoxT_1d4000000_3999999d4000000_80833_80861
import RHInBoxT_1d4000000_3999999d4000000_80861_80889
import RHInBoxT_1d4000000_3999999d4000000_80889_80917
import RHInBoxT_1d4000000_3999999d4000000_80917_80944
import RHInBoxT_1d4000000_3999999d4000000_80944_80972
import RHInBoxT_1d4000000_3999999d4000000_80972_81000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h81000

/-- The 36-band NOMINAL partition of `[80000, 81000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 80000
  | 1 => 80028
  | 2 => 80056
  | 3 => 80083
  | 4 => 80111
  | 5 => 80139
  | 6 => 80167
  | 7 => 80194
  | 8 => 80222
  | 9 => 80250
  | 10 => 80278
  | 11 => 80306
  | 12 => 80333
  | 13 => 80361
  | 14 => 80389
  | 15 => 80417
  | 16 => 80444
  | 17 => 80472
  | 18 => 80500
  | 19 => 80528
  | 20 => 80556
  | 21 => 80583
  | 22 => 80611
  | 23 => 80639
  | 24 => 80667
  | 25 => 80694
  | 26 => 80722
  | 27 => 80750
  | 28 => 80778
  | 29 => 80806
  | 30 => 80833
  | 31 => 80861
  | 32 => 80889
  | 33 => 80917
  | 34 => 80944
  | 35 => 80972
  | 36 => 81000
  | _ => 81000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((80000:ℝ)) ≤ (80028); norm_num
  · show ((80028:ℝ)) ≤ (80056); norm_num
  · show ((80056:ℝ)) ≤ (80083); norm_num
  · show ((80083:ℝ)) ≤ (80111); norm_num
  · show ((80111:ℝ)) ≤ (80139); norm_num
  · show ((80139:ℝ)) ≤ (80167); norm_num
  · show ((80167:ℝ)) ≤ (80194); norm_num
  · show ((80194:ℝ)) ≤ (80222); norm_num
  · show ((80222:ℝ)) ≤ (80250); norm_num
  · show ((80250:ℝ)) ≤ (80278); norm_num
  · show ((80278:ℝ)) ≤ (80306); norm_num
  · show ((80306:ℝ)) ≤ (80333); norm_num
  · show ((80333:ℝ)) ≤ (80361); norm_num
  · show ((80361:ℝ)) ≤ (80389); norm_num
  · show ((80389:ℝ)) ≤ (80417); norm_num
  · show ((80417:ℝ)) ≤ (80444); norm_num
  · show ((80444:ℝ)) ≤ (80472); norm_num
  · show ((80472:ℝ)) ≤ (80500); norm_num
  · show ((80500:ℝ)) ≤ (80528); norm_num
  · show ((80528:ℝ)) ≤ (80556); norm_num
  · show ((80556:ℝ)) ≤ (80583); norm_num
  · show ((80583:ℝ)) ≤ (80611); norm_num
  · show ((80611:ℝ)) ≤ (80639); norm_num
  · show ((80639:ℝ)) ≤ (80667); norm_num
  · show ((80667:ℝ)) ≤ (80694); norm_num
  · show ((80694:ℝ)) ≤ (80722); norm_num
  · show ((80722:ℝ)) ≤ (80750); norm_num
  · show ((80750:ℝ)) ≤ (80778); norm_num
  · show ((80778:ℝ)) ≤ (80806); norm_num
  · show ((80806:ℝ)) ≤ (80833); norm_num
  · show ((80833:ℝ)) ≤ (80861); norm_num
  · show ((80861:ℝ)) ≤ (80889); norm_num
  · show ((80889:ℝ)) ≤ (80917); norm_num
  · show ((80917:ℝ)) ≤ (80944); norm_num
  · show ((80944:ℝ)) ≤ (80972); norm_num
  · show ((80972:ℝ)) ≤ (81000); norm_num
  · show ((81000:ℝ)) ≤ (81000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 80000
  | 1 => 80028
  | 2 => 80056
  | 3 => 80083
  | 4 => 320443 / 4
  | 5 => 80139
  | 6 => 80167
  | 7 => 80194
  | 8 => 80222
  | 9 => 80250
  | 10 => 80278
  | 11 => 80306
  | 12 => 80333
  | 13 => 80361
  | 14 => 80389
  | 15 => 80417
  | 16 => 80444
  | 17 => 80472
  | 18 => 80500
  | 19 => 161055 / 2
  | 20 => 80556
  | 21 => 322331 / 4
  | 22 => 80611
  | 23 => 80639
  | 24 => 322667 / 4
  | 25 => 80694
  | 26 => 80722
  | 27 => 80750
  | 28 => 323111 / 4
  | 29 => 80806
  | 30 => 80833
  | 31 => 80861
  | 32 => 80889
  | 33 => 80917
  | 34 => 80944
  | 35 => 80972
  | _ => 80972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 80028
  | 1 => 320225 / 4
  | 2 => 80083
  | 3 => 80111
  | 4 => 80139
  | 5 => 320669 / 4
  | 6 => 80194
  | 7 => 80222
  | 8 => 80250
  | 9 => 80278
  | 10 => 80306
  | 11 => 321333 / 4
  | 12 => 80361
  | 13 => 80389
  | 14 => 321669 / 4
  | 15 => 80444
  | 16 => 80472
  | 17 => 80500
  | 18 => 80528
  | 19 => 80556
  | 20 => 80583
  | 21 => 80611
  | 22 => 80639
  | 23 => 80667
  | 24 => 322777 / 4
  | 25 => 80722
  | 26 => 80750
  | 27 => 80778
  | 28 => 80806
  | 29 => 80833
  | 30 => 80861
  | 31 => 80889
  | 32 => 80917
  | 33 => 80944
  | 34 => 80972
  | 35 => 81000
  | _ => 81000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 81000` (`log 81000 ≤ 12`, `2.7^12 ≥ 81000`). -/
theorem haC_81000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 81000 := by
  have hlog : Real.log 81000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 81000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 81000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[80000, 81000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[80000, 81000]` SEGMENT: every zero with `80000 ≤ Im ≤ 81000` is on the line. -/
theorem segment_80000_81000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 81000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (80000:ℝ) ≤ ρ.im → ρ.im ≤ 81000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 80000 81000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_81000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 81000 via the HEIGHT CHAIN**: `[0,80000]` ∘ `[80000,81000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_81000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 81000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 81000 → ρ.re = 1 / 2 := by
  have hγ80000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 80000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 80000 81000
    (AllZeros_h80000.all_nontrivial_zeros_up_to_height_80000_of_bands
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
      hγ80000)
    (segment_80000_81000 hbands hγ)

end AllZeros_h81000
