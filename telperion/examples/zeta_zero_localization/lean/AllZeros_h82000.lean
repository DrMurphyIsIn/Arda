/-  Height-chain step: all nontrivial zeta zeros up to height 82000 on Re = 1/2 --
    `AllZeros_h81000` + a `[81000, 82000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h81000
import RHInBoxT_1d4000000_3999999d4000000_323999d4_81028
import RHInBoxT_1d4000000_3999999d4000000_324111d4_81056
import RHInBoxT_1d4000000_3999999d4000000_81056_81083
import RHInBoxT_1d4000000_3999999d4000000_81083_81111
import RHInBoxT_1d4000000_3999999d4000000_81111_324557d4
import RHInBoxT_1d4000000_3999999d4000000_81139_81167
import RHInBoxT_1d4000000_3999999d4000000_81167_81194
import RHInBoxT_1d4000000_3999999d4000000_324775d4_81222
import RHInBoxT_1d4000000_3999999d4000000_81222_81250
import RHInBoxT_1d4000000_3999999d4000000_81250_81278
import RHInBoxT_1d4000000_3999999d4000000_81278_81306
import RHInBoxT_1d4000000_3999999d4000000_81306_81333
import RHInBoxT_1d4000000_3999999d4000000_81333_325445d4
import RHInBoxT_1d4000000_3999999d4000000_81361_81389
import RHInBoxT_1d4000000_3999999d4000000_81389_81417
import RHInBoxT_1d4000000_3999999d4000000_81417_81444
import RHInBoxT_1d4000000_3999999d4000000_81444_81472
import RHInBoxT_1d4000000_3999999d4000000_81472_81500
import RHInBoxT_1d4000000_3999999d4000000_81500_81528
import RHInBoxT_1d4000000_3999999d4000000_81528_81556
import RHInBoxT_1d4000000_3999999d4000000_81556_81583
import RHInBoxT_1d4000000_3999999d4000000_81583_81611
import RHInBoxT_1d4000000_3999999d4000000_81611_81639
import RHInBoxT_1d4000000_3999999d4000000_81639_81667
import RHInBoxT_1d4000000_3999999d4000000_81667_81694
import RHInBoxT_1d4000000_3999999d4000000_81694_81722
import RHInBoxT_1d4000000_3999999d4000000_81722_327001d4
import RHInBoxT_1d4000000_3999999d4000000_81750_327113d4
import RHInBoxT_1d4000000_3999999d4000000_81778_81806
import RHInBoxT_1d4000000_3999999d4000000_81806_81833
import RHInBoxT_1d4000000_3999999d4000000_327331d4_81861
import RHInBoxT_1d4000000_3999999d4000000_81861_81889
import RHInBoxT_1d4000000_3999999d4000000_81889_327669d4
import RHInBoxT_1d4000000_3999999d4000000_81917_81944
import RHInBoxT_1d4000000_3999999d4000000_327775d4_81972
import RHInBoxT_1d4000000_3999999d4000000_81972_82000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h82000

/-- The 36-band NOMINAL partition of `[81000, 82000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 81000
  | 1 => 81028
  | 2 => 81056
  | 3 => 81083
  | 4 => 81111
  | 5 => 81139
  | 6 => 81167
  | 7 => 81194
  | 8 => 81222
  | 9 => 81250
  | 10 => 81278
  | 11 => 81306
  | 12 => 81333
  | 13 => 81361
  | 14 => 81389
  | 15 => 81417
  | 16 => 81444
  | 17 => 81472
  | 18 => 81500
  | 19 => 81528
  | 20 => 81556
  | 21 => 81583
  | 22 => 81611
  | 23 => 81639
  | 24 => 81667
  | 25 => 81694
  | 26 => 81722
  | 27 => 81750
  | 28 => 81778
  | 29 => 81806
  | 30 => 81833
  | 31 => 81861
  | 32 => 81889
  | 33 => 81917
  | 34 => 81944
  | 35 => 81972
  | 36 => 82000
  | _ => 82000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((81000:ℝ)) ≤ (81028); norm_num
  · show ((81028:ℝ)) ≤ (81056); norm_num
  · show ((81056:ℝ)) ≤ (81083); norm_num
  · show ((81083:ℝ)) ≤ (81111); norm_num
  · show ((81111:ℝ)) ≤ (81139); norm_num
  · show ((81139:ℝ)) ≤ (81167); norm_num
  · show ((81167:ℝ)) ≤ (81194); norm_num
  · show ((81194:ℝ)) ≤ (81222); norm_num
  · show ((81222:ℝ)) ≤ (81250); norm_num
  · show ((81250:ℝ)) ≤ (81278); norm_num
  · show ((81278:ℝ)) ≤ (81306); norm_num
  · show ((81306:ℝ)) ≤ (81333); norm_num
  · show ((81333:ℝ)) ≤ (81361); norm_num
  · show ((81361:ℝ)) ≤ (81389); norm_num
  · show ((81389:ℝ)) ≤ (81417); norm_num
  · show ((81417:ℝ)) ≤ (81444); norm_num
  · show ((81444:ℝ)) ≤ (81472); norm_num
  · show ((81472:ℝ)) ≤ (81500); norm_num
  · show ((81500:ℝ)) ≤ (81528); norm_num
  · show ((81528:ℝ)) ≤ (81556); norm_num
  · show ((81556:ℝ)) ≤ (81583); norm_num
  · show ((81583:ℝ)) ≤ (81611); norm_num
  · show ((81611:ℝ)) ≤ (81639); norm_num
  · show ((81639:ℝ)) ≤ (81667); norm_num
  · show ((81667:ℝ)) ≤ (81694); norm_num
  · show ((81694:ℝ)) ≤ (81722); norm_num
  · show ((81722:ℝ)) ≤ (81750); norm_num
  · show ((81750:ℝ)) ≤ (81778); norm_num
  · show ((81778:ℝ)) ≤ (81806); norm_num
  · show ((81806:ℝ)) ≤ (81833); norm_num
  · show ((81833:ℝ)) ≤ (81861); norm_num
  · show ((81861:ℝ)) ≤ (81889); norm_num
  · show ((81889:ℝ)) ≤ (81917); norm_num
  · show ((81917:ℝ)) ≤ (81944); norm_num
  · show ((81944:ℝ)) ≤ (81972); norm_num
  · show ((81972:ℝ)) ≤ (82000); norm_num
  · show ((82000:ℝ)) ≤ (82000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 323999 / 4
  | 1 => 324111 / 4
  | 2 => 81056
  | 3 => 81083
  | 4 => 81111
  | 5 => 81139
  | 6 => 81167
  | 7 => 324775 / 4
  | 8 => 81222
  | 9 => 81250
  | 10 => 81278
  | 11 => 81306
  | 12 => 81333
  | 13 => 81361
  | 14 => 81389
  | 15 => 81417
  | 16 => 81444
  | 17 => 81472
  | 18 => 81500
  | 19 => 81528
  | 20 => 81556
  | 21 => 81583
  | 22 => 81611
  | 23 => 81639
  | 24 => 81667
  | 25 => 81694
  | 26 => 81722
  | 27 => 81750
  | 28 => 81778
  | 29 => 81806
  | 30 => 327331 / 4
  | 31 => 81861
  | 32 => 81889
  | 33 => 81917
  | 34 => 327775 / 4
  | 35 => 81972
  | _ => 81972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 81028
  | 1 => 81056
  | 2 => 81083
  | 3 => 81111
  | 4 => 324557 / 4
  | 5 => 81167
  | 6 => 81194
  | 7 => 81222
  | 8 => 81250
  | 9 => 81278
  | 10 => 81306
  | 11 => 81333
  | 12 => 325445 / 4
  | 13 => 81389
  | 14 => 81417
  | 15 => 81444
  | 16 => 81472
  | 17 => 81500
  | 18 => 81528
  | 19 => 81556
  | 20 => 81583
  | 21 => 81611
  | 22 => 81639
  | 23 => 81667
  | 24 => 81694
  | 25 => 81722
  | 26 => 327001 / 4
  | 27 => 327113 / 4
  | 28 => 81806
  | 29 => 81833
  | 30 => 81861
  | 31 => 81889
  | 32 => 327669 / 4
  | 33 => 81944
  | 34 => 81972
  | 35 => 82000
  | _ => 82000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 82000` (`log 82000 ≤ 12`, `2.7^12 ≥ 82000`). -/
theorem haC_82000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 82000 := by
  have hlog : Real.log 82000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 82000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 82000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[81000, 82000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[81000, 82000]` SEGMENT: every zero with `81000 ≤ Im ≤ 82000` is on the line. -/
theorem segment_81000_82000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 82000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (81000:ℝ) ≤ ρ.im → ρ.im ≤ 82000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 81000 82000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_82000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 82000 via the HEIGHT CHAIN**: `[0,81000]` ∘ `[81000,82000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_82000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 82000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 82000 → ρ.re = 1 / 2 := by
  have hγ81000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 81000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 81000 82000
    (AllZeros_h81000.all_nontrivial_zeros_up_to_height_81000_of_bands
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
      hγ81000)
    (segment_81000_82000 hbands hγ)

end AllZeros_h82000
