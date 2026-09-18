/-  Height-chain step: all nontrivial zeta zeros up to height 98000 on Re = 1/2 --
    `AllZeros_h97000` + a `[97000, 98000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h97000
import RHInBoxT_1d4000000_3999999d4000000_97000_97028
import RHInBoxT_1d4000000_3999999d4000000_388111d4_97056
import RHInBoxT_1d4000000_3999999d4000000_97056_97083
import RHInBoxT_1d4000000_3999999d4000000_97083_97111
import RHInBoxT_1d4000000_3999999d4000000_388443d4_388557d4
import RHInBoxT_1d4000000_3999999d4000000_97139_97167
import RHInBoxT_1d4000000_3999999d4000000_388667d4_97194
import RHInBoxT_1d4000000_3999999d4000000_97194_97222
import RHInBoxT_1d4000000_3999999d4000000_388887d4_97250
import RHInBoxT_1d4000000_3999999d4000000_97250_97278
import RHInBoxT_1d4000000_3999999d4000000_97278_97306
import RHInBoxT_1d4000000_3999999d4000000_97306_97333
import RHInBoxT_1d4000000_3999999d4000000_97333_97361
import RHInBoxT_1d4000000_3999999d4000000_97361_389557d4
import RHInBoxT_1d4000000_3999999d4000000_97389_97417
import RHInBoxT_1d4000000_3999999d4000000_389667d4_389777d4
import RHInBoxT_1d4000000_3999999d4000000_389775d4_97472
import RHInBoxT_1d4000000_3999999d4000000_97472_97500
import RHInBoxT_1d4000000_3999999d4000000_97500_97528
import RHInBoxT_1d4000000_3999999d4000000_97528_97556
import RHInBoxT_1d4000000_3999999d4000000_97556_390333d4
import RHInBoxT_1d4000000_3999999d4000000_97583_97611
import RHInBoxT_1d4000000_3999999d4000000_97611_97639
import RHInBoxT_1d4000000_3999999d4000000_97639_97667
import RHInBoxT_1d4000000_3999999d4000000_97667_97694
import RHInBoxT_1d4000000_3999999d4000000_97694_97722
import RHInBoxT_1d4000000_3999999d4000000_97722_97750
import RHInBoxT_1d4000000_3999999d4000000_97750_97778
import RHInBoxT_1d4000000_3999999d4000000_97778_97806
import RHInBoxT_1d4000000_3999999d4000000_97806_97833
import RHInBoxT_1d4000000_3999999d4000000_97833_97861
import RHInBoxT_1d4000000_3999999d4000000_97861_97889
import RHInBoxT_1d4000000_3999999d4000000_97889_97917
import RHInBoxT_1d4000000_3999999d4000000_97917_97944
import RHInBoxT_1d4000000_3999999d4000000_97944_97972
import RHInBoxT_1d4000000_3999999d4000000_97972_98000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h98000

/-- The 36-band NOMINAL partition of `[97000, 98000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 97000
  | 1 => 97028
  | 2 => 97056
  | 3 => 97083
  | 4 => 97111
  | 5 => 97139
  | 6 => 97167
  | 7 => 97194
  | 8 => 97222
  | 9 => 97250
  | 10 => 97278
  | 11 => 97306
  | 12 => 97333
  | 13 => 97361
  | 14 => 97389
  | 15 => 97417
  | 16 => 97444
  | 17 => 97472
  | 18 => 97500
  | 19 => 97528
  | 20 => 97556
  | 21 => 97583
  | 22 => 97611
  | 23 => 97639
  | 24 => 97667
  | 25 => 97694
  | 26 => 97722
  | 27 => 97750
  | 28 => 97778
  | 29 => 97806
  | 30 => 97833
  | 31 => 97861
  | 32 => 97889
  | 33 => 97917
  | 34 => 97944
  | 35 => 97972
  | 36 => 98000
  | _ => 98000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((97000:ℝ)) ≤ (97028); norm_num
  · show ((97028:ℝ)) ≤ (97056); norm_num
  · show ((97056:ℝ)) ≤ (97083); norm_num
  · show ((97083:ℝ)) ≤ (97111); norm_num
  · show ((97111:ℝ)) ≤ (97139); norm_num
  · show ((97139:ℝ)) ≤ (97167); norm_num
  · show ((97167:ℝ)) ≤ (97194); norm_num
  · show ((97194:ℝ)) ≤ (97222); norm_num
  · show ((97222:ℝ)) ≤ (97250); norm_num
  · show ((97250:ℝ)) ≤ (97278); norm_num
  · show ((97278:ℝ)) ≤ (97306); norm_num
  · show ((97306:ℝ)) ≤ (97333); norm_num
  · show ((97333:ℝ)) ≤ (97361); norm_num
  · show ((97361:ℝ)) ≤ (97389); norm_num
  · show ((97389:ℝ)) ≤ (97417); norm_num
  · show ((97417:ℝ)) ≤ (97444); norm_num
  · show ((97444:ℝ)) ≤ (97472); norm_num
  · show ((97472:ℝ)) ≤ (97500); norm_num
  · show ((97500:ℝ)) ≤ (97528); norm_num
  · show ((97528:ℝ)) ≤ (97556); norm_num
  · show ((97556:ℝ)) ≤ (97583); norm_num
  · show ((97583:ℝ)) ≤ (97611); norm_num
  · show ((97611:ℝ)) ≤ (97639); norm_num
  · show ((97639:ℝ)) ≤ (97667); norm_num
  · show ((97667:ℝ)) ≤ (97694); norm_num
  · show ((97694:ℝ)) ≤ (97722); norm_num
  · show ((97722:ℝ)) ≤ (97750); norm_num
  · show ((97750:ℝ)) ≤ (97778); norm_num
  · show ((97778:ℝ)) ≤ (97806); norm_num
  · show ((97806:ℝ)) ≤ (97833); norm_num
  · show ((97833:ℝ)) ≤ (97861); norm_num
  · show ((97861:ℝ)) ≤ (97889); norm_num
  · show ((97889:ℝ)) ≤ (97917); norm_num
  · show ((97917:ℝ)) ≤ (97944); norm_num
  · show ((97944:ℝ)) ≤ (97972); norm_num
  · show ((97972:ℝ)) ≤ (98000); norm_num
  · show ((98000:ℝ)) ≤ (98000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 97000
  | 1 => 388111 / 4
  | 2 => 97056
  | 3 => 97083
  | 4 => 388443 / 4
  | 5 => 97139
  | 6 => 388667 / 4
  | 7 => 97194
  | 8 => 388887 / 4
  | 9 => 97250
  | 10 => 97278
  | 11 => 97306
  | 12 => 97333
  | 13 => 97361
  | 14 => 97389
  | 15 => 389667 / 4
  | 16 => 389775 / 4
  | 17 => 97472
  | 18 => 97500
  | 19 => 97528
  | 20 => 97556
  | 21 => 97583
  | 22 => 97611
  | 23 => 97639
  | 24 => 97667
  | 25 => 97694
  | 26 => 97722
  | 27 => 97750
  | 28 => 97778
  | 29 => 97806
  | 30 => 97833
  | 31 => 97861
  | 32 => 97889
  | 33 => 97917
  | 34 => 97944
  | 35 => 97972
  | _ => 97972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 97028
  | 1 => 97056
  | 2 => 97083
  | 3 => 97111
  | 4 => 388557 / 4
  | 5 => 97167
  | 6 => 97194
  | 7 => 97222
  | 8 => 97250
  | 9 => 97278
  | 10 => 97306
  | 11 => 97333
  | 12 => 97361
  | 13 => 389557 / 4
  | 14 => 97417
  | 15 => 389777 / 4
  | 16 => 97472
  | 17 => 97500
  | 18 => 97528
  | 19 => 97556
  | 20 => 390333 / 4
  | 21 => 97611
  | 22 => 97639
  | 23 => 97667
  | 24 => 97694
  | 25 => 97722
  | 26 => 97750
  | 27 => 97778
  | 28 => 97806
  | 29 => 97833
  | 30 => 97861
  | 31 => 97889
  | 32 => 97917
  | 33 => 97944
  | 34 => 97972
  | 35 => 98000
  | _ => 98000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 98000` (`log 98000 ≤ 12`, `2.7^12 ≥ 98000`). -/
theorem haC_98000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 98000 := by
  have hlog : Real.log 98000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 98000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 98000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[97000, 98000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[97000, 98000]` SEGMENT: every zero with `97000 ≤ Im ≤ 98000` is on the line. -/
theorem segment_97000_98000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 98000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (97000:ℝ) ≤ ρ.im → ρ.im ≤ 98000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 97000 98000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_98000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 98000 via the HEIGHT CHAIN**: `[0,97000]` ∘ `[97000,98000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_98000_of_bands
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
    (hbands_94000 : AllZeros_h94000.BandHyp)
    (hbands_95000 : AllZeros_h95000.BandHyp)
    (hbands_96000 : AllZeros_h96000.BandHyp)
    (hbands_97000 : AllZeros_h97000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 98000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 98000 → ρ.re = 1 / 2 := by
  have hγ97000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 97000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 97000 98000
    (AllZeros_h97000.all_nontrivial_zeros_up_to_height_97000_of_bands
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
      hbands_94000
      hbands_95000
      hbands_96000
      hbands_97000
      hγ97000)
    (segment_97000_98000 hbands hγ)

end AllZeros_h98000
