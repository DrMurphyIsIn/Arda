/-  Height-chain step: all nontrivial zeta zeros up to height 89000 on Re = 1/2 --
    `AllZeros_h88000` + a `[88000, 89000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h88000
import RHInBoxT_1d4000000_3999999d4000000_88000_352113d4
import RHInBoxT_1d4000000_3999999d4000000_88028_88056
import RHInBoxT_1d4000000_3999999d4000000_88056_88083
import RHInBoxT_1d4000000_3999999d4000000_88083_352445d4
import RHInBoxT_1d4000000_3999999d4000000_88111_88139
import RHInBoxT_1d4000000_3999999d4000000_88139_88167
import RHInBoxT_1d4000000_3999999d4000000_88167_88194
import RHInBoxT_1d4000000_3999999d4000000_88194_352889d4
import RHInBoxT_1d4000000_3999999d4000000_88222_88250
import RHInBoxT_1d4000000_3999999d4000000_88250_88278
import RHInBoxT_1d4000000_3999999d4000000_88278_88306
import RHInBoxT_1d4000000_3999999d4000000_88306_88333
import RHInBoxT_1d4000000_3999999d4000000_353331d4_353445d4
import RHInBoxT_1d4000000_3999999d4000000_88361_88389
import RHInBoxT_1d4000000_3999999d4000000_88389_88417
import RHInBoxT_1d4000000_3999999d4000000_88417_88444
import RHInBoxT_1d4000000_3999999d4000000_88444_88472
import RHInBoxT_1d4000000_3999999d4000000_88472_88500
import RHInBoxT_1d4000000_3999999d4000000_88500_88528
import RHInBoxT_1d4000000_3999999d4000000_88528_88556
import RHInBoxT_1d4000000_3999999d4000000_88556_354333d4
import RHInBoxT_1d4000000_3999999d4000000_88583_88611
import RHInBoxT_1d4000000_3999999d4000000_88611_88639
import RHInBoxT_1d4000000_3999999d4000000_88639_88667
import RHInBoxT_1d4000000_3999999d4000000_88667_88694
import RHInBoxT_1d4000000_3999999d4000000_88694_88722
import RHInBoxT_1d4000000_3999999d4000000_354887d4_88750
import RHInBoxT_1d4000000_3999999d4000000_88750_88778
import RHInBoxT_1d4000000_3999999d4000000_88778_88806
import RHInBoxT_1d4000000_3999999d4000000_88806_88833
import RHInBoxT_1d4000000_3999999d4000000_355331d4_88861
import RHInBoxT_1d4000000_3999999d4000000_88861_88889
import RHInBoxT_1d4000000_3999999d4000000_88889_88917
import RHInBoxT_1d4000000_3999999d4000000_88917_88944
import RHInBoxT_1d4000000_3999999d4000000_88944_177945d2
import RHInBoxT_1d4000000_3999999d4000000_88972_89000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h89000

/-- The 36-band NOMINAL partition of `[88000, 89000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 88000
  | 1 => 88028
  | 2 => 88056
  | 3 => 88083
  | 4 => 88111
  | 5 => 88139
  | 6 => 88167
  | 7 => 88194
  | 8 => 88222
  | 9 => 88250
  | 10 => 88278
  | 11 => 88306
  | 12 => 88333
  | 13 => 88361
  | 14 => 88389
  | 15 => 88417
  | 16 => 88444
  | 17 => 88472
  | 18 => 88500
  | 19 => 88528
  | 20 => 88556
  | 21 => 88583
  | 22 => 88611
  | 23 => 88639
  | 24 => 88667
  | 25 => 88694
  | 26 => 88722
  | 27 => 88750
  | 28 => 88778
  | 29 => 88806
  | 30 => 88833
  | 31 => 88861
  | 32 => 88889
  | 33 => 88917
  | 34 => 88944
  | 35 => 88972
  | 36 => 89000
  | _ => 89000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((88000:ℝ)) ≤ (88028); norm_num
  · show ((88028:ℝ)) ≤ (88056); norm_num
  · show ((88056:ℝ)) ≤ (88083); norm_num
  · show ((88083:ℝ)) ≤ (88111); norm_num
  · show ((88111:ℝ)) ≤ (88139); norm_num
  · show ((88139:ℝ)) ≤ (88167); norm_num
  · show ((88167:ℝ)) ≤ (88194); norm_num
  · show ((88194:ℝ)) ≤ (88222); norm_num
  · show ((88222:ℝ)) ≤ (88250); norm_num
  · show ((88250:ℝ)) ≤ (88278); norm_num
  · show ((88278:ℝ)) ≤ (88306); norm_num
  · show ((88306:ℝ)) ≤ (88333); norm_num
  · show ((88333:ℝ)) ≤ (88361); norm_num
  · show ((88361:ℝ)) ≤ (88389); norm_num
  · show ((88389:ℝ)) ≤ (88417); norm_num
  · show ((88417:ℝ)) ≤ (88444); norm_num
  · show ((88444:ℝ)) ≤ (88472); norm_num
  · show ((88472:ℝ)) ≤ (88500); norm_num
  · show ((88500:ℝ)) ≤ (88528); norm_num
  · show ((88528:ℝ)) ≤ (88556); norm_num
  · show ((88556:ℝ)) ≤ (88583); norm_num
  · show ((88583:ℝ)) ≤ (88611); norm_num
  · show ((88611:ℝ)) ≤ (88639); norm_num
  · show ((88639:ℝ)) ≤ (88667); norm_num
  · show ((88667:ℝ)) ≤ (88694); norm_num
  · show ((88694:ℝ)) ≤ (88722); norm_num
  · show ((88722:ℝ)) ≤ (88750); norm_num
  · show ((88750:ℝ)) ≤ (88778); norm_num
  · show ((88778:ℝ)) ≤ (88806); norm_num
  · show ((88806:ℝ)) ≤ (88833); norm_num
  · show ((88833:ℝ)) ≤ (88861); norm_num
  · show ((88861:ℝ)) ≤ (88889); norm_num
  · show ((88889:ℝ)) ≤ (88917); norm_num
  · show ((88917:ℝ)) ≤ (88944); norm_num
  · show ((88944:ℝ)) ≤ (88972); norm_num
  · show ((88972:ℝ)) ≤ (89000); norm_num
  · show ((89000:ℝ)) ≤ (89000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 88000
  | 1 => 88028
  | 2 => 88056
  | 3 => 88083
  | 4 => 88111
  | 5 => 88139
  | 6 => 88167
  | 7 => 88194
  | 8 => 88222
  | 9 => 88250
  | 10 => 88278
  | 11 => 88306
  | 12 => 353331 / 4
  | 13 => 88361
  | 14 => 88389
  | 15 => 88417
  | 16 => 88444
  | 17 => 88472
  | 18 => 88500
  | 19 => 88528
  | 20 => 88556
  | 21 => 88583
  | 22 => 88611
  | 23 => 88639
  | 24 => 88667
  | 25 => 88694
  | 26 => 354887 / 4
  | 27 => 88750
  | 28 => 88778
  | 29 => 88806
  | 30 => 355331 / 4
  | 31 => 88861
  | 32 => 88889
  | 33 => 88917
  | 34 => 88944
  | 35 => 88972
  | _ => 88972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 352113 / 4
  | 1 => 88056
  | 2 => 88083
  | 3 => 352445 / 4
  | 4 => 88139
  | 5 => 88167
  | 6 => 88194
  | 7 => 352889 / 4
  | 8 => 88250
  | 9 => 88278
  | 10 => 88306
  | 11 => 88333
  | 12 => 353445 / 4
  | 13 => 88389
  | 14 => 88417
  | 15 => 88444
  | 16 => 88472
  | 17 => 88500
  | 18 => 88528
  | 19 => 88556
  | 20 => 354333 / 4
  | 21 => 88611
  | 22 => 88639
  | 23 => 88667
  | 24 => 88694
  | 25 => 88722
  | 26 => 88750
  | 27 => 88778
  | 28 => 88806
  | 29 => 88833
  | 30 => 88861
  | 31 => 88889
  | 32 => 88917
  | 33 => 88944
  | 34 => 177945 / 2
  | 35 => 89000
  | _ => 89000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 89000` (`log 89000 ≤ 12`, `2.7^12 ≥ 89000`). -/
theorem haC_89000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 89000 := by
  have hlog : Real.log 89000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 89000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 89000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[88000, 89000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[88000, 89000]` SEGMENT: every zero with `88000 ≤ Im ≤ 89000` is on the line. -/
theorem segment_88000_89000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 89000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (88000:ℝ) ≤ ρ.im → ρ.im ≤ 89000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 88000 89000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_89000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 89000 via the HEIGHT CHAIN**: `[0,88000]` ∘ `[88000,89000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_89000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 89000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 89000 → ρ.re = 1 / 2 := by
  have hγ88000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 88000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 88000 89000
    (AllZeros_h88000.all_nontrivial_zeros_up_to_height_88000_of_bands
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
      hγ88000)
    (segment_88000_89000 hbands hγ)

end AllZeros_h89000
