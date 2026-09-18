/-  Height-chain step: all nontrivial zeta zeros up to height 92000 on Re = 1/2 --
    `AllZeros_h91000` + a `[91000, 92000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h91000
import RHInBoxT_1d4000000_3999999d4000000_91000_364113d4
import RHInBoxT_1d4000000_3999999d4000000_91028_364225d4
import RHInBoxT_1d4000000_3999999d4000000_91056_91083
import RHInBoxT_1d4000000_3999999d4000000_91083_364445d4
import RHInBoxT_1d4000000_3999999d4000000_91111_91139
import RHInBoxT_1d4000000_3999999d4000000_91139_91167
import RHInBoxT_1d4000000_3999999d4000000_364667d4_91194
import RHInBoxT_1d4000000_3999999d4000000_91194_91222
import RHInBoxT_1d4000000_3999999d4000000_91222_91250
import RHInBoxT_1d4000000_3999999d4000000_91250_91278
import RHInBoxT_1d4000000_3999999d4000000_91278_91306
import RHInBoxT_1d4000000_3999999d4000000_91306_91333
import RHInBoxT_1d4000000_3999999d4000000_91333_91361
import RHInBoxT_1d4000000_3999999d4000000_365443d4_91389
import RHInBoxT_1d4000000_3999999d4000000_91389_91417
import RHInBoxT_1d4000000_3999999d4000000_91417_91444
import RHInBoxT_1d4000000_3999999d4000000_91444_91472
import RHInBoxT_1d4000000_3999999d4000000_91472_366001d4
import RHInBoxT_1d4000000_3999999d4000000_91500_91528
import RHInBoxT_1d4000000_3999999d4000000_91528_91556
import RHInBoxT_1d4000000_3999999d4000000_91556_366333d4
import RHInBoxT_1d4000000_3999999d4000000_91583_91611
import RHInBoxT_1d4000000_3999999d4000000_91611_91639
import RHInBoxT_1d4000000_3999999d4000000_91639_366669d4
import RHInBoxT_1d4000000_3999999d4000000_91667_91694
import RHInBoxT_1d4000000_3999999d4000000_366775d4_91722
import RHInBoxT_1d4000000_3999999d4000000_366887d4_91750
import RHInBoxT_1d4000000_3999999d4000000_91750_91778
import RHInBoxT_1d4000000_3999999d4000000_91778_91806
import RHInBoxT_1d4000000_3999999d4000000_91806_91833
import RHInBoxT_1d4000000_3999999d4000000_91833_91861
import RHInBoxT_1d4000000_3999999d4000000_91861_91889
import RHInBoxT_1d4000000_3999999d4000000_91889_91917
import RHInBoxT_1d4000000_3999999d4000000_367667d4_91944
import RHInBoxT_1d4000000_3999999d4000000_367775d4_91972
import RHInBoxT_1d4000000_3999999d4000000_91972_92000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h92000

/-- The 36-band NOMINAL partition of `[91000, 92000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 91000
  | 1 => 91028
  | 2 => 91056
  | 3 => 91083
  | 4 => 91111
  | 5 => 91139
  | 6 => 91167
  | 7 => 91194
  | 8 => 91222
  | 9 => 91250
  | 10 => 91278
  | 11 => 91306
  | 12 => 91333
  | 13 => 91361
  | 14 => 91389
  | 15 => 91417
  | 16 => 91444
  | 17 => 91472
  | 18 => 91500
  | 19 => 91528
  | 20 => 91556
  | 21 => 91583
  | 22 => 91611
  | 23 => 91639
  | 24 => 91667
  | 25 => 91694
  | 26 => 91722
  | 27 => 91750
  | 28 => 91778
  | 29 => 91806
  | 30 => 91833
  | 31 => 91861
  | 32 => 91889
  | 33 => 91917
  | 34 => 91944
  | 35 => 91972
  | 36 => 92000
  | _ => 92000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((91000:ℝ)) ≤ (91028); norm_num
  · show ((91028:ℝ)) ≤ (91056); norm_num
  · show ((91056:ℝ)) ≤ (91083); norm_num
  · show ((91083:ℝ)) ≤ (91111); norm_num
  · show ((91111:ℝ)) ≤ (91139); norm_num
  · show ((91139:ℝ)) ≤ (91167); norm_num
  · show ((91167:ℝ)) ≤ (91194); norm_num
  · show ((91194:ℝ)) ≤ (91222); norm_num
  · show ((91222:ℝ)) ≤ (91250); norm_num
  · show ((91250:ℝ)) ≤ (91278); norm_num
  · show ((91278:ℝ)) ≤ (91306); norm_num
  · show ((91306:ℝ)) ≤ (91333); norm_num
  · show ((91333:ℝ)) ≤ (91361); norm_num
  · show ((91361:ℝ)) ≤ (91389); norm_num
  · show ((91389:ℝ)) ≤ (91417); norm_num
  · show ((91417:ℝ)) ≤ (91444); norm_num
  · show ((91444:ℝ)) ≤ (91472); norm_num
  · show ((91472:ℝ)) ≤ (91500); norm_num
  · show ((91500:ℝ)) ≤ (91528); norm_num
  · show ((91528:ℝ)) ≤ (91556); norm_num
  · show ((91556:ℝ)) ≤ (91583); norm_num
  · show ((91583:ℝ)) ≤ (91611); norm_num
  · show ((91611:ℝ)) ≤ (91639); norm_num
  · show ((91639:ℝ)) ≤ (91667); norm_num
  · show ((91667:ℝ)) ≤ (91694); norm_num
  · show ((91694:ℝ)) ≤ (91722); norm_num
  · show ((91722:ℝ)) ≤ (91750); norm_num
  · show ((91750:ℝ)) ≤ (91778); norm_num
  · show ((91778:ℝ)) ≤ (91806); norm_num
  · show ((91806:ℝ)) ≤ (91833); norm_num
  · show ((91833:ℝ)) ≤ (91861); norm_num
  · show ((91861:ℝ)) ≤ (91889); norm_num
  · show ((91889:ℝ)) ≤ (91917); norm_num
  · show ((91917:ℝ)) ≤ (91944); norm_num
  · show ((91944:ℝ)) ≤ (91972); norm_num
  · show ((91972:ℝ)) ≤ (92000); norm_num
  · show ((92000:ℝ)) ≤ (92000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 91000
  | 1 => 91028
  | 2 => 91056
  | 3 => 91083
  | 4 => 91111
  | 5 => 91139
  | 6 => 364667 / 4
  | 7 => 91194
  | 8 => 91222
  | 9 => 91250
  | 10 => 91278
  | 11 => 91306
  | 12 => 91333
  | 13 => 365443 / 4
  | 14 => 91389
  | 15 => 91417
  | 16 => 91444
  | 17 => 91472
  | 18 => 91500
  | 19 => 91528
  | 20 => 91556
  | 21 => 91583
  | 22 => 91611
  | 23 => 91639
  | 24 => 91667
  | 25 => 366775 / 4
  | 26 => 366887 / 4
  | 27 => 91750
  | 28 => 91778
  | 29 => 91806
  | 30 => 91833
  | 31 => 91861
  | 32 => 91889
  | 33 => 367667 / 4
  | 34 => 367775 / 4
  | 35 => 91972
  | _ => 91972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 364113 / 4
  | 1 => 364225 / 4
  | 2 => 91083
  | 3 => 364445 / 4
  | 4 => 91139
  | 5 => 91167
  | 6 => 91194
  | 7 => 91222
  | 8 => 91250
  | 9 => 91278
  | 10 => 91306
  | 11 => 91333
  | 12 => 91361
  | 13 => 91389
  | 14 => 91417
  | 15 => 91444
  | 16 => 91472
  | 17 => 366001 / 4
  | 18 => 91528
  | 19 => 91556
  | 20 => 366333 / 4
  | 21 => 91611
  | 22 => 91639
  | 23 => 366669 / 4
  | 24 => 91694
  | 25 => 91722
  | 26 => 91750
  | 27 => 91778
  | 28 => 91806
  | 29 => 91833
  | 30 => 91861
  | 31 => 91889
  | 32 => 91917
  | 33 => 91944
  | 34 => 91972
  | 35 => 92000
  | _ => 92000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 92000` (`log 92000 ≤ 12`, `2.7^12 ≥ 92000`). -/
theorem haC_92000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 92000 := by
  have hlog : Real.log 92000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 92000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 92000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[91000, 92000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[91000, 92000]` SEGMENT: every zero with `91000 ≤ Im ≤ 92000` is on the line. -/
theorem segment_91000_92000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 92000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (91000:ℝ) ≤ ρ.im → ρ.im ≤ 92000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 91000 92000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_92000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 92000 via the HEIGHT CHAIN**: `[0,91000]` ∘ `[91000,92000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_92000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 92000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 92000 → ρ.re = 1 / 2 := by
  have hγ91000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 91000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 91000 92000
    (AllZeros_h91000.all_nontrivial_zeros_up_to_height_91000_of_bands
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
      hγ91000)
    (segment_91000_92000 hbands hγ)

end AllZeros_h92000
