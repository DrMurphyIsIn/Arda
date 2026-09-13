/-  Height-chain step: all nontrivial zeta zeros up to height 86000 on Re = 1/2 --
    `AllZeros_h85000` + a `[85000, 86000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h85000
import RHInBoxT_1d4000000_3999999d4000000_85000_85028
import RHInBoxT_1d4000000_3999999d4000000_85028_85056
import RHInBoxT_1d4000000_3999999d4000000_85056_85083
import RHInBoxT_1d4000000_3999999d4000000_340331d4_85111
import RHInBoxT_1d4000000_3999999d4000000_340443d4_85139
import RHInBoxT_1d4000000_3999999d4000000_85139_85167
import RHInBoxT_1d4000000_3999999d4000000_340667d4_85194
import RHInBoxT_1d4000000_3999999d4000000_85194_85222
import RHInBoxT_1d4000000_3999999d4000000_85222_85250
import RHInBoxT_1d4000000_3999999d4000000_85250_85278
import RHInBoxT_1d4000000_3999999d4000000_85278_85306
import RHInBoxT_1d4000000_3999999d4000000_85306_341333d4
import RHInBoxT_1d4000000_3999999d4000000_85333_85361
import RHInBoxT_1d4000000_3999999d4000000_85361_85389
import RHInBoxT_1d4000000_3999999d4000000_85389_85417
import RHInBoxT_1d4000000_3999999d4000000_85417_85444
import RHInBoxT_1d4000000_3999999d4000000_85444_85472
import RHInBoxT_1d4000000_3999999d4000000_85472_85500
import RHInBoxT_1d4000000_3999999d4000000_85500_85528
import RHInBoxT_1d4000000_3999999d4000000_85528_342225d4
import RHInBoxT_1d4000000_3999999d4000000_85556_85583
import RHInBoxT_1d4000000_3999999d4000000_85583_85611
import RHInBoxT_1d4000000_3999999d4000000_85611_85639
import RHInBoxT_1d4000000_3999999d4000000_85639_85667
import RHInBoxT_1d4000000_3999999d4000000_85667_85694
import RHInBoxT_1d4000000_3999999d4000000_85694_85722
import RHInBoxT_1d4000000_3999999d4000000_342887d4_85750
import RHInBoxT_1d4000000_3999999d4000000_85750_343113d4
import RHInBoxT_1d4000000_3999999d4000000_85778_343225d4
import RHInBoxT_1d4000000_3999999d4000000_85806_85833
import RHInBoxT_1d4000000_3999999d4000000_85833_85861
import RHInBoxT_1d4000000_3999999d4000000_85861_85889
import RHInBoxT_1d4000000_3999999d4000000_85889_85917
import RHInBoxT_1d4000000_3999999d4000000_85917_343777d4
import RHInBoxT_1d4000000_3999999d4000000_85944_85972
import RHInBoxT_1d4000000_3999999d4000000_85972_86000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h86000

/-- The 36-band NOMINAL partition of `[85000, 86000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 85000
  | 1 => 85028
  | 2 => 85056
  | 3 => 85083
  | 4 => 85111
  | 5 => 85139
  | 6 => 85167
  | 7 => 85194
  | 8 => 85222
  | 9 => 85250
  | 10 => 85278
  | 11 => 85306
  | 12 => 85333
  | 13 => 85361
  | 14 => 85389
  | 15 => 85417
  | 16 => 85444
  | 17 => 85472
  | 18 => 85500
  | 19 => 85528
  | 20 => 85556
  | 21 => 85583
  | 22 => 85611
  | 23 => 85639
  | 24 => 85667
  | 25 => 85694
  | 26 => 85722
  | 27 => 85750
  | 28 => 85778
  | 29 => 85806
  | 30 => 85833
  | 31 => 85861
  | 32 => 85889
  | 33 => 85917
  | 34 => 85944
  | 35 => 85972
  | 36 => 86000
  | _ => 86000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((85000:ℝ)) ≤ (85028); norm_num
  · show ((85028:ℝ)) ≤ (85056); norm_num
  · show ((85056:ℝ)) ≤ (85083); norm_num
  · show ((85083:ℝ)) ≤ (85111); norm_num
  · show ((85111:ℝ)) ≤ (85139); norm_num
  · show ((85139:ℝ)) ≤ (85167); norm_num
  · show ((85167:ℝ)) ≤ (85194); norm_num
  · show ((85194:ℝ)) ≤ (85222); norm_num
  · show ((85222:ℝ)) ≤ (85250); norm_num
  · show ((85250:ℝ)) ≤ (85278); norm_num
  · show ((85278:ℝ)) ≤ (85306); norm_num
  · show ((85306:ℝ)) ≤ (85333); norm_num
  · show ((85333:ℝ)) ≤ (85361); norm_num
  · show ((85361:ℝ)) ≤ (85389); norm_num
  · show ((85389:ℝ)) ≤ (85417); norm_num
  · show ((85417:ℝ)) ≤ (85444); norm_num
  · show ((85444:ℝ)) ≤ (85472); norm_num
  · show ((85472:ℝ)) ≤ (85500); norm_num
  · show ((85500:ℝ)) ≤ (85528); norm_num
  · show ((85528:ℝ)) ≤ (85556); norm_num
  · show ((85556:ℝ)) ≤ (85583); norm_num
  · show ((85583:ℝ)) ≤ (85611); norm_num
  · show ((85611:ℝ)) ≤ (85639); norm_num
  · show ((85639:ℝ)) ≤ (85667); norm_num
  · show ((85667:ℝ)) ≤ (85694); norm_num
  · show ((85694:ℝ)) ≤ (85722); norm_num
  · show ((85722:ℝ)) ≤ (85750); norm_num
  · show ((85750:ℝ)) ≤ (85778); norm_num
  · show ((85778:ℝ)) ≤ (85806); norm_num
  · show ((85806:ℝ)) ≤ (85833); norm_num
  · show ((85833:ℝ)) ≤ (85861); norm_num
  · show ((85861:ℝ)) ≤ (85889); norm_num
  · show ((85889:ℝ)) ≤ (85917); norm_num
  · show ((85917:ℝ)) ≤ (85944); norm_num
  · show ((85944:ℝ)) ≤ (85972); norm_num
  · show ((85972:ℝ)) ≤ (86000); norm_num
  · show ((86000:ℝ)) ≤ (86000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 85000
  | 1 => 85028
  | 2 => 85056
  | 3 => 340331 / 4
  | 4 => 340443 / 4
  | 5 => 85139
  | 6 => 340667 / 4
  | 7 => 85194
  | 8 => 85222
  | 9 => 85250
  | 10 => 85278
  | 11 => 85306
  | 12 => 85333
  | 13 => 85361
  | 14 => 85389
  | 15 => 85417
  | 16 => 85444
  | 17 => 85472
  | 18 => 85500
  | 19 => 85528
  | 20 => 85556
  | 21 => 85583
  | 22 => 85611
  | 23 => 85639
  | 24 => 85667
  | 25 => 85694
  | 26 => 342887 / 4
  | 27 => 85750
  | 28 => 85778
  | 29 => 85806
  | 30 => 85833
  | 31 => 85861
  | 32 => 85889
  | 33 => 85917
  | 34 => 85944
  | 35 => 85972
  | _ => 85972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 85028
  | 1 => 85056
  | 2 => 85083
  | 3 => 85111
  | 4 => 85139
  | 5 => 85167
  | 6 => 85194
  | 7 => 85222
  | 8 => 85250
  | 9 => 85278
  | 10 => 85306
  | 11 => 341333 / 4
  | 12 => 85361
  | 13 => 85389
  | 14 => 85417
  | 15 => 85444
  | 16 => 85472
  | 17 => 85500
  | 18 => 85528
  | 19 => 342225 / 4
  | 20 => 85583
  | 21 => 85611
  | 22 => 85639
  | 23 => 85667
  | 24 => 85694
  | 25 => 85722
  | 26 => 85750
  | 27 => 343113 / 4
  | 28 => 343225 / 4
  | 29 => 85833
  | 30 => 85861
  | 31 => 85889
  | 32 => 85917
  | 33 => 343777 / 4
  | 34 => 85972
  | 35 => 86000
  | _ => 86000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 86000` (`log 86000 ≤ 12`, `2.7^12 ≥ 86000`). -/
theorem haC_86000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 86000 := by
  have hlog : Real.log 86000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 86000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 86000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[85000, 86000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[85000, 86000]` SEGMENT: every zero with `85000 ≤ Im ≤ 86000` is on the line. -/
theorem segment_85000_86000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 86000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (85000:ℝ) ≤ ρ.im → ρ.im ≤ 86000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 85000 86000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_86000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 86000 via the HEIGHT CHAIN**: `[0,85000]` ∘ `[85000,86000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_86000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 86000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 86000 → ρ.re = 1 / 2 := by
  have hγ85000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 85000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 85000 86000
    (AllZeros_h85000.all_nontrivial_zeros_up_to_height_85000_of_bands
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
      hγ85000)
    (segment_85000_86000 hbands hγ)

end AllZeros_h86000
