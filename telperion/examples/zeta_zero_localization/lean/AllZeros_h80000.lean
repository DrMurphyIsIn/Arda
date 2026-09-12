/-  Height-chain step: all nontrivial zeta zeros up to height 80000 on Re = 1/2 --
    `AllZeros_h79000` + a `[79000, 80000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h79000
import RHInBoxT_1d4000000_3999999d4000000_79000_79028
import RHInBoxT_1d4000000_3999999d4000000_79028_79056
import RHInBoxT_1d4000000_3999999d4000000_79056_79083
import RHInBoxT_1d4000000_3999999d4000000_79083_79111
import RHInBoxT_1d4000000_3999999d4000000_79111_79139
import RHInBoxT_1d4000000_3999999d4000000_79139_79167
import RHInBoxT_1d4000000_3999999d4000000_79167_79194
import RHInBoxT_1d4000000_3999999d4000000_79194_79222
import RHInBoxT_1d4000000_3999999d4000000_79222_79250
import RHInBoxT_1d4000000_3999999d4000000_79250_317113d4
import RHInBoxT_1d4000000_3999999d4000000_79278_79306
import RHInBoxT_1d4000000_3999999d4000000_317223d4_79333
import RHInBoxT_1d4000000_3999999d4000000_79333_79361
import RHInBoxT_1d4000000_3999999d4000000_79361_79389
import RHInBoxT_1d4000000_3999999d4000000_79389_79417
import RHInBoxT_1d4000000_3999999d4000000_79417_79444
import RHInBoxT_1d4000000_3999999d4000000_79444_79472
import RHInBoxT_1d4000000_3999999d4000000_79472_79500
import RHInBoxT_1d4000000_3999999d4000000_79500_79528
import RHInBoxT_1d4000000_3999999d4000000_79528_318225d4
import RHInBoxT_1d4000000_3999999d4000000_79556_318333d4
import RHInBoxT_1d4000000_3999999d4000000_79583_79611
import RHInBoxT_1d4000000_3999999d4000000_318443d4_79639
import RHInBoxT_1d4000000_3999999d4000000_79639_79667
import RHInBoxT_1d4000000_3999999d4000000_318667d4_79694
import RHInBoxT_1d4000000_3999999d4000000_79694_79722
import RHInBoxT_1d4000000_3999999d4000000_79722_79750
import RHInBoxT_1d4000000_3999999d4000000_79750_79778
import RHInBoxT_1d4000000_3999999d4000000_319111d4_79806
import RHInBoxT_1d4000000_3999999d4000000_79806_79833
import RHInBoxT_1d4000000_3999999d4000000_319331d4_79861
import RHInBoxT_1d4000000_3999999d4000000_79861_79889
import RHInBoxT_1d4000000_3999999d4000000_79889_79917
import RHInBoxT_1d4000000_3999999d4000000_79917_319777d4
import RHInBoxT_1d4000000_3999999d4000000_79944_79972
import RHInBoxT_1d4000000_3999999d4000000_319887d4_80000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h80000

/-- The 36-band NOMINAL partition of `[79000, 80000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 79000
  | 1 => 79028
  | 2 => 79056
  | 3 => 79083
  | 4 => 79111
  | 5 => 79139
  | 6 => 79167
  | 7 => 79194
  | 8 => 79222
  | 9 => 79250
  | 10 => 79278
  | 11 => 79306
  | 12 => 79333
  | 13 => 79361
  | 14 => 79389
  | 15 => 79417
  | 16 => 79444
  | 17 => 79472
  | 18 => 79500
  | 19 => 79528
  | 20 => 79556
  | 21 => 79583
  | 22 => 79611
  | 23 => 79639
  | 24 => 79667
  | 25 => 79694
  | 26 => 79722
  | 27 => 79750
  | 28 => 79778
  | 29 => 79806
  | 30 => 79833
  | 31 => 79861
  | 32 => 79889
  | 33 => 79917
  | 34 => 79944
  | 35 => 79972
  | 36 => 80000
  | _ => 80000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((79000:ℝ)) ≤ (79028); norm_num
  · show ((79028:ℝ)) ≤ (79056); norm_num
  · show ((79056:ℝ)) ≤ (79083); norm_num
  · show ((79083:ℝ)) ≤ (79111); norm_num
  · show ((79111:ℝ)) ≤ (79139); norm_num
  · show ((79139:ℝ)) ≤ (79167); norm_num
  · show ((79167:ℝ)) ≤ (79194); norm_num
  · show ((79194:ℝ)) ≤ (79222); norm_num
  · show ((79222:ℝ)) ≤ (79250); norm_num
  · show ((79250:ℝ)) ≤ (79278); norm_num
  · show ((79278:ℝ)) ≤ (79306); norm_num
  · show ((79306:ℝ)) ≤ (79333); norm_num
  · show ((79333:ℝ)) ≤ (79361); norm_num
  · show ((79361:ℝ)) ≤ (79389); norm_num
  · show ((79389:ℝ)) ≤ (79417); norm_num
  · show ((79417:ℝ)) ≤ (79444); norm_num
  · show ((79444:ℝ)) ≤ (79472); norm_num
  · show ((79472:ℝ)) ≤ (79500); norm_num
  · show ((79500:ℝ)) ≤ (79528); norm_num
  · show ((79528:ℝ)) ≤ (79556); norm_num
  · show ((79556:ℝ)) ≤ (79583); norm_num
  · show ((79583:ℝ)) ≤ (79611); norm_num
  · show ((79611:ℝ)) ≤ (79639); norm_num
  · show ((79639:ℝ)) ≤ (79667); norm_num
  · show ((79667:ℝ)) ≤ (79694); norm_num
  · show ((79694:ℝ)) ≤ (79722); norm_num
  · show ((79722:ℝ)) ≤ (79750); norm_num
  · show ((79750:ℝ)) ≤ (79778); norm_num
  · show ((79778:ℝ)) ≤ (79806); norm_num
  · show ((79806:ℝ)) ≤ (79833); norm_num
  · show ((79833:ℝ)) ≤ (79861); norm_num
  · show ((79861:ℝ)) ≤ (79889); norm_num
  · show ((79889:ℝ)) ≤ (79917); norm_num
  · show ((79917:ℝ)) ≤ (79944); norm_num
  · show ((79944:ℝ)) ≤ (79972); norm_num
  · show ((79972:ℝ)) ≤ (80000); norm_num
  · show ((80000:ℝ)) ≤ (80000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 79000
  | 1 => 79028
  | 2 => 79056
  | 3 => 79083
  | 4 => 79111
  | 5 => 79139
  | 6 => 79167
  | 7 => 79194
  | 8 => 79222
  | 9 => 79250
  | 10 => 79278
  | 11 => 317223 / 4
  | 12 => 79333
  | 13 => 79361
  | 14 => 79389
  | 15 => 79417
  | 16 => 79444
  | 17 => 79472
  | 18 => 79500
  | 19 => 79528
  | 20 => 79556
  | 21 => 79583
  | 22 => 318443 / 4
  | 23 => 79639
  | 24 => 318667 / 4
  | 25 => 79694
  | 26 => 79722
  | 27 => 79750
  | 28 => 319111 / 4
  | 29 => 79806
  | 30 => 319331 / 4
  | 31 => 79861
  | 32 => 79889
  | 33 => 79917
  | 34 => 79944
  | 35 => 319887 / 4
  | _ => 319887 / 4

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 79028
  | 1 => 79056
  | 2 => 79083
  | 3 => 79111
  | 4 => 79139
  | 5 => 79167
  | 6 => 79194
  | 7 => 79222
  | 8 => 79250
  | 9 => 317113 / 4
  | 10 => 79306
  | 11 => 79333
  | 12 => 79361
  | 13 => 79389
  | 14 => 79417
  | 15 => 79444
  | 16 => 79472
  | 17 => 79500
  | 18 => 79528
  | 19 => 318225 / 4
  | 20 => 318333 / 4
  | 21 => 79611
  | 22 => 79639
  | 23 => 79667
  | 24 => 79694
  | 25 => 79722
  | 26 => 79750
  | 27 => 79778
  | 28 => 79806
  | 29 => 79833
  | 30 => 79861
  | 31 => 79889
  | 32 => 79917
  | 33 => 319777 / 4
  | 34 => 79972
  | 35 => 80000
  | _ => 80000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 80000` (`log 80000 ≤ 12`, `2.7^12 ≥ 80000`). -/
theorem haC_80000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 80000 := by
  have hlog : Real.log 80000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 80000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 80000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[79000, 80000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[79000, 80000]` SEGMENT: every zero with `79000 ≤ Im ≤ 80000` is on the line. -/
theorem segment_79000_80000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 80000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (79000:ℝ) ≤ ρ.im → ρ.im ≤ 80000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 79000 80000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_80000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 80000 via the HEIGHT CHAIN**: `[0,79000]` ∘ `[79000,80000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_80000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 80000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 80000 → ρ.re = 1 / 2 := by
  have hγ79000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 79000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 79000 80000
    (AllZeros_h79000.all_nontrivial_zeros_up_to_height_79000_of_bands
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
      hγ79000)
    (segment_79000_80000 hbands hγ)

end AllZeros_h80000
