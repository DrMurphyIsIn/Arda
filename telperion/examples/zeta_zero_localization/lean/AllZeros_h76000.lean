/-  Height-chain step: all nontrivial zeta zeros up to height 76000 on Re = 1/2 --
    `AllZeros_h75000` + a `[75000, 76000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h75000
import RHInBoxT_1d4000000_3999999d4000000_75000_75028
import RHInBoxT_1d4000000_3999999d4000000_75028_75056
import RHInBoxT_1d4000000_3999999d4000000_75056_300333d4
import RHInBoxT_1d4000000_3999999d4000000_75083_75111
import RHInBoxT_1d4000000_3999999d4000000_75111_75139
import RHInBoxT_1d4000000_3999999d4000000_300555d4_75167
import RHInBoxT_1d4000000_3999999d4000000_75167_75194
import RHInBoxT_1d4000000_3999999d4000000_75194_75222
import RHInBoxT_1d4000000_3999999d4000000_75222_75250
import RHInBoxT_1d4000000_3999999d4000000_75250_75278
import RHInBoxT_1d4000000_3999999d4000000_75278_75306
import RHInBoxT_1d4000000_3999999d4000000_75306_75333
import RHInBoxT_1d4000000_3999999d4000000_75333_75361
import RHInBoxT_1d4000000_3999999d4000000_301443d4_301557d4
import RHInBoxT_1d4000000_3999999d4000000_75389_75417
import RHInBoxT_1d4000000_3999999d4000000_75417_75444
import RHInBoxT_1d4000000_3999999d4000000_75444_75472
import RHInBoxT_1d4000000_3999999d4000000_75472_75500
import RHInBoxT_1d4000000_3999999d4000000_75500_75528
import RHInBoxT_1d4000000_3999999d4000000_75528_75556
import RHInBoxT_1d4000000_3999999d4000000_75556_75583
import RHInBoxT_1d4000000_3999999d4000000_75583_75611
import RHInBoxT_1d4000000_3999999d4000000_75611_75639
import RHInBoxT_1d4000000_3999999d4000000_75639_75667
import RHInBoxT_1d4000000_3999999d4000000_75667_75694
import RHInBoxT_1d4000000_3999999d4000000_75694_75722
import RHInBoxT_1d4000000_3999999d4000000_75722_75750
import RHInBoxT_1d4000000_3999999d4000000_75750_75778
import RHInBoxT_1d4000000_3999999d4000000_75778_75806
import RHInBoxT_1d4000000_3999999d4000000_75806_303333d4
import RHInBoxT_1d4000000_3999999d4000000_75833_75861
import RHInBoxT_1d4000000_3999999d4000000_75861_75889
import RHInBoxT_1d4000000_3999999d4000000_75889_303669d4
import RHInBoxT_1d4000000_3999999d4000000_75917_75944
import RHInBoxT_1d4000000_3999999d4000000_75944_75972
import RHInBoxT_1d4000000_3999999d4000000_75972_76000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h76000

/-- The 36-band NOMINAL partition of `[75000, 76000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 75000
  | 1 => 75028
  | 2 => 75056
  | 3 => 75083
  | 4 => 75111
  | 5 => 75139
  | 6 => 75167
  | 7 => 75194
  | 8 => 75222
  | 9 => 75250
  | 10 => 75278
  | 11 => 75306
  | 12 => 75333
  | 13 => 75361
  | 14 => 75389
  | 15 => 75417
  | 16 => 75444
  | 17 => 75472
  | 18 => 75500
  | 19 => 75528
  | 20 => 75556
  | 21 => 75583
  | 22 => 75611
  | 23 => 75639
  | 24 => 75667
  | 25 => 75694
  | 26 => 75722
  | 27 => 75750
  | 28 => 75778
  | 29 => 75806
  | 30 => 75833
  | 31 => 75861
  | 32 => 75889
  | 33 => 75917
  | 34 => 75944
  | 35 => 75972
  | 36 => 76000
  | _ => 76000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((75000:ℝ)) ≤ (75028); norm_num
  · show ((75028:ℝ)) ≤ (75056); norm_num
  · show ((75056:ℝ)) ≤ (75083); norm_num
  · show ((75083:ℝ)) ≤ (75111); norm_num
  · show ((75111:ℝ)) ≤ (75139); norm_num
  · show ((75139:ℝ)) ≤ (75167); norm_num
  · show ((75167:ℝ)) ≤ (75194); norm_num
  · show ((75194:ℝ)) ≤ (75222); norm_num
  · show ((75222:ℝ)) ≤ (75250); norm_num
  · show ((75250:ℝ)) ≤ (75278); norm_num
  · show ((75278:ℝ)) ≤ (75306); norm_num
  · show ((75306:ℝ)) ≤ (75333); norm_num
  · show ((75333:ℝ)) ≤ (75361); norm_num
  · show ((75361:ℝ)) ≤ (75389); norm_num
  · show ((75389:ℝ)) ≤ (75417); norm_num
  · show ((75417:ℝ)) ≤ (75444); norm_num
  · show ((75444:ℝ)) ≤ (75472); norm_num
  · show ((75472:ℝ)) ≤ (75500); norm_num
  · show ((75500:ℝ)) ≤ (75528); norm_num
  · show ((75528:ℝ)) ≤ (75556); norm_num
  · show ((75556:ℝ)) ≤ (75583); norm_num
  · show ((75583:ℝ)) ≤ (75611); norm_num
  · show ((75611:ℝ)) ≤ (75639); norm_num
  · show ((75639:ℝ)) ≤ (75667); norm_num
  · show ((75667:ℝ)) ≤ (75694); norm_num
  · show ((75694:ℝ)) ≤ (75722); norm_num
  · show ((75722:ℝ)) ≤ (75750); norm_num
  · show ((75750:ℝ)) ≤ (75778); norm_num
  · show ((75778:ℝ)) ≤ (75806); norm_num
  · show ((75806:ℝ)) ≤ (75833); norm_num
  · show ((75833:ℝ)) ≤ (75861); norm_num
  · show ((75861:ℝ)) ≤ (75889); norm_num
  · show ((75889:ℝ)) ≤ (75917); norm_num
  · show ((75917:ℝ)) ≤ (75944); norm_num
  · show ((75944:ℝ)) ≤ (75972); norm_num
  · show ((75972:ℝ)) ≤ (76000); norm_num
  · show ((76000:ℝ)) ≤ (76000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 75000
  | 1 => 75028
  | 2 => 75056
  | 3 => 75083
  | 4 => 75111
  | 5 => 300555 / 4
  | 6 => 75167
  | 7 => 75194
  | 8 => 75222
  | 9 => 75250
  | 10 => 75278
  | 11 => 75306
  | 12 => 75333
  | 13 => 301443 / 4
  | 14 => 75389
  | 15 => 75417
  | 16 => 75444
  | 17 => 75472
  | 18 => 75500
  | 19 => 75528
  | 20 => 75556
  | 21 => 75583
  | 22 => 75611
  | 23 => 75639
  | 24 => 75667
  | 25 => 75694
  | 26 => 75722
  | 27 => 75750
  | 28 => 75778
  | 29 => 75806
  | 30 => 75833
  | 31 => 75861
  | 32 => 75889
  | 33 => 75917
  | 34 => 75944
  | 35 => 75972
  | _ => 75972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 75028
  | 1 => 75056
  | 2 => 300333 / 4
  | 3 => 75111
  | 4 => 75139
  | 5 => 75167
  | 6 => 75194
  | 7 => 75222
  | 8 => 75250
  | 9 => 75278
  | 10 => 75306
  | 11 => 75333
  | 12 => 75361
  | 13 => 301557 / 4
  | 14 => 75417
  | 15 => 75444
  | 16 => 75472
  | 17 => 75500
  | 18 => 75528
  | 19 => 75556
  | 20 => 75583
  | 21 => 75611
  | 22 => 75639
  | 23 => 75667
  | 24 => 75694
  | 25 => 75722
  | 26 => 75750
  | 27 => 75778
  | 28 => 75806
  | 29 => 303333 / 4
  | 30 => 75861
  | 31 => 75889
  | 32 => 303669 / 4
  | 33 => 75944
  | 34 => 75972
  | 35 => 76000
  | _ => 76000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 76000` (`log 76000 ≤ 12`, `2.7^12 ≥ 76000`). -/
theorem haC_76000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 76000 := by
  have hlog : Real.log 76000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 76000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 76000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[75000, 76000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[75000, 76000]` SEGMENT: every zero with `75000 ≤ Im ≤ 76000` is on the line. -/
theorem segment_75000_76000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 76000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (75000:ℝ) ≤ ρ.im → ρ.im ≤ 76000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 75000 76000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_76000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 76000 via the HEIGHT CHAIN**: `[0,75000]` ∘ `[75000,76000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_76000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 76000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 76000 → ρ.re = 1 / 2 := by
  have hγ75000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 75000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 75000 76000
    (AllZeros_h75000.all_nontrivial_zeros_up_to_height_75000_of_bands
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
      hγ75000)
    (segment_75000_76000 hbands hγ)

end AllZeros_h76000
