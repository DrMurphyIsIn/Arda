/-  Height-chain step: all nontrivial zeta zeros up to height 71000 on Re = 1/2 --
    `AllZeros_h70000` + a `[70000, 71000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h70000
import RHInBoxT_1d4000000_3999999d4000000_70000_70028
import RHInBoxT_1d4000000_3999999d4000000_70028_70056
import RHInBoxT_1d4000000_3999999d4000000_280223d4_70083
import RHInBoxT_1d4000000_3999999d4000000_70083_280445d4
import RHInBoxT_1d4000000_3999999d4000000_70111_70139
import RHInBoxT_1d4000000_3999999d4000000_280555d4_70167
import RHInBoxT_1d4000000_3999999d4000000_70167_70194
import RHInBoxT_1d4000000_3999999d4000000_70194_70222
import RHInBoxT_1d4000000_3999999d4000000_280887d4_70250
import RHInBoxT_1d4000000_3999999d4000000_70250_70278
import RHInBoxT_1d4000000_3999999d4000000_70278_70306
import RHInBoxT_1d4000000_3999999d4000000_70306_70333
import RHInBoxT_1d4000000_3999999d4000000_70333_70361
import RHInBoxT_1d4000000_3999999d4000000_70361_70389
import RHInBoxT_1d4000000_3999999d4000000_70389_70417
import RHInBoxT_1d4000000_3999999d4000000_70417_70444
import RHInBoxT_1d4000000_3999999d4000000_70444_70472
import RHInBoxT_1d4000000_3999999d4000000_70472_70500
import RHInBoxT_1d4000000_3999999d4000000_70500_70528
import RHInBoxT_1d4000000_3999999d4000000_70528_70556
import RHInBoxT_1d4000000_3999999d4000000_70556_70583
import RHInBoxT_1d4000000_3999999d4000000_70583_70611
import RHInBoxT_1d4000000_3999999d4000000_70611_70639
import RHInBoxT_1d4000000_3999999d4000000_70639_70667
import RHInBoxT_1d4000000_3999999d4000000_70667_282777d4
import RHInBoxT_1d4000000_3999999d4000000_70694_70722
import RHInBoxT_1d4000000_3999999d4000000_70722_70750
import RHInBoxT_1d4000000_3999999d4000000_70750_70778
import RHInBoxT_1d4000000_3999999d4000000_70778_70806
import RHInBoxT_1d4000000_3999999d4000000_283223d4_70833
import RHInBoxT_1d4000000_3999999d4000000_70833_70861
import RHInBoxT_1d4000000_3999999d4000000_70861_70889
import RHInBoxT_1d4000000_3999999d4000000_70889_70917
import RHInBoxT_1d4000000_3999999d4000000_283667d4_70944
import RHInBoxT_1d4000000_3999999d4000000_70944_70972
import RHInBoxT_1d4000000_3999999d4000000_70972_71000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h71000

/-- The 36-band NOMINAL partition of `[70000, 71000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 70000
  | 1 => 70028
  | 2 => 70056
  | 3 => 70083
  | 4 => 70111
  | 5 => 70139
  | 6 => 70167
  | 7 => 70194
  | 8 => 70222
  | 9 => 70250
  | 10 => 70278
  | 11 => 70306
  | 12 => 70333
  | 13 => 70361
  | 14 => 70389
  | 15 => 70417
  | 16 => 70444
  | 17 => 70472
  | 18 => 70500
  | 19 => 70528
  | 20 => 70556
  | 21 => 70583
  | 22 => 70611
  | 23 => 70639
  | 24 => 70667
  | 25 => 70694
  | 26 => 70722
  | 27 => 70750
  | 28 => 70778
  | 29 => 70806
  | 30 => 70833
  | 31 => 70861
  | 32 => 70889
  | 33 => 70917
  | 34 => 70944
  | 35 => 70972
  | 36 => 71000
  | _ => 71000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((70000:ℝ)) ≤ (70028); norm_num
  · show ((70028:ℝ)) ≤ (70056); norm_num
  · show ((70056:ℝ)) ≤ (70083); norm_num
  · show ((70083:ℝ)) ≤ (70111); norm_num
  · show ((70111:ℝ)) ≤ (70139); norm_num
  · show ((70139:ℝ)) ≤ (70167); norm_num
  · show ((70167:ℝ)) ≤ (70194); norm_num
  · show ((70194:ℝ)) ≤ (70222); norm_num
  · show ((70222:ℝ)) ≤ (70250); norm_num
  · show ((70250:ℝ)) ≤ (70278); norm_num
  · show ((70278:ℝ)) ≤ (70306); norm_num
  · show ((70306:ℝ)) ≤ (70333); norm_num
  · show ((70333:ℝ)) ≤ (70361); norm_num
  · show ((70361:ℝ)) ≤ (70389); norm_num
  · show ((70389:ℝ)) ≤ (70417); norm_num
  · show ((70417:ℝ)) ≤ (70444); norm_num
  · show ((70444:ℝ)) ≤ (70472); norm_num
  · show ((70472:ℝ)) ≤ (70500); norm_num
  · show ((70500:ℝ)) ≤ (70528); norm_num
  · show ((70528:ℝ)) ≤ (70556); norm_num
  · show ((70556:ℝ)) ≤ (70583); norm_num
  · show ((70583:ℝ)) ≤ (70611); norm_num
  · show ((70611:ℝ)) ≤ (70639); norm_num
  · show ((70639:ℝ)) ≤ (70667); norm_num
  · show ((70667:ℝ)) ≤ (70694); norm_num
  · show ((70694:ℝ)) ≤ (70722); norm_num
  · show ((70722:ℝ)) ≤ (70750); norm_num
  · show ((70750:ℝ)) ≤ (70778); norm_num
  · show ((70778:ℝ)) ≤ (70806); norm_num
  · show ((70806:ℝ)) ≤ (70833); norm_num
  · show ((70833:ℝ)) ≤ (70861); norm_num
  · show ((70861:ℝ)) ≤ (70889); norm_num
  · show ((70889:ℝ)) ≤ (70917); norm_num
  · show ((70917:ℝ)) ≤ (70944); norm_num
  · show ((70944:ℝ)) ≤ (70972); norm_num
  · show ((70972:ℝ)) ≤ (71000); norm_num
  · show ((71000:ℝ)) ≤ (71000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 70000
  | 1 => 70028
  | 2 => 280223 / 4
  | 3 => 70083
  | 4 => 70111
  | 5 => 280555 / 4
  | 6 => 70167
  | 7 => 70194
  | 8 => 280887 / 4
  | 9 => 70250
  | 10 => 70278
  | 11 => 70306
  | 12 => 70333
  | 13 => 70361
  | 14 => 70389
  | 15 => 70417
  | 16 => 70444
  | 17 => 70472
  | 18 => 70500
  | 19 => 70528
  | 20 => 70556
  | 21 => 70583
  | 22 => 70611
  | 23 => 70639
  | 24 => 70667
  | 25 => 70694
  | 26 => 70722
  | 27 => 70750
  | 28 => 70778
  | 29 => 283223 / 4
  | 30 => 70833
  | 31 => 70861
  | 32 => 70889
  | 33 => 283667 / 4
  | 34 => 70944
  | 35 => 70972
  | _ => 70972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 70028
  | 1 => 70056
  | 2 => 70083
  | 3 => 280445 / 4
  | 4 => 70139
  | 5 => 70167
  | 6 => 70194
  | 7 => 70222
  | 8 => 70250
  | 9 => 70278
  | 10 => 70306
  | 11 => 70333
  | 12 => 70361
  | 13 => 70389
  | 14 => 70417
  | 15 => 70444
  | 16 => 70472
  | 17 => 70500
  | 18 => 70528
  | 19 => 70556
  | 20 => 70583
  | 21 => 70611
  | 22 => 70639
  | 23 => 70667
  | 24 => 282777 / 4
  | 25 => 70722
  | 26 => 70750
  | 27 => 70778
  | 28 => 70806
  | 29 => 70833
  | 30 => 70861
  | 31 => 70889
  | 32 => 70917
  | 33 => 70944
  | 34 => 70972
  | 35 => 71000
  | _ => 71000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 71000` (`log 71000 ≤ 12`, `2.7^12 ≥ 71000`). -/
theorem haC_71000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 71000 := by
  have hlog : Real.log 71000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 71000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 71000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[70000, 71000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[70000, 71000]` SEGMENT: every zero with `70000 ≤ Im ≤ 71000` is on the line. -/
theorem segment_70000_71000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 71000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (70000:ℝ) ≤ ρ.im → ρ.im ≤ 71000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 70000 71000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_71000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 71000 via the HEIGHT CHAIN**: `[0,70000]` ∘ `[70000,71000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_71000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 71000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 71000 → ρ.re = 1 / 2 := by
  have hγ70000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 70000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 70000 71000
    (AllZeros_h70000.all_nontrivial_zeros_up_to_height_70000_of_bands
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
      hγ70000)
    (segment_70000_71000 hbands hγ)

end AllZeros_h71000
