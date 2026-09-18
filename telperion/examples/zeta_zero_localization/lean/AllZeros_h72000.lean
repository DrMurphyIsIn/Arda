/-  Height-chain step: all nontrivial zeta zeros up to height 72000 on Re = 1/2 --
    `AllZeros_h71000` + a `[71000, 72000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h71000
import RHInBoxT_1d4000000_3999999d4000000_283999d4_71028
import RHInBoxT_1d4000000_3999999d4000000_71028_71056
import RHInBoxT_1d4000000_3999999d4000000_71056_71083
import RHInBoxT_1d4000000_3999999d4000000_71083_71111
import RHInBoxT_1d4000000_3999999d4000000_71111_284557d4
import RHInBoxT_1d4000000_3999999d4000000_71139_71167
import RHInBoxT_1d4000000_3999999d4000000_71167_71194
import RHInBoxT_1d4000000_3999999d4000000_71194_71222
import RHInBoxT_1d4000000_3999999d4000000_71222_71250
import RHInBoxT_1d4000000_3999999d4000000_71250_71278
import RHInBoxT_1d4000000_3999999d4000000_71278_285225d4
import RHInBoxT_1d4000000_3999999d4000000_71306_285333d4
import RHInBoxT_1d4000000_3999999d4000000_71333_71361
import RHInBoxT_1d4000000_3999999d4000000_71361_71389
import RHInBoxT_1d4000000_3999999d4000000_71389_71417
import RHInBoxT_1d4000000_3999999d4000000_71417_285777d4
import RHInBoxT_1d4000000_3999999d4000000_71444_71472
import RHInBoxT_1d4000000_3999999d4000000_285887d4_71500
import RHInBoxT_1d4000000_3999999d4000000_285999d4_71528
import RHInBoxT_1d4000000_3999999d4000000_71528_71556
import RHInBoxT_1d4000000_3999999d4000000_71556_71583
import RHInBoxT_1d4000000_3999999d4000000_71583_286445d4
import RHInBoxT_1d4000000_3999999d4000000_71611_71639
import RHInBoxT_1d4000000_3999999d4000000_71639_71667
import RHInBoxT_1d4000000_3999999d4000000_71667_71694
import RHInBoxT_1d4000000_3999999d4000000_71694_286889d4
import RHInBoxT_1d4000000_3999999d4000000_71722_71750
import RHInBoxT_1d4000000_3999999d4000000_71750_71778
import RHInBoxT_1d4000000_3999999d4000000_71778_71806
import RHInBoxT_1d4000000_3999999d4000000_287223d4_71833
import RHInBoxT_1d4000000_3999999d4000000_71833_287445d4
import RHInBoxT_1d4000000_3999999d4000000_71861_71889
import RHInBoxT_1d4000000_3999999d4000000_71889_71917
import RHInBoxT_1d4000000_3999999d4000000_71917_71944
import RHInBoxT_1d4000000_3999999d4000000_71944_71972
import RHInBoxT_1d4000000_3999999d4000000_71972_72000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h72000

/-- The 36-band NOMINAL partition of `[71000, 72000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 71000
  | 1 => 71028
  | 2 => 71056
  | 3 => 71083
  | 4 => 71111
  | 5 => 71139
  | 6 => 71167
  | 7 => 71194
  | 8 => 71222
  | 9 => 71250
  | 10 => 71278
  | 11 => 71306
  | 12 => 71333
  | 13 => 71361
  | 14 => 71389
  | 15 => 71417
  | 16 => 71444
  | 17 => 71472
  | 18 => 71500
  | 19 => 71528
  | 20 => 71556
  | 21 => 71583
  | 22 => 71611
  | 23 => 71639
  | 24 => 71667
  | 25 => 71694
  | 26 => 71722
  | 27 => 71750
  | 28 => 71778
  | 29 => 71806
  | 30 => 71833
  | 31 => 71861
  | 32 => 71889
  | 33 => 71917
  | 34 => 71944
  | 35 => 71972
  | 36 => 72000
  | _ => 72000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((71000:ℝ)) ≤ (71028); norm_num
  · show ((71028:ℝ)) ≤ (71056); norm_num
  · show ((71056:ℝ)) ≤ (71083); norm_num
  · show ((71083:ℝ)) ≤ (71111); norm_num
  · show ((71111:ℝ)) ≤ (71139); norm_num
  · show ((71139:ℝ)) ≤ (71167); norm_num
  · show ((71167:ℝ)) ≤ (71194); norm_num
  · show ((71194:ℝ)) ≤ (71222); norm_num
  · show ((71222:ℝ)) ≤ (71250); norm_num
  · show ((71250:ℝ)) ≤ (71278); norm_num
  · show ((71278:ℝ)) ≤ (71306); norm_num
  · show ((71306:ℝ)) ≤ (71333); norm_num
  · show ((71333:ℝ)) ≤ (71361); norm_num
  · show ((71361:ℝ)) ≤ (71389); norm_num
  · show ((71389:ℝ)) ≤ (71417); norm_num
  · show ((71417:ℝ)) ≤ (71444); norm_num
  · show ((71444:ℝ)) ≤ (71472); norm_num
  · show ((71472:ℝ)) ≤ (71500); norm_num
  · show ((71500:ℝ)) ≤ (71528); norm_num
  · show ((71528:ℝ)) ≤ (71556); norm_num
  · show ((71556:ℝ)) ≤ (71583); norm_num
  · show ((71583:ℝ)) ≤ (71611); norm_num
  · show ((71611:ℝ)) ≤ (71639); norm_num
  · show ((71639:ℝ)) ≤ (71667); norm_num
  · show ((71667:ℝ)) ≤ (71694); norm_num
  · show ((71694:ℝ)) ≤ (71722); norm_num
  · show ((71722:ℝ)) ≤ (71750); norm_num
  · show ((71750:ℝ)) ≤ (71778); norm_num
  · show ((71778:ℝ)) ≤ (71806); norm_num
  · show ((71806:ℝ)) ≤ (71833); norm_num
  · show ((71833:ℝ)) ≤ (71861); norm_num
  · show ((71861:ℝ)) ≤ (71889); norm_num
  · show ((71889:ℝ)) ≤ (71917); norm_num
  · show ((71917:ℝ)) ≤ (71944); norm_num
  · show ((71944:ℝ)) ≤ (71972); norm_num
  · show ((71972:ℝ)) ≤ (72000); norm_num
  · show ((72000:ℝ)) ≤ (72000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 283999 / 4
  | 1 => 71028
  | 2 => 71056
  | 3 => 71083
  | 4 => 71111
  | 5 => 71139
  | 6 => 71167
  | 7 => 71194
  | 8 => 71222
  | 9 => 71250
  | 10 => 71278
  | 11 => 71306
  | 12 => 71333
  | 13 => 71361
  | 14 => 71389
  | 15 => 71417
  | 16 => 71444
  | 17 => 285887 / 4
  | 18 => 285999 / 4
  | 19 => 71528
  | 20 => 71556
  | 21 => 71583
  | 22 => 71611
  | 23 => 71639
  | 24 => 71667
  | 25 => 71694
  | 26 => 71722
  | 27 => 71750
  | 28 => 71778
  | 29 => 287223 / 4
  | 30 => 71833
  | 31 => 71861
  | 32 => 71889
  | 33 => 71917
  | 34 => 71944
  | 35 => 71972
  | _ => 71972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 71028
  | 1 => 71056
  | 2 => 71083
  | 3 => 71111
  | 4 => 284557 / 4
  | 5 => 71167
  | 6 => 71194
  | 7 => 71222
  | 8 => 71250
  | 9 => 71278
  | 10 => 285225 / 4
  | 11 => 285333 / 4
  | 12 => 71361
  | 13 => 71389
  | 14 => 71417
  | 15 => 285777 / 4
  | 16 => 71472
  | 17 => 71500
  | 18 => 71528
  | 19 => 71556
  | 20 => 71583
  | 21 => 286445 / 4
  | 22 => 71639
  | 23 => 71667
  | 24 => 71694
  | 25 => 286889 / 4
  | 26 => 71750
  | 27 => 71778
  | 28 => 71806
  | 29 => 71833
  | 30 => 287445 / 4
  | 31 => 71889
  | 32 => 71917
  | 33 => 71944
  | 34 => 71972
  | 35 => 72000
  | _ => 72000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 72000` (`log 72000 ≤ 12`, `2.7^12 ≥ 72000`). -/
theorem haC_72000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 72000 := by
  have hlog : Real.log 72000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 72000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 72000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[71000, 72000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[71000, 72000]` SEGMENT: every zero with `71000 ≤ Im ≤ 72000` is on the line. -/
theorem segment_71000_72000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 72000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (71000:ℝ) ≤ ρ.im → ρ.im ≤ 72000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 71000 72000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_72000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 72000 via the HEIGHT CHAIN**: `[0,71000]` ∘ `[71000,72000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_72000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 72000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 72000 → ρ.re = 1 / 2 := by
  have hγ71000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 71000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 71000 72000
    (AllZeros_h71000.all_nontrivial_zeros_up_to_height_71000_of_bands
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
      hγ71000)
    (segment_71000_72000 hbands hγ)

end AllZeros_h72000
