/-  Height-chain step: all nontrivial zeta zeros up to height 78000 on Re = 1/2 --
    `AllZeros_h77000` + a `[77000, 78000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h77000
import RHInBoxT_1d4000000_3999999d4000000_77000_77028
import RHInBoxT_1d4000000_3999999d4000000_77028_77056
import RHInBoxT_1d4000000_3999999d4000000_77056_77083
import RHInBoxT_1d4000000_3999999d4000000_77083_77111
import RHInBoxT_1d4000000_3999999d4000000_77111_77139
import RHInBoxT_1d4000000_3999999d4000000_77139_308669d4
import RHInBoxT_1d4000000_3999999d4000000_77167_308777d4
import RHInBoxT_1d4000000_3999999d4000000_77194_77222
import RHInBoxT_1d4000000_3999999d4000000_77222_77250
import RHInBoxT_1d4000000_3999999d4000000_77250_77278
import RHInBoxT_1d4000000_3999999d4000000_77278_77306
import RHInBoxT_1d4000000_3999999d4000000_77306_77333
import RHInBoxT_1d4000000_3999999d4000000_77333_77361
import RHInBoxT_1d4000000_3999999d4000000_77361_309557d4
import RHInBoxT_1d4000000_3999999d4000000_77389_77417
import RHInBoxT_1d4000000_3999999d4000000_77417_77444
import RHInBoxT_1d4000000_3999999d4000000_77444_77472
import RHInBoxT_1d4000000_3999999d4000000_77472_77500
import RHInBoxT_1d4000000_3999999d4000000_77500_77528
import RHInBoxT_1d4000000_3999999d4000000_77528_77556
import RHInBoxT_1d4000000_3999999d4000000_77556_310333d4
import RHInBoxT_1d4000000_3999999d4000000_77583_310445d4
import RHInBoxT_1d4000000_3999999d4000000_77611_77639
import RHInBoxT_1d4000000_3999999d4000000_77639_77667
import RHInBoxT_1d4000000_3999999d4000000_310667d4_310777d4
import RHInBoxT_1d4000000_3999999d4000000_77694_77722
import RHInBoxT_1d4000000_3999999d4000000_77722_77750
import RHInBoxT_1d4000000_3999999d4000000_77750_77778
import RHInBoxT_1d4000000_3999999d4000000_77778_77806
import RHInBoxT_1d4000000_3999999d4000000_77806_77833
import RHInBoxT_1d4000000_3999999d4000000_311331d4_77861
import RHInBoxT_1d4000000_3999999d4000000_77861_77889
import RHInBoxT_1d4000000_3999999d4000000_311555d4_77917
import RHInBoxT_1d4000000_3999999d4000000_77917_77944
import RHInBoxT_1d4000000_3999999d4000000_77944_77972
import RHInBoxT_1d4000000_3999999d4000000_77972_78000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h78000

/-- The 36-band NOMINAL partition of `[77000, 78000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 77000
  | 1 => 77028
  | 2 => 77056
  | 3 => 77083
  | 4 => 77111
  | 5 => 77139
  | 6 => 77167
  | 7 => 77194
  | 8 => 77222
  | 9 => 77250
  | 10 => 77278
  | 11 => 77306
  | 12 => 77333
  | 13 => 77361
  | 14 => 77389
  | 15 => 77417
  | 16 => 77444
  | 17 => 77472
  | 18 => 77500
  | 19 => 77528
  | 20 => 77556
  | 21 => 77583
  | 22 => 77611
  | 23 => 77639
  | 24 => 77667
  | 25 => 77694
  | 26 => 77722
  | 27 => 77750
  | 28 => 77778
  | 29 => 77806
  | 30 => 77833
  | 31 => 77861
  | 32 => 77889
  | 33 => 77917
  | 34 => 77944
  | 35 => 77972
  | 36 => 78000
  | _ => 78000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((77000:ℝ)) ≤ (77028); norm_num
  · show ((77028:ℝ)) ≤ (77056); norm_num
  · show ((77056:ℝ)) ≤ (77083); norm_num
  · show ((77083:ℝ)) ≤ (77111); norm_num
  · show ((77111:ℝ)) ≤ (77139); norm_num
  · show ((77139:ℝ)) ≤ (77167); norm_num
  · show ((77167:ℝ)) ≤ (77194); norm_num
  · show ((77194:ℝ)) ≤ (77222); norm_num
  · show ((77222:ℝ)) ≤ (77250); norm_num
  · show ((77250:ℝ)) ≤ (77278); norm_num
  · show ((77278:ℝ)) ≤ (77306); norm_num
  · show ((77306:ℝ)) ≤ (77333); norm_num
  · show ((77333:ℝ)) ≤ (77361); norm_num
  · show ((77361:ℝ)) ≤ (77389); norm_num
  · show ((77389:ℝ)) ≤ (77417); norm_num
  · show ((77417:ℝ)) ≤ (77444); norm_num
  · show ((77444:ℝ)) ≤ (77472); norm_num
  · show ((77472:ℝ)) ≤ (77500); norm_num
  · show ((77500:ℝ)) ≤ (77528); norm_num
  · show ((77528:ℝ)) ≤ (77556); norm_num
  · show ((77556:ℝ)) ≤ (77583); norm_num
  · show ((77583:ℝ)) ≤ (77611); norm_num
  · show ((77611:ℝ)) ≤ (77639); norm_num
  · show ((77639:ℝ)) ≤ (77667); norm_num
  · show ((77667:ℝ)) ≤ (77694); norm_num
  · show ((77694:ℝ)) ≤ (77722); norm_num
  · show ((77722:ℝ)) ≤ (77750); norm_num
  · show ((77750:ℝ)) ≤ (77778); norm_num
  · show ((77778:ℝ)) ≤ (77806); norm_num
  · show ((77806:ℝ)) ≤ (77833); norm_num
  · show ((77833:ℝ)) ≤ (77861); norm_num
  · show ((77861:ℝ)) ≤ (77889); norm_num
  · show ((77889:ℝ)) ≤ (77917); norm_num
  · show ((77917:ℝ)) ≤ (77944); norm_num
  · show ((77944:ℝ)) ≤ (77972); norm_num
  · show ((77972:ℝ)) ≤ (78000); norm_num
  · show ((78000:ℝ)) ≤ (78000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 77000
  | 1 => 77028
  | 2 => 77056
  | 3 => 77083
  | 4 => 77111
  | 5 => 77139
  | 6 => 77167
  | 7 => 77194
  | 8 => 77222
  | 9 => 77250
  | 10 => 77278
  | 11 => 77306
  | 12 => 77333
  | 13 => 77361
  | 14 => 77389
  | 15 => 77417
  | 16 => 77444
  | 17 => 77472
  | 18 => 77500
  | 19 => 77528
  | 20 => 77556
  | 21 => 77583
  | 22 => 77611
  | 23 => 77639
  | 24 => 310667 / 4
  | 25 => 77694
  | 26 => 77722
  | 27 => 77750
  | 28 => 77778
  | 29 => 77806
  | 30 => 311331 / 4
  | 31 => 77861
  | 32 => 311555 / 4
  | 33 => 77917
  | 34 => 77944
  | 35 => 77972
  | _ => 77972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 77028
  | 1 => 77056
  | 2 => 77083
  | 3 => 77111
  | 4 => 77139
  | 5 => 308669 / 4
  | 6 => 308777 / 4
  | 7 => 77222
  | 8 => 77250
  | 9 => 77278
  | 10 => 77306
  | 11 => 77333
  | 12 => 77361
  | 13 => 309557 / 4
  | 14 => 77417
  | 15 => 77444
  | 16 => 77472
  | 17 => 77500
  | 18 => 77528
  | 19 => 77556
  | 20 => 310333 / 4
  | 21 => 310445 / 4
  | 22 => 77639
  | 23 => 77667
  | 24 => 310777 / 4
  | 25 => 77722
  | 26 => 77750
  | 27 => 77778
  | 28 => 77806
  | 29 => 77833
  | 30 => 77861
  | 31 => 77889
  | 32 => 77917
  | 33 => 77944
  | 34 => 77972
  | 35 => 78000
  | _ => 78000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 78000` (`log 78000 ≤ 12`, `2.7^12 ≥ 78000`). -/
theorem haC_78000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 78000 := by
  have hlog : Real.log 78000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 78000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 78000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[77000, 78000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[77000, 78000]` SEGMENT: every zero with `77000 ≤ Im ≤ 78000` is on the line. -/
theorem segment_77000_78000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 78000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (77000:ℝ) ≤ ρ.im → ρ.im ≤ 78000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 77000 78000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_78000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 78000 via the HEIGHT CHAIN**: `[0,77000]` ∘ `[77000,78000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_78000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 78000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 78000 → ρ.re = 1 / 2 := by
  have hγ77000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 77000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 77000 78000
    (AllZeros_h77000.all_nontrivial_zeros_up_to_height_77000_of_bands
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
      hγ77000)
    (segment_77000_78000 hbands hγ)

end AllZeros_h78000
