/-  Height-chain step: all nontrivial zeta zeros up to height 83000 on Re = 1/2 --
    `AllZeros_h82000` + a `[82000, 83000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h82000
import RHInBoxT_1d4000000_3999999d4000000_82000_82028
import RHInBoxT_1d4000000_3999999d4000000_82028_82056
import RHInBoxT_1d4000000_3999999d4000000_328223d4_82083
import RHInBoxT_1d4000000_3999999d4000000_82083_82111
import RHInBoxT_1d4000000_3999999d4000000_82111_82139
import RHInBoxT_1d4000000_3999999d4000000_82139_82167
import RHInBoxT_1d4000000_3999999d4000000_82167_82194
import RHInBoxT_1d4000000_3999999d4000000_82194_82222
import RHInBoxT_1d4000000_3999999d4000000_82222_82250
import RHInBoxT_1d4000000_3999999d4000000_328999d4_82278
import RHInBoxT_1d4000000_3999999d4000000_82278_82306
import RHInBoxT_1d4000000_3999999d4000000_82306_82333
import RHInBoxT_1d4000000_3999999d4000000_82333_329445d4
import RHInBoxT_1d4000000_3999999d4000000_82361_82389
import RHInBoxT_1d4000000_3999999d4000000_82389_82417
import RHInBoxT_1d4000000_3999999d4000000_82417_82444
import RHInBoxT_1d4000000_3999999d4000000_82444_82472
import RHInBoxT_1d4000000_3999999d4000000_82472_82500
import RHInBoxT_1d4000000_3999999d4000000_82500_82528
import RHInBoxT_1d4000000_3999999d4000000_82528_82556
import RHInBoxT_1d4000000_3999999d4000000_330223d4_82583
import RHInBoxT_1d4000000_3999999d4000000_82583_330445d4
import RHInBoxT_1d4000000_3999999d4000000_82611_330557d4
import RHInBoxT_1d4000000_3999999d4000000_82639_82667
import RHInBoxT_1d4000000_3999999d4000000_330667d4_82694
import RHInBoxT_1d4000000_3999999d4000000_82694_82722
import RHInBoxT_1d4000000_3999999d4000000_82722_82750
import RHInBoxT_1d4000000_3999999d4000000_82750_82778
import RHInBoxT_1d4000000_3999999d4000000_82778_82806
import RHInBoxT_1d4000000_3999999d4000000_82806_331333d4
import RHInBoxT_1d4000000_3999999d4000000_82833_82861
import RHInBoxT_1d4000000_3999999d4000000_82861_82889
import RHInBoxT_1d4000000_3999999d4000000_82889_82917
import RHInBoxT_1d4000000_3999999d4000000_82917_82944
import RHInBoxT_1d4000000_3999999d4000000_82944_82972
import RHInBoxT_1d4000000_3999999d4000000_82972_166001d2

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h83000

/-- The 36-band NOMINAL partition of `[82000, 83000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 82000
  | 1 => 82028
  | 2 => 82056
  | 3 => 82083
  | 4 => 82111
  | 5 => 82139
  | 6 => 82167
  | 7 => 82194
  | 8 => 82222
  | 9 => 82250
  | 10 => 82278
  | 11 => 82306
  | 12 => 82333
  | 13 => 82361
  | 14 => 82389
  | 15 => 82417
  | 16 => 82444
  | 17 => 82472
  | 18 => 82500
  | 19 => 82528
  | 20 => 82556
  | 21 => 82583
  | 22 => 82611
  | 23 => 82639
  | 24 => 82667
  | 25 => 82694
  | 26 => 82722
  | 27 => 82750
  | 28 => 82778
  | 29 => 82806
  | 30 => 82833
  | 31 => 82861
  | 32 => 82889
  | 33 => 82917
  | 34 => 82944
  | 35 => 82972
  | 36 => 83000
  | _ => 83000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((82000:ℝ)) ≤ (82028); norm_num
  · show ((82028:ℝ)) ≤ (82056); norm_num
  · show ((82056:ℝ)) ≤ (82083); norm_num
  · show ((82083:ℝ)) ≤ (82111); norm_num
  · show ((82111:ℝ)) ≤ (82139); norm_num
  · show ((82139:ℝ)) ≤ (82167); norm_num
  · show ((82167:ℝ)) ≤ (82194); norm_num
  · show ((82194:ℝ)) ≤ (82222); norm_num
  · show ((82222:ℝ)) ≤ (82250); norm_num
  · show ((82250:ℝ)) ≤ (82278); norm_num
  · show ((82278:ℝ)) ≤ (82306); norm_num
  · show ((82306:ℝ)) ≤ (82333); norm_num
  · show ((82333:ℝ)) ≤ (82361); norm_num
  · show ((82361:ℝ)) ≤ (82389); norm_num
  · show ((82389:ℝ)) ≤ (82417); norm_num
  · show ((82417:ℝ)) ≤ (82444); norm_num
  · show ((82444:ℝ)) ≤ (82472); norm_num
  · show ((82472:ℝ)) ≤ (82500); norm_num
  · show ((82500:ℝ)) ≤ (82528); norm_num
  · show ((82528:ℝ)) ≤ (82556); norm_num
  · show ((82556:ℝ)) ≤ (82583); norm_num
  · show ((82583:ℝ)) ≤ (82611); norm_num
  · show ((82611:ℝ)) ≤ (82639); norm_num
  · show ((82639:ℝ)) ≤ (82667); norm_num
  · show ((82667:ℝ)) ≤ (82694); norm_num
  · show ((82694:ℝ)) ≤ (82722); norm_num
  · show ((82722:ℝ)) ≤ (82750); norm_num
  · show ((82750:ℝ)) ≤ (82778); norm_num
  · show ((82778:ℝ)) ≤ (82806); norm_num
  · show ((82806:ℝ)) ≤ (82833); norm_num
  · show ((82833:ℝ)) ≤ (82861); norm_num
  · show ((82861:ℝ)) ≤ (82889); norm_num
  · show ((82889:ℝ)) ≤ (82917); norm_num
  · show ((82917:ℝ)) ≤ (82944); norm_num
  · show ((82944:ℝ)) ≤ (82972); norm_num
  · show ((82972:ℝ)) ≤ (83000); norm_num
  · show ((83000:ℝ)) ≤ (83000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 82000
  | 1 => 82028
  | 2 => 328223 / 4
  | 3 => 82083
  | 4 => 82111
  | 5 => 82139
  | 6 => 82167
  | 7 => 82194
  | 8 => 82222
  | 9 => 328999 / 4
  | 10 => 82278
  | 11 => 82306
  | 12 => 82333
  | 13 => 82361
  | 14 => 82389
  | 15 => 82417
  | 16 => 82444
  | 17 => 82472
  | 18 => 82500
  | 19 => 82528
  | 20 => 330223 / 4
  | 21 => 82583
  | 22 => 82611
  | 23 => 82639
  | 24 => 330667 / 4
  | 25 => 82694
  | 26 => 82722
  | 27 => 82750
  | 28 => 82778
  | 29 => 82806
  | 30 => 82833
  | 31 => 82861
  | 32 => 82889
  | 33 => 82917
  | 34 => 82944
  | 35 => 82972
  | _ => 82972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 82028
  | 1 => 82056
  | 2 => 82083
  | 3 => 82111
  | 4 => 82139
  | 5 => 82167
  | 6 => 82194
  | 7 => 82222
  | 8 => 82250
  | 9 => 82278
  | 10 => 82306
  | 11 => 82333
  | 12 => 329445 / 4
  | 13 => 82389
  | 14 => 82417
  | 15 => 82444
  | 16 => 82472
  | 17 => 82500
  | 18 => 82528
  | 19 => 82556
  | 20 => 82583
  | 21 => 330445 / 4
  | 22 => 330557 / 4
  | 23 => 82667
  | 24 => 82694
  | 25 => 82722
  | 26 => 82750
  | 27 => 82778
  | 28 => 82806
  | 29 => 331333 / 4
  | 30 => 82861
  | 31 => 82889
  | 32 => 82917
  | 33 => 82944
  | 34 => 82972
  | 35 => 166001 / 2
  | _ => 166001 / 2

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 83000` (`log 83000 ≤ 12`, `2.7^12 ≥ 83000`). -/
theorem haC_83000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 83000 := by
  have hlog : Real.log 83000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 83000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 83000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[82000, 83000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[82000, 83000]` SEGMENT: every zero with `82000 ≤ Im ≤ 83000` is on the line. -/
theorem segment_82000_83000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 83000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (82000:ℝ) ≤ ρ.im → ρ.im ≤ 83000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 82000 83000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_83000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 83000 via the HEIGHT CHAIN**: `[0,82000]` ∘ `[82000,83000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_83000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 83000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 83000 → ρ.re = 1 / 2 := by
  have hγ82000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 82000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 82000 83000
    (AllZeros_h82000.all_nontrivial_zeros_up_to_height_82000_of_bands
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
      hγ82000)
    (segment_82000_83000 hbands hγ)

end AllZeros_h83000
