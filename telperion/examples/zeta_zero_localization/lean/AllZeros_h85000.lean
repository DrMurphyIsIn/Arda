/-  Height-chain step: all nontrivial zeta zeros up to height 85000 on Re = 1/2 --
    `AllZeros_h84000` + a `[84000, 85000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h84000
import RHInBoxT_1d4000000_3999999d4000000_84000_336113d4
import RHInBoxT_1d4000000_3999999d4000000_84028_84056
import RHInBoxT_1d4000000_3999999d4000000_84056_84083
import RHInBoxT_1d4000000_3999999d4000000_84083_84111
import RHInBoxT_1d4000000_3999999d4000000_84111_84139
import RHInBoxT_1d4000000_3999999d4000000_84139_84167
import RHInBoxT_1d4000000_3999999d4000000_84167_336777d4
import RHInBoxT_1d4000000_3999999d4000000_84194_84222
import RHInBoxT_1d4000000_3999999d4000000_336887d4_84250
import RHInBoxT_1d4000000_3999999d4000000_336999d4_84278
import RHInBoxT_1d4000000_3999999d4000000_84278_84306
import RHInBoxT_1d4000000_3999999d4000000_337223d4_84333
import RHInBoxT_1d4000000_3999999d4000000_84333_84361
import RHInBoxT_1d4000000_3999999d4000000_337443d4_84389
import RHInBoxT_1d4000000_3999999d4000000_84389_84417
import RHInBoxT_1d4000000_3999999d4000000_84417_84444
import RHInBoxT_1d4000000_3999999d4000000_84444_84472
import RHInBoxT_1d4000000_3999999d4000000_84472_84500
import RHInBoxT_1d4000000_3999999d4000000_84500_84528
import RHInBoxT_1d4000000_3999999d4000000_84528_84556
import RHInBoxT_1d4000000_3999999d4000000_84556_84583
import RHInBoxT_1d4000000_3999999d4000000_338331d4_338445d4
import RHInBoxT_1d4000000_3999999d4000000_84611_84639
import RHInBoxT_1d4000000_3999999d4000000_84639_84667
import RHInBoxT_1d4000000_3999999d4000000_338667d4_338777d4
import RHInBoxT_1d4000000_3999999d4000000_84694_84722
import RHInBoxT_1d4000000_3999999d4000000_84722_84750
import RHInBoxT_1d4000000_3999999d4000000_338999d4_84778
import RHInBoxT_1d4000000_3999999d4000000_339111d4_84806
import RHInBoxT_1d4000000_3999999d4000000_84806_84833
import RHInBoxT_1d4000000_3999999d4000000_84833_84861
import RHInBoxT_1d4000000_3999999d4000000_339443d4_84889
import RHInBoxT_1d4000000_3999999d4000000_84889_339669d4
import RHInBoxT_1d4000000_3999999d4000000_84917_84944
import RHInBoxT_1d4000000_3999999d4000000_84944_84972
import RHInBoxT_1d4000000_3999999d4000000_84972_85000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h85000

/-- The 36-band NOMINAL partition of `[84000, 85000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 84000
  | 1 => 84028
  | 2 => 84056
  | 3 => 84083
  | 4 => 84111
  | 5 => 84139
  | 6 => 84167
  | 7 => 84194
  | 8 => 84222
  | 9 => 84250
  | 10 => 84278
  | 11 => 84306
  | 12 => 84333
  | 13 => 84361
  | 14 => 84389
  | 15 => 84417
  | 16 => 84444
  | 17 => 84472
  | 18 => 84500
  | 19 => 84528
  | 20 => 84556
  | 21 => 84583
  | 22 => 84611
  | 23 => 84639
  | 24 => 84667
  | 25 => 84694
  | 26 => 84722
  | 27 => 84750
  | 28 => 84778
  | 29 => 84806
  | 30 => 84833
  | 31 => 84861
  | 32 => 84889
  | 33 => 84917
  | 34 => 84944
  | 35 => 84972
  | 36 => 85000
  | _ => 85000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((84000:ℝ)) ≤ (84028); norm_num
  · show ((84028:ℝ)) ≤ (84056); norm_num
  · show ((84056:ℝ)) ≤ (84083); norm_num
  · show ((84083:ℝ)) ≤ (84111); norm_num
  · show ((84111:ℝ)) ≤ (84139); norm_num
  · show ((84139:ℝ)) ≤ (84167); norm_num
  · show ((84167:ℝ)) ≤ (84194); norm_num
  · show ((84194:ℝ)) ≤ (84222); norm_num
  · show ((84222:ℝ)) ≤ (84250); norm_num
  · show ((84250:ℝ)) ≤ (84278); norm_num
  · show ((84278:ℝ)) ≤ (84306); norm_num
  · show ((84306:ℝ)) ≤ (84333); norm_num
  · show ((84333:ℝ)) ≤ (84361); norm_num
  · show ((84361:ℝ)) ≤ (84389); norm_num
  · show ((84389:ℝ)) ≤ (84417); norm_num
  · show ((84417:ℝ)) ≤ (84444); norm_num
  · show ((84444:ℝ)) ≤ (84472); norm_num
  · show ((84472:ℝ)) ≤ (84500); norm_num
  · show ((84500:ℝ)) ≤ (84528); norm_num
  · show ((84528:ℝ)) ≤ (84556); norm_num
  · show ((84556:ℝ)) ≤ (84583); norm_num
  · show ((84583:ℝ)) ≤ (84611); norm_num
  · show ((84611:ℝ)) ≤ (84639); norm_num
  · show ((84639:ℝ)) ≤ (84667); norm_num
  · show ((84667:ℝ)) ≤ (84694); norm_num
  · show ((84694:ℝ)) ≤ (84722); norm_num
  · show ((84722:ℝ)) ≤ (84750); norm_num
  · show ((84750:ℝ)) ≤ (84778); norm_num
  · show ((84778:ℝ)) ≤ (84806); norm_num
  · show ((84806:ℝ)) ≤ (84833); norm_num
  · show ((84833:ℝ)) ≤ (84861); norm_num
  · show ((84861:ℝ)) ≤ (84889); norm_num
  · show ((84889:ℝ)) ≤ (84917); norm_num
  · show ((84917:ℝ)) ≤ (84944); norm_num
  · show ((84944:ℝ)) ≤ (84972); norm_num
  · show ((84972:ℝ)) ≤ (85000); norm_num
  · show ((85000:ℝ)) ≤ (85000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 84000
  | 1 => 84028
  | 2 => 84056
  | 3 => 84083
  | 4 => 84111
  | 5 => 84139
  | 6 => 84167
  | 7 => 84194
  | 8 => 336887 / 4
  | 9 => 336999 / 4
  | 10 => 84278
  | 11 => 337223 / 4
  | 12 => 84333
  | 13 => 337443 / 4
  | 14 => 84389
  | 15 => 84417
  | 16 => 84444
  | 17 => 84472
  | 18 => 84500
  | 19 => 84528
  | 20 => 84556
  | 21 => 338331 / 4
  | 22 => 84611
  | 23 => 84639
  | 24 => 338667 / 4
  | 25 => 84694
  | 26 => 84722
  | 27 => 338999 / 4
  | 28 => 339111 / 4
  | 29 => 84806
  | 30 => 84833
  | 31 => 339443 / 4
  | 32 => 84889
  | 33 => 84917
  | 34 => 84944
  | 35 => 84972
  | _ => 84972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 336113 / 4
  | 1 => 84056
  | 2 => 84083
  | 3 => 84111
  | 4 => 84139
  | 5 => 84167
  | 6 => 336777 / 4
  | 7 => 84222
  | 8 => 84250
  | 9 => 84278
  | 10 => 84306
  | 11 => 84333
  | 12 => 84361
  | 13 => 84389
  | 14 => 84417
  | 15 => 84444
  | 16 => 84472
  | 17 => 84500
  | 18 => 84528
  | 19 => 84556
  | 20 => 84583
  | 21 => 338445 / 4
  | 22 => 84639
  | 23 => 84667
  | 24 => 338777 / 4
  | 25 => 84722
  | 26 => 84750
  | 27 => 84778
  | 28 => 84806
  | 29 => 84833
  | 30 => 84861
  | 31 => 84889
  | 32 => 339669 / 4
  | 33 => 84944
  | 34 => 84972
  | 35 => 85000
  | _ => 85000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 85000` (`log 85000 ≤ 12`, `2.7^12 ≥ 85000`). -/
theorem haC_85000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 85000 := by
  have hlog : Real.log 85000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 85000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 85000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[84000, 85000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[84000, 85000]` SEGMENT: every zero with `84000 ≤ Im ≤ 85000` is on the line. -/
theorem segment_84000_85000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 85000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (84000:ℝ) ≤ ρ.im → ρ.im ≤ 85000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 84000 85000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_85000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 85000 via the HEIGHT CHAIN**: `[0,84000]` ∘ `[84000,85000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_85000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 85000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 85000 → ρ.re = 1 / 2 := by
  have hγ84000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 84000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 84000 85000
    (AllZeros_h84000.all_nontrivial_zeros_up_to_height_84000_of_bands
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
      hγ84000)
    (segment_84000_85000 hbands hγ)

end AllZeros_h85000
