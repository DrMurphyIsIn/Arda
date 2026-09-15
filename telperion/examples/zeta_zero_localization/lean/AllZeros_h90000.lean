/-  Height-chain step: all nontrivial zeta zeros up to height 90000 on Re = 1/2 --
    `AllZeros_h89000` + a `[89000, 90000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h89000
import RHInBoxT_1d4000000_3999999d4000000_89000_89028
import RHInBoxT_1d4000000_3999999d4000000_356111d4_89056
import RHInBoxT_1d4000000_3999999d4000000_89056_89083
import RHInBoxT_1d4000000_3999999d4000000_89083_356445d4
import RHInBoxT_1d4000000_3999999d4000000_89111_356557d4
import RHInBoxT_1d4000000_3999999d4000000_89139_89167
import RHInBoxT_1d4000000_3999999d4000000_89167_89194
import RHInBoxT_1d4000000_3999999d4000000_89194_89222
import RHInBoxT_1d4000000_3999999d4000000_89222_89250
import RHInBoxT_1d4000000_3999999d4000000_89250_89278
import RHInBoxT_1d4000000_3999999d4000000_357111d4_89306
import RHInBoxT_1d4000000_3999999d4000000_89306_89333
import RHInBoxT_1d4000000_3999999d4000000_89333_178723d2
import RHInBoxT_1d4000000_3999999d4000000_89361_89389
import RHInBoxT_1d4000000_3999999d4000000_89389_89417
import RHInBoxT_1d4000000_3999999d4000000_89417_357777d4
import RHInBoxT_1d4000000_3999999d4000000_89444_89472
import RHInBoxT_1d4000000_3999999d4000000_89472_89500
import RHInBoxT_1d4000000_3999999d4000000_89500_89528
import RHInBoxT_1d4000000_3999999d4000000_89528_89556
import RHInBoxT_1d4000000_3999999d4000000_89556_89583
import RHInBoxT_1d4000000_3999999d4000000_89583_89611
import RHInBoxT_1d4000000_3999999d4000000_358443d4_89639
import RHInBoxT_1d4000000_3999999d4000000_89639_89667
import RHInBoxT_1d4000000_3999999d4000000_89667_89694
import RHInBoxT_1d4000000_3999999d4000000_89694_89722
import RHInBoxT_1d4000000_3999999d4000000_89722_89750
import RHInBoxT_1d4000000_3999999d4000000_89750_89778
import RHInBoxT_1d4000000_3999999d4000000_89778_89806
import RHInBoxT_1d4000000_3999999d4000000_89806_89833
import RHInBoxT_1d4000000_3999999d4000000_89833_359445d4
import RHInBoxT_1d4000000_3999999d4000000_89861_359557d4
import RHInBoxT_1d4000000_3999999d4000000_89889_89917
import RHInBoxT_1d4000000_3999999d4000000_89917_89944
import RHInBoxT_1d4000000_3999999d4000000_359775d4_89972
import RHInBoxT_1d4000000_3999999d4000000_89972_360001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h90000

/-- The 36-band NOMINAL partition of `[89000, 90000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 89000
  | 1 => 89028
  | 2 => 89056
  | 3 => 89083
  | 4 => 89111
  | 5 => 89139
  | 6 => 89167
  | 7 => 89194
  | 8 => 89222
  | 9 => 89250
  | 10 => 89278
  | 11 => 89306
  | 12 => 89333
  | 13 => 89361
  | 14 => 89389
  | 15 => 89417
  | 16 => 89444
  | 17 => 89472
  | 18 => 89500
  | 19 => 89528
  | 20 => 89556
  | 21 => 89583
  | 22 => 89611
  | 23 => 89639
  | 24 => 89667
  | 25 => 89694
  | 26 => 89722
  | 27 => 89750
  | 28 => 89778
  | 29 => 89806
  | 30 => 89833
  | 31 => 89861
  | 32 => 89889
  | 33 => 89917
  | 34 => 89944
  | 35 => 89972
  | 36 => 90000
  | _ => 90000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((89000:ℝ)) ≤ (89028); norm_num
  · show ((89028:ℝ)) ≤ (89056); norm_num
  · show ((89056:ℝ)) ≤ (89083); norm_num
  · show ((89083:ℝ)) ≤ (89111); norm_num
  · show ((89111:ℝ)) ≤ (89139); norm_num
  · show ((89139:ℝ)) ≤ (89167); norm_num
  · show ((89167:ℝ)) ≤ (89194); norm_num
  · show ((89194:ℝ)) ≤ (89222); norm_num
  · show ((89222:ℝ)) ≤ (89250); norm_num
  · show ((89250:ℝ)) ≤ (89278); norm_num
  · show ((89278:ℝ)) ≤ (89306); norm_num
  · show ((89306:ℝ)) ≤ (89333); norm_num
  · show ((89333:ℝ)) ≤ (89361); norm_num
  · show ((89361:ℝ)) ≤ (89389); norm_num
  · show ((89389:ℝ)) ≤ (89417); norm_num
  · show ((89417:ℝ)) ≤ (89444); norm_num
  · show ((89444:ℝ)) ≤ (89472); norm_num
  · show ((89472:ℝ)) ≤ (89500); norm_num
  · show ((89500:ℝ)) ≤ (89528); norm_num
  · show ((89528:ℝ)) ≤ (89556); norm_num
  · show ((89556:ℝ)) ≤ (89583); norm_num
  · show ((89583:ℝ)) ≤ (89611); norm_num
  · show ((89611:ℝ)) ≤ (89639); norm_num
  · show ((89639:ℝ)) ≤ (89667); norm_num
  · show ((89667:ℝ)) ≤ (89694); norm_num
  · show ((89694:ℝ)) ≤ (89722); norm_num
  · show ((89722:ℝ)) ≤ (89750); norm_num
  · show ((89750:ℝ)) ≤ (89778); norm_num
  · show ((89778:ℝ)) ≤ (89806); norm_num
  · show ((89806:ℝ)) ≤ (89833); norm_num
  · show ((89833:ℝ)) ≤ (89861); norm_num
  · show ((89861:ℝ)) ≤ (89889); norm_num
  · show ((89889:ℝ)) ≤ (89917); norm_num
  · show ((89917:ℝ)) ≤ (89944); norm_num
  · show ((89944:ℝ)) ≤ (89972); norm_num
  · show ((89972:ℝ)) ≤ (90000); norm_num
  · show ((90000:ℝ)) ≤ (90000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 89000
  | 1 => 356111 / 4
  | 2 => 89056
  | 3 => 89083
  | 4 => 89111
  | 5 => 89139
  | 6 => 89167
  | 7 => 89194
  | 8 => 89222
  | 9 => 89250
  | 10 => 357111 / 4
  | 11 => 89306
  | 12 => 89333
  | 13 => 89361
  | 14 => 89389
  | 15 => 89417
  | 16 => 89444
  | 17 => 89472
  | 18 => 89500
  | 19 => 89528
  | 20 => 89556
  | 21 => 89583
  | 22 => 358443 / 4
  | 23 => 89639
  | 24 => 89667
  | 25 => 89694
  | 26 => 89722
  | 27 => 89750
  | 28 => 89778
  | 29 => 89806
  | 30 => 89833
  | 31 => 89861
  | 32 => 89889
  | 33 => 89917
  | 34 => 359775 / 4
  | 35 => 89972
  | _ => 89972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 89028
  | 1 => 89056
  | 2 => 89083
  | 3 => 356445 / 4
  | 4 => 356557 / 4
  | 5 => 89167
  | 6 => 89194
  | 7 => 89222
  | 8 => 89250
  | 9 => 89278
  | 10 => 89306
  | 11 => 89333
  | 12 => 178723 / 2
  | 13 => 89389
  | 14 => 89417
  | 15 => 357777 / 4
  | 16 => 89472
  | 17 => 89500
  | 18 => 89528
  | 19 => 89556
  | 20 => 89583
  | 21 => 89611
  | 22 => 89639
  | 23 => 89667
  | 24 => 89694
  | 25 => 89722
  | 26 => 89750
  | 27 => 89778
  | 28 => 89806
  | 29 => 89833
  | 30 => 359445 / 4
  | 31 => 359557 / 4
  | 32 => 89917
  | 33 => 89944
  | 34 => 89972
  | 35 => 360001 / 4
  | _ => 360001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 90000` (`log 90000 ≤ 12`, `2.7^12 ≥ 90000`). -/
theorem haC_90000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 90000 := by
  have hlog : Real.log 90000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 90000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 90000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[89000, 90000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[89000, 90000]` SEGMENT: every zero with `89000 ≤ Im ≤ 90000` is on the line. -/
theorem segment_89000_90000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 90000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (89000:ℝ) ≤ ρ.im → ρ.im ≤ 90000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 89000 90000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_90000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 90000 via the HEIGHT CHAIN**: `[0,89000]` ∘ `[89000,90000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_90000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 90000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 90000 → ρ.re = 1 / 2 := by
  have hγ89000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 89000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 89000 90000
    (AllZeros_h89000.all_nontrivial_zeros_up_to_height_89000_of_bands
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
      hγ89000)
    (segment_89000_90000 hbands hγ)

end AllZeros_h90000
