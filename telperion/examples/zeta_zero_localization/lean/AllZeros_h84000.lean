/-  Height-chain step: all nontrivial zeta zeros up to height 84000 on Re = 1/2 --
    `AllZeros_h83000` + a `[83000, 84000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h83000
import RHInBoxT_1d4000000_3999999d4000000_83000_83028
import RHInBoxT_1d4000000_3999999d4000000_83028_83056
import RHInBoxT_1d4000000_3999999d4000000_83056_83083
import RHInBoxT_1d4000000_3999999d4000000_83083_83111
import RHInBoxT_1d4000000_3999999d4000000_83111_83139
import RHInBoxT_1d4000000_3999999d4000000_83139_332669d4
import RHInBoxT_1d4000000_3999999d4000000_83167_83194
import RHInBoxT_1d4000000_3999999d4000000_83194_83222
import RHInBoxT_1d4000000_3999999d4000000_83222_83250
import RHInBoxT_1d4000000_3999999d4000000_83250_83278
import RHInBoxT_1d4000000_3999999d4000000_83278_83306
import RHInBoxT_1d4000000_3999999d4000000_83306_83333
import RHInBoxT_1d4000000_3999999d4000000_83333_83361
import RHInBoxT_1d4000000_3999999d4000000_83361_83389
import RHInBoxT_1d4000000_3999999d4000000_83389_83417
import RHInBoxT_1d4000000_3999999d4000000_83417_83444
import RHInBoxT_1d4000000_3999999d4000000_83444_83472
import RHInBoxT_1d4000000_3999999d4000000_83472_83500
import RHInBoxT_1d4000000_3999999d4000000_83500_83528
import RHInBoxT_1d4000000_3999999d4000000_334111d4_83556
import RHInBoxT_1d4000000_3999999d4000000_83556_83583
import RHInBoxT_1d4000000_3999999d4000000_334331d4_83611
import RHInBoxT_1d4000000_3999999d4000000_83611_83639
import RHInBoxT_1d4000000_3999999d4000000_83639_83667
import RHInBoxT_1d4000000_3999999d4000000_83667_334777d4
import RHInBoxT_1d4000000_3999999d4000000_83694_334889d4
import RHInBoxT_1d4000000_3999999d4000000_83722_83750
import RHInBoxT_1d4000000_3999999d4000000_83750_83778
import RHInBoxT_1d4000000_3999999d4000000_83778_83806
import RHInBoxT_1d4000000_3999999d4000000_335223d4_83833
import RHInBoxT_1d4000000_3999999d4000000_83833_335445d4
import RHInBoxT_1d4000000_3999999d4000000_83861_83889
import RHInBoxT_1d4000000_3999999d4000000_83889_83917
import RHInBoxT_1d4000000_3999999d4000000_335667d4_83944
import RHInBoxT_1d4000000_3999999d4000000_83944_83972
import RHInBoxT_1d4000000_3999999d4000000_83972_84000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h84000

/-- The 36-band NOMINAL partition of `[83000, 84000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 83000
  | 1 => 83028
  | 2 => 83056
  | 3 => 83083
  | 4 => 83111
  | 5 => 83139
  | 6 => 83167
  | 7 => 83194
  | 8 => 83222
  | 9 => 83250
  | 10 => 83278
  | 11 => 83306
  | 12 => 83333
  | 13 => 83361
  | 14 => 83389
  | 15 => 83417
  | 16 => 83444
  | 17 => 83472
  | 18 => 83500
  | 19 => 83528
  | 20 => 83556
  | 21 => 83583
  | 22 => 83611
  | 23 => 83639
  | 24 => 83667
  | 25 => 83694
  | 26 => 83722
  | 27 => 83750
  | 28 => 83778
  | 29 => 83806
  | 30 => 83833
  | 31 => 83861
  | 32 => 83889
  | 33 => 83917
  | 34 => 83944
  | 35 => 83972
  | 36 => 84000
  | _ => 84000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((83000:ℝ)) ≤ (83028); norm_num
  · show ((83028:ℝ)) ≤ (83056); norm_num
  · show ((83056:ℝ)) ≤ (83083); norm_num
  · show ((83083:ℝ)) ≤ (83111); norm_num
  · show ((83111:ℝ)) ≤ (83139); norm_num
  · show ((83139:ℝ)) ≤ (83167); norm_num
  · show ((83167:ℝ)) ≤ (83194); norm_num
  · show ((83194:ℝ)) ≤ (83222); norm_num
  · show ((83222:ℝ)) ≤ (83250); norm_num
  · show ((83250:ℝ)) ≤ (83278); norm_num
  · show ((83278:ℝ)) ≤ (83306); norm_num
  · show ((83306:ℝ)) ≤ (83333); norm_num
  · show ((83333:ℝ)) ≤ (83361); norm_num
  · show ((83361:ℝ)) ≤ (83389); norm_num
  · show ((83389:ℝ)) ≤ (83417); norm_num
  · show ((83417:ℝ)) ≤ (83444); norm_num
  · show ((83444:ℝ)) ≤ (83472); norm_num
  · show ((83472:ℝ)) ≤ (83500); norm_num
  · show ((83500:ℝ)) ≤ (83528); norm_num
  · show ((83528:ℝ)) ≤ (83556); norm_num
  · show ((83556:ℝ)) ≤ (83583); norm_num
  · show ((83583:ℝ)) ≤ (83611); norm_num
  · show ((83611:ℝ)) ≤ (83639); norm_num
  · show ((83639:ℝ)) ≤ (83667); norm_num
  · show ((83667:ℝ)) ≤ (83694); norm_num
  · show ((83694:ℝ)) ≤ (83722); norm_num
  · show ((83722:ℝ)) ≤ (83750); norm_num
  · show ((83750:ℝ)) ≤ (83778); norm_num
  · show ((83778:ℝ)) ≤ (83806); norm_num
  · show ((83806:ℝ)) ≤ (83833); norm_num
  · show ((83833:ℝ)) ≤ (83861); norm_num
  · show ((83861:ℝ)) ≤ (83889); norm_num
  · show ((83889:ℝ)) ≤ (83917); norm_num
  · show ((83917:ℝ)) ≤ (83944); norm_num
  · show ((83944:ℝ)) ≤ (83972); norm_num
  · show ((83972:ℝ)) ≤ (84000); norm_num
  · show ((84000:ℝ)) ≤ (84000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 83000
  | 1 => 83028
  | 2 => 83056
  | 3 => 83083
  | 4 => 83111
  | 5 => 83139
  | 6 => 83167
  | 7 => 83194
  | 8 => 83222
  | 9 => 83250
  | 10 => 83278
  | 11 => 83306
  | 12 => 83333
  | 13 => 83361
  | 14 => 83389
  | 15 => 83417
  | 16 => 83444
  | 17 => 83472
  | 18 => 83500
  | 19 => 334111 / 4
  | 20 => 83556
  | 21 => 334331 / 4
  | 22 => 83611
  | 23 => 83639
  | 24 => 83667
  | 25 => 83694
  | 26 => 83722
  | 27 => 83750
  | 28 => 83778
  | 29 => 335223 / 4
  | 30 => 83833
  | 31 => 83861
  | 32 => 83889
  | 33 => 335667 / 4
  | 34 => 83944
  | 35 => 83972
  | _ => 83972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 83028
  | 1 => 83056
  | 2 => 83083
  | 3 => 83111
  | 4 => 83139
  | 5 => 332669 / 4
  | 6 => 83194
  | 7 => 83222
  | 8 => 83250
  | 9 => 83278
  | 10 => 83306
  | 11 => 83333
  | 12 => 83361
  | 13 => 83389
  | 14 => 83417
  | 15 => 83444
  | 16 => 83472
  | 17 => 83500
  | 18 => 83528
  | 19 => 83556
  | 20 => 83583
  | 21 => 83611
  | 22 => 83639
  | 23 => 83667
  | 24 => 334777 / 4
  | 25 => 334889 / 4
  | 26 => 83750
  | 27 => 83778
  | 28 => 83806
  | 29 => 83833
  | 30 => 335445 / 4
  | 31 => 83889
  | 32 => 83917
  | 33 => 83944
  | 34 => 83972
  | 35 => 84000
  | _ => 84000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 84000` (`log 84000 ≤ 12`, `2.7^12 ≥ 84000`). -/
theorem haC_84000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 84000 := by
  have hlog : Real.log 84000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 84000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 84000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[83000, 84000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[83000, 84000]` SEGMENT: every zero with `83000 ≤ Im ≤ 84000` is on the line. -/
theorem segment_83000_84000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 84000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (83000:ℝ) ≤ ρ.im → ρ.im ≤ 84000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 83000 84000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_84000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 84000 via the HEIGHT CHAIN**: `[0,83000]` ∘ `[83000,84000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_84000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 84000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 84000 → ρ.re = 1 / 2 := by
  have hγ83000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 83000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 83000 84000
    (AllZeros_h83000.all_nontrivial_zeros_up_to_height_83000_of_bands
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
      hγ83000)
    (segment_83000_84000 hbands hγ)

end AllZeros_h84000
