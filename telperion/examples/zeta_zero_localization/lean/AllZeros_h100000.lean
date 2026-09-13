/-  Height-chain step: all nontrivial zeta zeros up to height 100000 on Re = 1/2 --
    `AllZeros_h99000` + a `[99000, 100000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h99000
import RHInBoxT_1d4000000_3999999d4000000_99000_99026
import RHInBoxT_1d4000000_3999999d4000000_99026_99053
import RHInBoxT_1d4000000_3999999d4000000_396211d4_99079
import RHInBoxT_1d4000000_3999999d4000000_99079_99105
import RHInBoxT_1d4000000_3999999d4000000_99105_99132
import RHInBoxT_1d4000000_3999999d4000000_99132_99158
import RHInBoxT_1d4000000_3999999d4000000_396631d4_99184
import RHInBoxT_1d4000000_3999999d4000000_99184_99211
import RHInBoxT_1d4000000_3999999d4000000_99211_396949d4
import RHInBoxT_1d4000000_3999999d4000000_99237_99263
import RHInBoxT_1d4000000_3999999d4000000_99263_99289
import RHInBoxT_1d4000000_3999999d4000000_99289_99316
import RHInBoxT_1d4000000_3999999d4000000_397263d4_99342
import RHInBoxT_1d4000000_3999999d4000000_397367d4_99368
import RHInBoxT_1d4000000_3999999d4000000_99368_99395
import RHInBoxT_1d4000000_3999999d4000000_99395_99421
import RHInBoxT_1d4000000_3999999d4000000_99421_397789d4
import RHInBoxT_1d4000000_3999999d4000000_99447_99474
import RHInBoxT_1d4000000_3999999d4000000_99474_99500
import RHInBoxT_1d4000000_3999999d4000000_99500_199053d2
import RHInBoxT_1d4000000_3999999d4000000_99526_99553
import RHInBoxT_1d4000000_3999999d4000000_99553_99579
import RHInBoxT_1d4000000_3999999d4000000_99579_99605
import RHInBoxT_1d4000000_3999999d4000000_99605_99632
import RHInBoxT_1d4000000_3999999d4000000_99632_99658
import RHInBoxT_1d4000000_3999999d4000000_99658_99684
import RHInBoxT_1d4000000_3999999d4000000_99684_99711
import RHInBoxT_1d4000000_3999999d4000000_398843d4_99737
import RHInBoxT_1d4000000_3999999d4000000_99737_99763
import RHInBoxT_1d4000000_3999999d4000000_99763_99789
import RHInBoxT_1d4000000_3999999d4000000_99789_399265d4
import RHInBoxT_1d4000000_3999999d4000000_99816_99842
import RHInBoxT_1d4000000_3999999d4000000_99842_99868
import RHInBoxT_1d4000000_3999999d4000000_99868_99895
import RHInBoxT_1d4000000_3999999d4000000_99895_99921
import RHInBoxT_1d4000000_3999999d4000000_399683d4_99947
import RHInBoxT_1d4000000_3999999d4000000_399787d4_99974
import RHInBoxT_1d4000000_3999999d4000000_99974_100000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h100000

/-- The 38-band NOMINAL partition of `[99000, 100000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 99000
  | 1 => 99026
  | 2 => 99053
  | 3 => 99079
  | 4 => 99105
  | 5 => 99132
  | 6 => 99158
  | 7 => 99184
  | 8 => 99211
  | 9 => 99237
  | 10 => 99263
  | 11 => 99289
  | 12 => 99316
  | 13 => 99342
  | 14 => 99368
  | 15 => 99395
  | 16 => 99421
  | 17 => 99447
  | 18 => 99474
  | 19 => 99500
  | 20 => 99526
  | 21 => 99553
  | 22 => 99579
  | 23 => 99605
  | 24 => 99632
  | 25 => 99658
  | 26 => 99684
  | 27 => 99711
  | 28 => 99737
  | 29 => 99763
  | 30 => 99789
  | 31 => 99816
  | 32 => 99842
  | 33 => 99868
  | 34 => 99895
  | 35 => 99921
  | 36 => 99947
  | 37 => 99974
  | 38 => 100000
  | _ => 100000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((99000:ℝ)) ≤ (99026); norm_num
  · show ((99026:ℝ)) ≤ (99053); norm_num
  · show ((99053:ℝ)) ≤ (99079); norm_num
  · show ((99079:ℝ)) ≤ (99105); norm_num
  · show ((99105:ℝ)) ≤ (99132); norm_num
  · show ((99132:ℝ)) ≤ (99158); norm_num
  · show ((99158:ℝ)) ≤ (99184); norm_num
  · show ((99184:ℝ)) ≤ (99211); norm_num
  · show ((99211:ℝ)) ≤ (99237); norm_num
  · show ((99237:ℝ)) ≤ (99263); norm_num
  · show ((99263:ℝ)) ≤ (99289); norm_num
  · show ((99289:ℝ)) ≤ (99316); norm_num
  · show ((99316:ℝ)) ≤ (99342); norm_num
  · show ((99342:ℝ)) ≤ (99368); norm_num
  · show ((99368:ℝ)) ≤ (99395); norm_num
  · show ((99395:ℝ)) ≤ (99421); norm_num
  · show ((99421:ℝ)) ≤ (99447); norm_num
  · show ((99447:ℝ)) ≤ (99474); norm_num
  · show ((99474:ℝ)) ≤ (99500); norm_num
  · show ((99500:ℝ)) ≤ (99526); norm_num
  · show ((99526:ℝ)) ≤ (99553); norm_num
  · show ((99553:ℝ)) ≤ (99579); norm_num
  · show ((99579:ℝ)) ≤ (99605); norm_num
  · show ((99605:ℝ)) ≤ (99632); norm_num
  · show ((99632:ℝ)) ≤ (99658); norm_num
  · show ((99658:ℝ)) ≤ (99684); norm_num
  · show ((99684:ℝ)) ≤ (99711); norm_num
  · show ((99711:ℝ)) ≤ (99737); norm_num
  · show ((99737:ℝ)) ≤ (99763); norm_num
  · show ((99763:ℝ)) ≤ (99789); norm_num
  · show ((99789:ℝ)) ≤ (99816); norm_num
  · show ((99816:ℝ)) ≤ (99842); norm_num
  · show ((99842:ℝ)) ≤ (99868); norm_num
  · show ((99868:ℝ)) ≤ (99895); norm_num
  · show ((99895:ℝ)) ≤ (99921); norm_num
  · show ((99921:ℝ)) ≤ (99947); norm_num
  · show ((99947:ℝ)) ≤ (99974); norm_num
  · show ((99974:ℝ)) ≤ (100000); norm_num
  · show ((100000:ℝ)) ≤ (100000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 99000
  | 1 => 99026
  | 2 => 396211 / 4
  | 3 => 99079
  | 4 => 99105
  | 5 => 99132
  | 6 => 396631 / 4
  | 7 => 99184
  | 8 => 99211
  | 9 => 99237
  | 10 => 99263
  | 11 => 99289
  | 12 => 397263 / 4
  | 13 => 397367 / 4
  | 14 => 99368
  | 15 => 99395
  | 16 => 99421
  | 17 => 99447
  | 18 => 99474
  | 19 => 99500
  | 20 => 99526
  | 21 => 99553
  | 22 => 99579
  | 23 => 99605
  | 24 => 99632
  | 25 => 99658
  | 26 => 99684
  | 27 => 398843 / 4
  | 28 => 99737
  | 29 => 99763
  | 30 => 99789
  | 31 => 99816
  | 32 => 99842
  | 33 => 99868
  | 34 => 99895
  | 35 => 399683 / 4
  | 36 => 399787 / 4
  | 37 => 99974
  | _ => 99974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 99026
  | 1 => 99053
  | 2 => 99079
  | 3 => 99105
  | 4 => 99132
  | 5 => 99158
  | 6 => 99184
  | 7 => 99211
  | 8 => 396949 / 4
  | 9 => 99263
  | 10 => 99289
  | 11 => 99316
  | 12 => 99342
  | 13 => 99368
  | 14 => 99395
  | 15 => 99421
  | 16 => 397789 / 4
  | 17 => 99474
  | 18 => 99500
  | 19 => 199053 / 2
  | 20 => 99553
  | 21 => 99579
  | 22 => 99605
  | 23 => 99632
  | 24 => 99658
  | 25 => 99684
  | 26 => 99711
  | 27 => 99737
  | 28 => 99763
  | 29 => 99789
  | 30 => 399265 / 4
  | 31 => 99842
  | 32 => 99868
  | 33 => 99895
  | 34 => 99921
  | 35 => 99947
  | 36 => 99974
  | 37 => 100000
  | _ => 100000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 100000` (`log 100000 ≤ 12`, `2.7^12 ≥ 100000`). -/
theorem haC_100000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 100000 := by
  have hlog : Real.log 100000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 100000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 100000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[99000, 100000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[99000, 100000]` SEGMENT: every zero with `99000 ≤ Im ≤ 100000` is on the line. -/
theorem segment_99000_100000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (99000:ℝ) ≤ ρ.im → ρ.im ≤ 100000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 99000 100000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_100000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 100000 via the HEIGHT CHAIN**: `[0,99000]` ∘ `[99000,100000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_100000_of_bands
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
    (hbands_90000 : AllZeros_h90000.BandHyp)
    (hbands_91000 : AllZeros_h91000.BandHyp)
    (hbands_92000 : AllZeros_h92000.BandHyp)
    (hbands_93000 : AllZeros_h93000.BandHyp)
    (hbands_94000 : AllZeros_h94000.BandHyp)
    (hbands_95000 : AllZeros_h95000.BandHyp)
    (hbands_96000 : AllZeros_h96000.BandHyp)
    (hbands_97000 : AllZeros_h97000.BandHyp)
    (hbands_98000 : AllZeros_h98000.BandHyp)
    (hbands_99000 : AllZeros_h99000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100000 → ρ.re = 1 / 2 := by
  have hγ99000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 99000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 99000 100000
    (AllZeros_h99000.all_nontrivial_zeros_up_to_height_99000_of_bands
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
      hbands_90000
      hbands_91000
      hbands_92000
      hbands_93000
      hbands_94000
      hbands_95000
      hbands_96000
      hbands_97000
      hbands_98000
      hbands_99000
      hγ99000)
    (segment_99000_100000 hbands hγ)

end AllZeros_h100000
