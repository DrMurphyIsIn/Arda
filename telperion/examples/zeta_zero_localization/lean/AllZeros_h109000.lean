/-  Height-chain step: all nontrivial zeta zeros up to height 109000 on Re = 1/2 --
    `AllZeros_h108000` + a `[108000, 109000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h108000
import RHInBoxT_1d4000000_3999999d4000000_108000_108026
import RHInBoxT_1d4000000_3999999d4000000_108026_108053
import RHInBoxT_1d4000000_3999999d4000000_108053_108079
import RHInBoxT_1d4000000_3999999d4000000_108079_108105
import RHInBoxT_1d4000000_3999999d4000000_108105_108132
import RHInBoxT_1d4000000_3999999d4000000_108132_108158
import RHInBoxT_1d4000000_3999999d4000000_108158_108184
import RHInBoxT_1d4000000_3999999d4000000_108184_108211
import RHInBoxT_1d4000000_3999999d4000000_108211_108237
import RHInBoxT_1d4000000_3999999d4000000_108237_108263
import RHInBoxT_1d4000000_3999999d4000000_108263_108289
import RHInBoxT_1d4000000_3999999d4000000_433155d4_108316
import RHInBoxT_1d4000000_3999999d4000000_108316_108342
import RHInBoxT_1d4000000_3999999d4000000_108342_433473d4
import RHInBoxT_1d4000000_3999999d4000000_108368_108395
import RHInBoxT_1d4000000_3999999d4000000_108395_108421
import RHInBoxT_1d4000000_3999999d4000000_108421_108447
import RHInBoxT_1d4000000_3999999d4000000_108447_433897d4
import RHInBoxT_1d4000000_3999999d4000000_108474_108500
import RHInBoxT_1d4000000_3999999d4000000_108500_108526
import RHInBoxT_1d4000000_3999999d4000000_108526_108553
import RHInBoxT_1d4000000_3999999d4000000_108553_108579
import RHInBoxT_1d4000000_3999999d4000000_108579_108605
import RHInBoxT_1d4000000_3999999d4000000_108605_108632
import RHInBoxT_1d4000000_3999999d4000000_108632_108658
import RHInBoxT_1d4000000_3999999d4000000_108658_108684
import RHInBoxT_1d4000000_3999999d4000000_108684_108711
import RHInBoxT_1d4000000_3999999d4000000_108711_108737
import RHInBoxT_1d4000000_3999999d4000000_108737_108763
import RHInBoxT_1d4000000_3999999d4000000_108763_108789
import RHInBoxT_1d4000000_3999999d4000000_108789_108816
import RHInBoxT_1d4000000_3999999d4000000_435263d4_108842
import RHInBoxT_1d4000000_3999999d4000000_108842_108868
import RHInBoxT_1d4000000_3999999d4000000_108868_108895
import RHInBoxT_1d4000000_3999999d4000000_108895_108921
import RHInBoxT_1d4000000_3999999d4000000_108921_108947
import RHInBoxT_1d4000000_3999999d4000000_108947_435897d4
import RHInBoxT_1d4000000_3999999d4000000_108974_109000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h109000

/-- The 38-band NOMINAL partition of `[108000, 109000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 108000
  | 1 => 108026
  | 2 => 108053
  | 3 => 108079
  | 4 => 108105
  | 5 => 108132
  | 6 => 108158
  | 7 => 108184
  | 8 => 108211
  | 9 => 108237
  | 10 => 108263
  | 11 => 108289
  | 12 => 108316
  | 13 => 108342
  | 14 => 108368
  | 15 => 108395
  | 16 => 108421
  | 17 => 108447
  | 18 => 108474
  | 19 => 108500
  | 20 => 108526
  | 21 => 108553
  | 22 => 108579
  | 23 => 108605
  | 24 => 108632
  | 25 => 108658
  | 26 => 108684
  | 27 => 108711
  | 28 => 108737
  | 29 => 108763
  | 30 => 108789
  | 31 => 108816
  | 32 => 108842
  | 33 => 108868
  | 34 => 108895
  | 35 => 108921
  | 36 => 108947
  | 37 => 108974
  | 38 => 109000
  | _ => 109000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((108000:ℝ)) ≤ (108026); norm_num
  · show ((108026:ℝ)) ≤ (108053); norm_num
  · show ((108053:ℝ)) ≤ (108079); norm_num
  · show ((108079:ℝ)) ≤ (108105); norm_num
  · show ((108105:ℝ)) ≤ (108132); norm_num
  · show ((108132:ℝ)) ≤ (108158); norm_num
  · show ((108158:ℝ)) ≤ (108184); norm_num
  · show ((108184:ℝ)) ≤ (108211); norm_num
  · show ((108211:ℝ)) ≤ (108237); norm_num
  · show ((108237:ℝ)) ≤ (108263); norm_num
  · show ((108263:ℝ)) ≤ (108289); norm_num
  · show ((108289:ℝ)) ≤ (108316); norm_num
  · show ((108316:ℝ)) ≤ (108342); norm_num
  · show ((108342:ℝ)) ≤ (108368); norm_num
  · show ((108368:ℝ)) ≤ (108395); norm_num
  · show ((108395:ℝ)) ≤ (108421); norm_num
  · show ((108421:ℝ)) ≤ (108447); norm_num
  · show ((108447:ℝ)) ≤ (108474); norm_num
  · show ((108474:ℝ)) ≤ (108500); norm_num
  · show ((108500:ℝ)) ≤ (108526); norm_num
  · show ((108526:ℝ)) ≤ (108553); norm_num
  · show ((108553:ℝ)) ≤ (108579); norm_num
  · show ((108579:ℝ)) ≤ (108605); norm_num
  · show ((108605:ℝ)) ≤ (108632); norm_num
  · show ((108632:ℝ)) ≤ (108658); norm_num
  · show ((108658:ℝ)) ≤ (108684); norm_num
  · show ((108684:ℝ)) ≤ (108711); norm_num
  · show ((108711:ℝ)) ≤ (108737); norm_num
  · show ((108737:ℝ)) ≤ (108763); norm_num
  · show ((108763:ℝ)) ≤ (108789); norm_num
  · show ((108789:ℝ)) ≤ (108816); norm_num
  · show ((108816:ℝ)) ≤ (108842); norm_num
  · show ((108842:ℝ)) ≤ (108868); norm_num
  · show ((108868:ℝ)) ≤ (108895); norm_num
  · show ((108895:ℝ)) ≤ (108921); norm_num
  · show ((108921:ℝ)) ≤ (108947); norm_num
  · show ((108947:ℝ)) ≤ (108974); norm_num
  · show ((108974:ℝ)) ≤ (109000); norm_num
  · show ((109000:ℝ)) ≤ (109000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 108000
  | 1 => 108026
  | 2 => 108053
  | 3 => 108079
  | 4 => 108105
  | 5 => 108132
  | 6 => 108158
  | 7 => 108184
  | 8 => 108211
  | 9 => 108237
  | 10 => 108263
  | 11 => 433155 / 4
  | 12 => 108316
  | 13 => 108342
  | 14 => 108368
  | 15 => 108395
  | 16 => 108421
  | 17 => 108447
  | 18 => 108474
  | 19 => 108500
  | 20 => 108526
  | 21 => 108553
  | 22 => 108579
  | 23 => 108605
  | 24 => 108632
  | 25 => 108658
  | 26 => 108684
  | 27 => 108711
  | 28 => 108737
  | 29 => 108763
  | 30 => 108789
  | 31 => 435263 / 4
  | 32 => 108842
  | 33 => 108868
  | 34 => 108895
  | 35 => 108921
  | 36 => 108947
  | 37 => 108974
  | _ => 108974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 108026
  | 1 => 108053
  | 2 => 108079
  | 3 => 108105
  | 4 => 108132
  | 5 => 108158
  | 6 => 108184
  | 7 => 108211
  | 8 => 108237
  | 9 => 108263
  | 10 => 108289
  | 11 => 108316
  | 12 => 108342
  | 13 => 433473 / 4
  | 14 => 108395
  | 15 => 108421
  | 16 => 108447
  | 17 => 433897 / 4
  | 18 => 108500
  | 19 => 108526
  | 20 => 108553
  | 21 => 108579
  | 22 => 108605
  | 23 => 108632
  | 24 => 108658
  | 25 => 108684
  | 26 => 108711
  | 27 => 108737
  | 28 => 108763
  | 29 => 108789
  | 30 => 108816
  | 31 => 108842
  | 32 => 108868
  | 33 => 108895
  | 34 => 108921
  | 35 => 108947
  | 36 => 435897 / 4
  | 37 => 109000
  | _ => 109000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 109000` (`log 109000 ≤ 12`, `2.7^12 ≥ 109000`). -/
theorem haC_109000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 109000 := by
  have hlog : Real.log 109000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 109000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 109000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[108000, 109000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[108000, 109000]` SEGMENT: every zero with `108000 ≤ Im ≤ 109000` is on the line. -/
theorem segment_108000_109000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 109000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (108000:ℝ) ≤ ρ.im → ρ.im ≤ 109000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 108000 109000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_109000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 109000 via the HEIGHT CHAIN**: `[0,108000]` ∘ `[108000,109000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_109000_of_bands
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
    (hbands_100000 : AllZeros_h100000.BandHyp)
    (hbands_101000 : AllZeros_h101000.BandHyp)
    (hbands_102000 : AllZeros_h102000.BandHyp)
    (hbands_103000 : AllZeros_h103000.BandHyp)
    (hbands_104000 : AllZeros_h104000.BandHyp)
    (hbands_105000 : AllZeros_h105000.BandHyp)
    (hbands_106000 : AllZeros_h106000.BandHyp)
    (hbands_107000 : AllZeros_h107000.BandHyp)
    (hbands_108000 : AllZeros_h108000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 109000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 109000 → ρ.re = 1 / 2 := by
  have hγ108000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 108000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 108000 109000
    (AllZeros_h108000.all_nontrivial_zeros_up_to_height_108000_of_bands
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
      hbands_100000
      hbands_101000
      hbands_102000
      hbands_103000
      hbands_104000
      hbands_105000
      hbands_106000
      hbands_107000
      hbands_108000
      hγ108000)
    (segment_108000_109000 hbands hγ)

end AllZeros_h109000
