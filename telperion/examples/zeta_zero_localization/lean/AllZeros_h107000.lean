/-  Height-chain step: all nontrivial zeta zeros up to height 107000 on Re = 1/2 --
    `AllZeros_h106000` + a `[106000, 107000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h106000
import RHInBoxT_1d4000000_3999999d4000000_106000_106026
import RHInBoxT_1d4000000_3999999d4000000_106026_106053
import RHInBoxT_1d4000000_3999999d4000000_106053_106079
import RHInBoxT_1d4000000_3999999d4000000_106079_424421d4
import RHInBoxT_1d4000000_3999999d4000000_106105_106132
import RHInBoxT_1d4000000_3999999d4000000_106132_106158
import RHInBoxT_1d4000000_3999999d4000000_106158_106184
import RHInBoxT_1d4000000_3999999d4000000_106184_106211
import RHInBoxT_1d4000000_3999999d4000000_106211_106237
import RHInBoxT_1d4000000_3999999d4000000_106237_106263
import RHInBoxT_1d4000000_3999999d4000000_106263_106289
import RHInBoxT_1d4000000_3999999d4000000_106289_106316
import RHInBoxT_1d4000000_3999999d4000000_106316_425369d4
import RHInBoxT_1d4000000_3999999d4000000_106342_106368
import RHInBoxT_1d4000000_3999999d4000000_106368_106395
import RHInBoxT_1d4000000_3999999d4000000_106395_106421
import RHInBoxT_1d4000000_3999999d4000000_106421_106447
import RHInBoxT_1d4000000_3999999d4000000_106447_106474
import RHInBoxT_1d4000000_3999999d4000000_106474_106500
import RHInBoxT_1d4000000_3999999d4000000_106500_106526
import RHInBoxT_1d4000000_3999999d4000000_106526_106553
import RHInBoxT_1d4000000_3999999d4000000_106553_106579
import RHInBoxT_1d4000000_3999999d4000000_426315d4_426421d4
import RHInBoxT_1d4000000_3999999d4000000_106605_106632
import RHInBoxT_1d4000000_3999999d4000000_106632_106658
import RHInBoxT_1d4000000_3999999d4000000_426631d4_426737d4
import RHInBoxT_1d4000000_3999999d4000000_106684_106711
import RHInBoxT_1d4000000_3999999d4000000_106711_106737
import RHInBoxT_1d4000000_3999999d4000000_106737_427053d4
import RHInBoxT_1d4000000_3999999d4000000_106763_106789
import RHInBoxT_1d4000000_3999999d4000000_106789_106816
import RHInBoxT_1d4000000_3999999d4000000_427263d4_427369d4
import RHInBoxT_1d4000000_3999999d4000000_106842_106868
import RHInBoxT_1d4000000_3999999d4000000_106868_106895
import RHInBoxT_1d4000000_3999999d4000000_106895_106921
import RHInBoxT_1d4000000_3999999d4000000_106921_427789d4
import RHInBoxT_1d4000000_3999999d4000000_106947_427897d4
import RHInBoxT_1d4000000_3999999d4000000_106974_428001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h107000

/-- The 38-band NOMINAL partition of `[106000, 107000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 106000
  | 1 => 106026
  | 2 => 106053
  | 3 => 106079
  | 4 => 106105
  | 5 => 106132
  | 6 => 106158
  | 7 => 106184
  | 8 => 106211
  | 9 => 106237
  | 10 => 106263
  | 11 => 106289
  | 12 => 106316
  | 13 => 106342
  | 14 => 106368
  | 15 => 106395
  | 16 => 106421
  | 17 => 106447
  | 18 => 106474
  | 19 => 106500
  | 20 => 106526
  | 21 => 106553
  | 22 => 106579
  | 23 => 106605
  | 24 => 106632
  | 25 => 106658
  | 26 => 106684
  | 27 => 106711
  | 28 => 106737
  | 29 => 106763
  | 30 => 106789
  | 31 => 106816
  | 32 => 106842
  | 33 => 106868
  | 34 => 106895
  | 35 => 106921
  | 36 => 106947
  | 37 => 106974
  | 38 => 107000
  | _ => 107000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((106000:ℝ)) ≤ (106026); norm_num
  · show ((106026:ℝ)) ≤ (106053); norm_num
  · show ((106053:ℝ)) ≤ (106079); norm_num
  · show ((106079:ℝ)) ≤ (106105); norm_num
  · show ((106105:ℝ)) ≤ (106132); norm_num
  · show ((106132:ℝ)) ≤ (106158); norm_num
  · show ((106158:ℝ)) ≤ (106184); norm_num
  · show ((106184:ℝ)) ≤ (106211); norm_num
  · show ((106211:ℝ)) ≤ (106237); norm_num
  · show ((106237:ℝ)) ≤ (106263); norm_num
  · show ((106263:ℝ)) ≤ (106289); norm_num
  · show ((106289:ℝ)) ≤ (106316); norm_num
  · show ((106316:ℝ)) ≤ (106342); norm_num
  · show ((106342:ℝ)) ≤ (106368); norm_num
  · show ((106368:ℝ)) ≤ (106395); norm_num
  · show ((106395:ℝ)) ≤ (106421); norm_num
  · show ((106421:ℝ)) ≤ (106447); norm_num
  · show ((106447:ℝ)) ≤ (106474); norm_num
  · show ((106474:ℝ)) ≤ (106500); norm_num
  · show ((106500:ℝ)) ≤ (106526); norm_num
  · show ((106526:ℝ)) ≤ (106553); norm_num
  · show ((106553:ℝ)) ≤ (106579); norm_num
  · show ((106579:ℝ)) ≤ (106605); norm_num
  · show ((106605:ℝ)) ≤ (106632); norm_num
  · show ((106632:ℝ)) ≤ (106658); norm_num
  · show ((106658:ℝ)) ≤ (106684); norm_num
  · show ((106684:ℝ)) ≤ (106711); norm_num
  · show ((106711:ℝ)) ≤ (106737); norm_num
  · show ((106737:ℝ)) ≤ (106763); norm_num
  · show ((106763:ℝ)) ≤ (106789); norm_num
  · show ((106789:ℝ)) ≤ (106816); norm_num
  · show ((106816:ℝ)) ≤ (106842); norm_num
  · show ((106842:ℝ)) ≤ (106868); norm_num
  · show ((106868:ℝ)) ≤ (106895); norm_num
  · show ((106895:ℝ)) ≤ (106921); norm_num
  · show ((106921:ℝ)) ≤ (106947); norm_num
  · show ((106947:ℝ)) ≤ (106974); norm_num
  · show ((106974:ℝ)) ≤ (107000); norm_num
  · show ((107000:ℝ)) ≤ (107000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 106000
  | 1 => 106026
  | 2 => 106053
  | 3 => 106079
  | 4 => 106105
  | 5 => 106132
  | 6 => 106158
  | 7 => 106184
  | 8 => 106211
  | 9 => 106237
  | 10 => 106263
  | 11 => 106289
  | 12 => 106316
  | 13 => 106342
  | 14 => 106368
  | 15 => 106395
  | 16 => 106421
  | 17 => 106447
  | 18 => 106474
  | 19 => 106500
  | 20 => 106526
  | 21 => 106553
  | 22 => 426315 / 4
  | 23 => 106605
  | 24 => 106632
  | 25 => 426631 / 4
  | 26 => 106684
  | 27 => 106711
  | 28 => 106737
  | 29 => 106763
  | 30 => 106789
  | 31 => 427263 / 4
  | 32 => 106842
  | 33 => 106868
  | 34 => 106895
  | 35 => 106921
  | 36 => 106947
  | 37 => 106974
  | _ => 106974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 106026
  | 1 => 106053
  | 2 => 106079
  | 3 => 424421 / 4
  | 4 => 106132
  | 5 => 106158
  | 6 => 106184
  | 7 => 106211
  | 8 => 106237
  | 9 => 106263
  | 10 => 106289
  | 11 => 106316
  | 12 => 425369 / 4
  | 13 => 106368
  | 14 => 106395
  | 15 => 106421
  | 16 => 106447
  | 17 => 106474
  | 18 => 106500
  | 19 => 106526
  | 20 => 106553
  | 21 => 106579
  | 22 => 426421 / 4
  | 23 => 106632
  | 24 => 106658
  | 25 => 426737 / 4
  | 26 => 106711
  | 27 => 106737
  | 28 => 427053 / 4
  | 29 => 106789
  | 30 => 106816
  | 31 => 427369 / 4
  | 32 => 106868
  | 33 => 106895
  | 34 => 106921
  | 35 => 427789 / 4
  | 36 => 427897 / 4
  | 37 => 428001 / 4
  | _ => 428001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 107000` (`log 107000 ≤ 12`, `2.7^12 ≥ 107000`). -/
theorem haC_107000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 107000 := by
  have hlog : Real.log 107000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 107000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 107000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[106000, 107000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[106000, 107000]` SEGMENT: every zero with `106000 ≤ Im ≤ 107000` is on the line. -/
theorem segment_106000_107000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 107000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (106000:ℝ) ≤ ρ.im → ρ.im ≤ 107000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 106000 107000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_107000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 107000 via the HEIGHT CHAIN**: `[0,106000]` ∘ `[106000,107000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_107000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 107000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 107000 → ρ.re = 1 / 2 := by
  have hγ106000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 106000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 106000 107000
    (AllZeros_h106000.all_nontrivial_zeros_up_to_height_106000_of_bands
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
      hγ106000)
    (segment_106000_107000 hbands hγ)

end AllZeros_h107000
