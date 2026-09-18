/-  Height-chain step: all nontrivial zeta zeros up to height 110000 on Re = 1/2 --
    `AllZeros_h109000` + a `[109000, 110000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h109000
import RHInBoxT_1d4000000_3999999d4000000_109000_109026
import RHInBoxT_1d4000000_3999999d4000000_109026_109053
import RHInBoxT_1d4000000_3999999d4000000_109053_109079
import RHInBoxT_1d4000000_3999999d4000000_109079_109105
import RHInBoxT_1d4000000_3999999d4000000_109105_109132
import RHInBoxT_1d4000000_3999999d4000000_436527d4_109158
import RHInBoxT_1d4000000_3999999d4000000_109158_109184
import RHInBoxT_1d4000000_3999999d4000000_109184_109211
import RHInBoxT_1d4000000_3999999d4000000_109211_109237
import RHInBoxT_1d4000000_3999999d4000000_109237_109263
import RHInBoxT_1d4000000_3999999d4000000_109263_109289
import RHInBoxT_1d4000000_3999999d4000000_109289_109316
import RHInBoxT_1d4000000_3999999d4000000_109316_109342
import RHInBoxT_1d4000000_3999999d4000000_109342_437473d4
import RHInBoxT_1d4000000_3999999d4000000_109368_109395
import RHInBoxT_1d4000000_3999999d4000000_109395_109421
import RHInBoxT_1d4000000_3999999d4000000_109421_109447
import RHInBoxT_1d4000000_3999999d4000000_109447_437897d4
import RHInBoxT_1d4000000_3999999d4000000_109474_438001d4
import RHInBoxT_1d4000000_3999999d4000000_109500_109526
import RHInBoxT_1d4000000_3999999d4000000_109526_109553
import RHInBoxT_1d4000000_3999999d4000000_109553_109579
import RHInBoxT_1d4000000_3999999d4000000_109579_438421d4
import RHInBoxT_1d4000000_3999999d4000000_109605_109632
import RHInBoxT_1d4000000_3999999d4000000_109632_109658
import RHInBoxT_1d4000000_3999999d4000000_109658_109684
import RHInBoxT_1d4000000_3999999d4000000_109684_109711
import RHInBoxT_1d4000000_3999999d4000000_109711_109737
import RHInBoxT_1d4000000_3999999d4000000_109737_109763
import RHInBoxT_1d4000000_3999999d4000000_109763_109789
import RHInBoxT_1d4000000_3999999d4000000_109789_109816
import RHInBoxT_1d4000000_3999999d4000000_109816_439369d4
import RHInBoxT_1d4000000_3999999d4000000_109842_109868
import RHInBoxT_1d4000000_3999999d4000000_109868_109895
import RHInBoxT_1d4000000_3999999d4000000_109895_109921
import RHInBoxT_1d4000000_3999999d4000000_109921_109947
import RHInBoxT_1d4000000_3999999d4000000_109947_109974
import RHInBoxT_1d4000000_3999999d4000000_109974_110000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h110000

/-- The 38-band NOMINAL partition of `[109000, 110000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 109000
  | 1 => 109026
  | 2 => 109053
  | 3 => 109079
  | 4 => 109105
  | 5 => 109132
  | 6 => 109158
  | 7 => 109184
  | 8 => 109211
  | 9 => 109237
  | 10 => 109263
  | 11 => 109289
  | 12 => 109316
  | 13 => 109342
  | 14 => 109368
  | 15 => 109395
  | 16 => 109421
  | 17 => 109447
  | 18 => 109474
  | 19 => 109500
  | 20 => 109526
  | 21 => 109553
  | 22 => 109579
  | 23 => 109605
  | 24 => 109632
  | 25 => 109658
  | 26 => 109684
  | 27 => 109711
  | 28 => 109737
  | 29 => 109763
  | 30 => 109789
  | 31 => 109816
  | 32 => 109842
  | 33 => 109868
  | 34 => 109895
  | 35 => 109921
  | 36 => 109947
  | 37 => 109974
  | 38 => 110000
  | _ => 110000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((109000:ℝ)) ≤ (109026); norm_num
  · show ((109026:ℝ)) ≤ (109053); norm_num
  · show ((109053:ℝ)) ≤ (109079); norm_num
  · show ((109079:ℝ)) ≤ (109105); norm_num
  · show ((109105:ℝ)) ≤ (109132); norm_num
  · show ((109132:ℝ)) ≤ (109158); norm_num
  · show ((109158:ℝ)) ≤ (109184); norm_num
  · show ((109184:ℝ)) ≤ (109211); norm_num
  · show ((109211:ℝ)) ≤ (109237); norm_num
  · show ((109237:ℝ)) ≤ (109263); norm_num
  · show ((109263:ℝ)) ≤ (109289); norm_num
  · show ((109289:ℝ)) ≤ (109316); norm_num
  · show ((109316:ℝ)) ≤ (109342); norm_num
  · show ((109342:ℝ)) ≤ (109368); norm_num
  · show ((109368:ℝ)) ≤ (109395); norm_num
  · show ((109395:ℝ)) ≤ (109421); norm_num
  · show ((109421:ℝ)) ≤ (109447); norm_num
  · show ((109447:ℝ)) ≤ (109474); norm_num
  · show ((109474:ℝ)) ≤ (109500); norm_num
  · show ((109500:ℝ)) ≤ (109526); norm_num
  · show ((109526:ℝ)) ≤ (109553); norm_num
  · show ((109553:ℝ)) ≤ (109579); norm_num
  · show ((109579:ℝ)) ≤ (109605); norm_num
  · show ((109605:ℝ)) ≤ (109632); norm_num
  · show ((109632:ℝ)) ≤ (109658); norm_num
  · show ((109658:ℝ)) ≤ (109684); norm_num
  · show ((109684:ℝ)) ≤ (109711); norm_num
  · show ((109711:ℝ)) ≤ (109737); norm_num
  · show ((109737:ℝ)) ≤ (109763); norm_num
  · show ((109763:ℝ)) ≤ (109789); norm_num
  · show ((109789:ℝ)) ≤ (109816); norm_num
  · show ((109816:ℝ)) ≤ (109842); norm_num
  · show ((109842:ℝ)) ≤ (109868); norm_num
  · show ((109868:ℝ)) ≤ (109895); norm_num
  · show ((109895:ℝ)) ≤ (109921); norm_num
  · show ((109921:ℝ)) ≤ (109947); norm_num
  · show ((109947:ℝ)) ≤ (109974); norm_num
  · show ((109974:ℝ)) ≤ (110000); norm_num
  · show ((110000:ℝ)) ≤ (110000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 109000
  | 1 => 109026
  | 2 => 109053
  | 3 => 109079
  | 4 => 109105
  | 5 => 436527 / 4
  | 6 => 109158
  | 7 => 109184
  | 8 => 109211
  | 9 => 109237
  | 10 => 109263
  | 11 => 109289
  | 12 => 109316
  | 13 => 109342
  | 14 => 109368
  | 15 => 109395
  | 16 => 109421
  | 17 => 109447
  | 18 => 109474
  | 19 => 109500
  | 20 => 109526
  | 21 => 109553
  | 22 => 109579
  | 23 => 109605
  | 24 => 109632
  | 25 => 109658
  | 26 => 109684
  | 27 => 109711
  | 28 => 109737
  | 29 => 109763
  | 30 => 109789
  | 31 => 109816
  | 32 => 109842
  | 33 => 109868
  | 34 => 109895
  | 35 => 109921
  | 36 => 109947
  | 37 => 109974
  | _ => 109974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 109026
  | 1 => 109053
  | 2 => 109079
  | 3 => 109105
  | 4 => 109132
  | 5 => 109158
  | 6 => 109184
  | 7 => 109211
  | 8 => 109237
  | 9 => 109263
  | 10 => 109289
  | 11 => 109316
  | 12 => 109342
  | 13 => 437473 / 4
  | 14 => 109395
  | 15 => 109421
  | 16 => 109447
  | 17 => 437897 / 4
  | 18 => 438001 / 4
  | 19 => 109526
  | 20 => 109553
  | 21 => 109579
  | 22 => 438421 / 4
  | 23 => 109632
  | 24 => 109658
  | 25 => 109684
  | 26 => 109711
  | 27 => 109737
  | 28 => 109763
  | 29 => 109789
  | 30 => 109816
  | 31 => 439369 / 4
  | 32 => 109868
  | 33 => 109895
  | 34 => 109921
  | 35 => 109947
  | 36 => 109974
  | 37 => 110000
  | _ => 110000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 110000` (`log 110000 ≤ 12`, `2.7^12 ≥ 110000`). -/
theorem haC_110000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 110000 := by
  have hlog : Real.log 110000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 110000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 110000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[109000, 110000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[109000, 110000]` SEGMENT: every zero with `109000 ≤ Im ≤ 110000` is on the line. -/
theorem segment_109000_110000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 110000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (109000:ℝ) ≤ ρ.im → ρ.im ≤ 110000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 109000 110000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_110000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 110000 via the HEIGHT CHAIN**: `[0,109000]` ∘ `[109000,110000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_110000_of_bands
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
    (hbands_109000 : AllZeros_h109000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 110000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 110000 → ρ.re = 1 / 2 := by
  have hγ109000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 109000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 109000 110000
    (AllZeros_h109000.all_nontrivial_zeros_up_to_height_109000_of_bands
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
      hbands_109000
      hγ109000)
    (segment_109000_110000 hbands hγ)

end AllZeros_h110000
