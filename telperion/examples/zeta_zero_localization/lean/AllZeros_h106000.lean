/-  Height-chain step: all nontrivial zeta zeros up to height 106000 on Re = 1/2 --
    `AllZeros_h105000` + a `[105000, 106000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h105000
import RHInBoxT_1d4000000_3999999d4000000_105000_105026
import RHInBoxT_1d4000000_3999999d4000000_420103d4_105053
import RHInBoxT_1d4000000_3999999d4000000_105053_105079
import RHInBoxT_1d4000000_3999999d4000000_105079_105105
import RHInBoxT_1d4000000_3999999d4000000_105105_105132
import RHInBoxT_1d4000000_3999999d4000000_105132_105158
import RHInBoxT_1d4000000_3999999d4000000_105158_420737d4
import RHInBoxT_1d4000000_3999999d4000000_105184_105211
import RHInBoxT_1d4000000_3999999d4000000_105211_105237
import RHInBoxT_1d4000000_3999999d4000000_105237_105263
import RHInBoxT_1d4000000_3999999d4000000_105263_105289
import RHInBoxT_1d4000000_3999999d4000000_105289_105316
import RHInBoxT_1d4000000_3999999d4000000_105316_421369d4
import RHInBoxT_1d4000000_3999999d4000000_105342_105368
import RHInBoxT_1d4000000_3999999d4000000_105368_105395
import RHInBoxT_1d4000000_3999999d4000000_105395_105421
import RHInBoxT_1d4000000_3999999d4000000_421683d4_105447
import RHInBoxT_1d4000000_3999999d4000000_105447_105474
import RHInBoxT_1d4000000_3999999d4000000_105474_105500
import RHInBoxT_1d4000000_3999999d4000000_105500_105526
import RHInBoxT_1d4000000_3999999d4000000_105526_422213d4
import RHInBoxT_1d4000000_3999999d4000000_105553_105579
import RHInBoxT_1d4000000_3999999d4000000_105579_105605
import RHInBoxT_1d4000000_3999999d4000000_105605_105632
import RHInBoxT_1d4000000_3999999d4000000_105632_422633d4
import RHInBoxT_1d4000000_3999999d4000000_105658_105684
import RHInBoxT_1d4000000_3999999d4000000_105684_105711
import RHInBoxT_1d4000000_3999999d4000000_105711_422949d4
import RHInBoxT_1d4000000_3999999d4000000_105737_105763
import RHInBoxT_1d4000000_3999999d4000000_105763_105789
import RHInBoxT_1d4000000_3999999d4000000_105789_105816
import RHInBoxT_1d4000000_3999999d4000000_105816_105842
import RHInBoxT_1d4000000_3999999d4000000_105842_105868
import RHInBoxT_1d4000000_3999999d4000000_105868_105895
import RHInBoxT_1d4000000_3999999d4000000_105895_105921
import RHInBoxT_1d4000000_3999999d4000000_105921_105947
import RHInBoxT_1d4000000_3999999d4000000_423787d4_105974
import RHInBoxT_1d4000000_3999999d4000000_423895d4_106000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h106000

/-- The 38-band NOMINAL partition of `[105000, 106000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 105000
  | 1 => 105026
  | 2 => 105053
  | 3 => 105079
  | 4 => 105105
  | 5 => 105132
  | 6 => 105158
  | 7 => 105184
  | 8 => 105211
  | 9 => 105237
  | 10 => 105263
  | 11 => 105289
  | 12 => 105316
  | 13 => 105342
  | 14 => 105368
  | 15 => 105395
  | 16 => 105421
  | 17 => 105447
  | 18 => 105474
  | 19 => 105500
  | 20 => 105526
  | 21 => 105553
  | 22 => 105579
  | 23 => 105605
  | 24 => 105632
  | 25 => 105658
  | 26 => 105684
  | 27 => 105711
  | 28 => 105737
  | 29 => 105763
  | 30 => 105789
  | 31 => 105816
  | 32 => 105842
  | 33 => 105868
  | 34 => 105895
  | 35 => 105921
  | 36 => 105947
  | 37 => 105974
  | 38 => 106000
  | _ => 106000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((105000:ℝ)) ≤ (105026); norm_num
  · show ((105026:ℝ)) ≤ (105053); norm_num
  · show ((105053:ℝ)) ≤ (105079); norm_num
  · show ((105079:ℝ)) ≤ (105105); norm_num
  · show ((105105:ℝ)) ≤ (105132); norm_num
  · show ((105132:ℝ)) ≤ (105158); norm_num
  · show ((105158:ℝ)) ≤ (105184); norm_num
  · show ((105184:ℝ)) ≤ (105211); norm_num
  · show ((105211:ℝ)) ≤ (105237); norm_num
  · show ((105237:ℝ)) ≤ (105263); norm_num
  · show ((105263:ℝ)) ≤ (105289); norm_num
  · show ((105289:ℝ)) ≤ (105316); norm_num
  · show ((105316:ℝ)) ≤ (105342); norm_num
  · show ((105342:ℝ)) ≤ (105368); norm_num
  · show ((105368:ℝ)) ≤ (105395); norm_num
  · show ((105395:ℝ)) ≤ (105421); norm_num
  · show ((105421:ℝ)) ≤ (105447); norm_num
  · show ((105447:ℝ)) ≤ (105474); norm_num
  · show ((105474:ℝ)) ≤ (105500); norm_num
  · show ((105500:ℝ)) ≤ (105526); norm_num
  · show ((105526:ℝ)) ≤ (105553); norm_num
  · show ((105553:ℝ)) ≤ (105579); norm_num
  · show ((105579:ℝ)) ≤ (105605); norm_num
  · show ((105605:ℝ)) ≤ (105632); norm_num
  · show ((105632:ℝ)) ≤ (105658); norm_num
  · show ((105658:ℝ)) ≤ (105684); norm_num
  · show ((105684:ℝ)) ≤ (105711); norm_num
  · show ((105711:ℝ)) ≤ (105737); norm_num
  · show ((105737:ℝ)) ≤ (105763); norm_num
  · show ((105763:ℝ)) ≤ (105789); norm_num
  · show ((105789:ℝ)) ≤ (105816); norm_num
  · show ((105816:ℝ)) ≤ (105842); norm_num
  · show ((105842:ℝ)) ≤ (105868); norm_num
  · show ((105868:ℝ)) ≤ (105895); norm_num
  · show ((105895:ℝ)) ≤ (105921); norm_num
  · show ((105921:ℝ)) ≤ (105947); norm_num
  · show ((105947:ℝ)) ≤ (105974); norm_num
  · show ((105974:ℝ)) ≤ (106000); norm_num
  · show ((106000:ℝ)) ≤ (106000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 105000
  | 1 => 420103 / 4
  | 2 => 105053
  | 3 => 105079
  | 4 => 105105
  | 5 => 105132
  | 6 => 105158
  | 7 => 105184
  | 8 => 105211
  | 9 => 105237
  | 10 => 105263
  | 11 => 105289
  | 12 => 105316
  | 13 => 105342
  | 14 => 105368
  | 15 => 105395
  | 16 => 421683 / 4
  | 17 => 105447
  | 18 => 105474
  | 19 => 105500
  | 20 => 105526
  | 21 => 105553
  | 22 => 105579
  | 23 => 105605
  | 24 => 105632
  | 25 => 105658
  | 26 => 105684
  | 27 => 105711
  | 28 => 105737
  | 29 => 105763
  | 30 => 105789
  | 31 => 105816
  | 32 => 105842
  | 33 => 105868
  | 34 => 105895
  | 35 => 105921
  | 36 => 423787 / 4
  | 37 => 423895 / 4
  | _ => 423895 / 4

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 105026
  | 1 => 105053
  | 2 => 105079
  | 3 => 105105
  | 4 => 105132
  | 5 => 105158
  | 6 => 420737 / 4
  | 7 => 105211
  | 8 => 105237
  | 9 => 105263
  | 10 => 105289
  | 11 => 105316
  | 12 => 421369 / 4
  | 13 => 105368
  | 14 => 105395
  | 15 => 105421
  | 16 => 105447
  | 17 => 105474
  | 18 => 105500
  | 19 => 105526
  | 20 => 422213 / 4
  | 21 => 105579
  | 22 => 105605
  | 23 => 105632
  | 24 => 422633 / 4
  | 25 => 105684
  | 26 => 105711
  | 27 => 422949 / 4
  | 28 => 105763
  | 29 => 105789
  | 30 => 105816
  | 31 => 105842
  | 32 => 105868
  | 33 => 105895
  | 34 => 105921
  | 35 => 105947
  | 36 => 105974
  | 37 => 106000
  | _ => 106000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 106000` (`log 106000 ≤ 12`, `2.7^12 ≥ 106000`). -/
theorem haC_106000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 106000 := by
  have hlog : Real.log 106000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 106000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 106000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[105000, 106000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[105000, 106000]` SEGMENT: every zero with `105000 ≤ Im ≤ 106000` is on the line. -/
theorem segment_105000_106000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 106000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (105000:ℝ) ≤ ρ.im → ρ.im ≤ 106000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 105000 106000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_106000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 106000 via the HEIGHT CHAIN**: `[0,105000]` ∘ `[105000,106000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_106000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 106000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 106000 → ρ.re = 1 / 2 := by
  have hγ105000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 105000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 105000 106000
    (AllZeros_h105000.all_nontrivial_zeros_up_to_height_105000_of_bands
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
      hγ105000)
    (segment_105000_106000 hbands hγ)

end AllZeros_h106000
