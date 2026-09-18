/-  Height-chain step: all nontrivial zeta zeros up to height 349000 on Re = 1/2 --
    `AllZeros_h348000` + a `[348000, 349000]` SEGMENT certificate (42 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h348000
import RHInBoxT_1d4000000_3999999d4000000_1391999d4_1392097d4
import RHInBoxT_1d4000000_3999999d4000000_348024_348048
import RHInBoxT_1d4000000_3999999d4000000_348048_348071
import RHInBoxT_1d4000000_3999999d4000000_348071_348095
import RHInBoxT_1d4000000_3999999d4000000_1392379d4_348119
import RHInBoxT_1d4000000_3999999d4000000_1392475d4_348143
import RHInBoxT_1d4000000_3999999d4000000_348143_348167
import RHInBoxT_1d4000000_3999999d4000000_348167_348190
import RHInBoxT_1d4000000_3999999d4000000_348190_348214
import RHInBoxT_1d4000000_3999999d4000000_348214_348238
import RHInBoxT_1d4000000_3999999d4000000_348238_348262
import RHInBoxT_1d4000000_3999999d4000000_1393047d4_348286
import RHInBoxT_1d4000000_3999999d4000000_348286_348310
import RHInBoxT_1d4000000_3999999d4000000_348310_348333
import RHInBoxT_1d4000000_3999999d4000000_348333_348357
import RHInBoxT_1d4000000_3999999d4000000_348357_348381
import RHInBoxT_1d4000000_3999999d4000000_348381_1393621d4
import RHInBoxT_1d4000000_3999999d4000000_348405_348429
import RHInBoxT_1d4000000_3999999d4000000_348429_348452
import RHInBoxT_1d4000000_3999999d4000000_348452_348476
import RHInBoxT_1d4000000_3999999d4000000_348476_348500
import RHInBoxT_1d4000000_3999999d4000000_348500_348524
import RHInBoxT_1d4000000_3999999d4000000_348524_348548
import RHInBoxT_1d4000000_3999999d4000000_348548_348571
import RHInBoxT_1d4000000_3999999d4000000_348571_348595
import RHInBoxT_1d4000000_3999999d4000000_348595_1394477d4
import RHInBoxT_1d4000000_3999999d4000000_348619_348643
import RHInBoxT_1d4000000_3999999d4000000_348643_348667
import RHInBoxT_1d4000000_3999999d4000000_1394667d4_1394761d4
import RHInBoxT_1d4000000_3999999d4000000_348690_348714
import RHInBoxT_1d4000000_3999999d4000000_348714_348738
import RHInBoxT_1d4000000_3999999d4000000_348738_348762
import RHInBoxT_1d4000000_3999999d4000000_1395047d4_348786
import RHInBoxT_1d4000000_3999999d4000000_348786_348810
import RHInBoxT_1d4000000_3999999d4000000_348810_348833
import RHInBoxT_1d4000000_3999999d4000000_1395331d4_1395429d4
import RHInBoxT_1d4000000_3999999d4000000_348857_348881
import RHInBoxT_1d4000000_3999999d4000000_348881_348905
import RHInBoxT_1d4000000_3999999d4000000_1395619d4_348929
import RHInBoxT_1d4000000_3999999d4000000_348929_1395809d4
import RHInBoxT_1d4000000_3999999d4000000_348952_348976
import RHInBoxT_1d4000000_3999999d4000000_348976_349000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h349000

/-- The 42-band NOMINAL partition of `[348000, 349000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 348000
  | 1 => 348024
  | 2 => 348048
  | 3 => 348071
  | 4 => 348095
  | 5 => 348119
  | 6 => 348143
  | 7 => 348167
  | 8 => 348190
  | 9 => 348214
  | 10 => 348238
  | 11 => 348262
  | 12 => 348286
  | 13 => 348310
  | 14 => 348333
  | 15 => 348357
  | 16 => 348381
  | 17 => 348405
  | 18 => 348429
  | 19 => 348452
  | 20 => 348476
  | 21 => 348500
  | 22 => 348524
  | 23 => 348548
  | 24 => 348571
  | 25 => 348595
  | 26 => 348619
  | 27 => 348643
  | 28 => 348667
  | 29 => 348690
  | 30 => 348714
  | 31 => 348738
  | 32 => 348762
  | 33 => 348786
  | 34 => 348810
  | 35 => 348833
  | 36 => 348857
  | 37 => 348881
  | 38 => 348905
  | 39 => 348929
  | 40 => 348952
  | 41 => 348976
  | 42 => 349000
  | _ => 349000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((348000:ℝ)) ≤ (348024); norm_num
  · show ((348024:ℝ)) ≤ (348048); norm_num
  · show ((348048:ℝ)) ≤ (348071); norm_num
  · show ((348071:ℝ)) ≤ (348095); norm_num
  · show ((348095:ℝ)) ≤ (348119); norm_num
  · show ((348119:ℝ)) ≤ (348143); norm_num
  · show ((348143:ℝ)) ≤ (348167); norm_num
  · show ((348167:ℝ)) ≤ (348190); norm_num
  · show ((348190:ℝ)) ≤ (348214); norm_num
  · show ((348214:ℝ)) ≤ (348238); norm_num
  · show ((348238:ℝ)) ≤ (348262); norm_num
  · show ((348262:ℝ)) ≤ (348286); norm_num
  · show ((348286:ℝ)) ≤ (348310); norm_num
  · show ((348310:ℝ)) ≤ (348333); norm_num
  · show ((348333:ℝ)) ≤ (348357); norm_num
  · show ((348357:ℝ)) ≤ (348381); norm_num
  · show ((348381:ℝ)) ≤ (348405); norm_num
  · show ((348405:ℝ)) ≤ (348429); norm_num
  · show ((348429:ℝ)) ≤ (348452); norm_num
  · show ((348452:ℝ)) ≤ (348476); norm_num
  · show ((348476:ℝ)) ≤ (348500); norm_num
  · show ((348500:ℝ)) ≤ (348524); norm_num
  · show ((348524:ℝ)) ≤ (348548); norm_num
  · show ((348548:ℝ)) ≤ (348571); norm_num
  · show ((348571:ℝ)) ≤ (348595); norm_num
  · show ((348595:ℝ)) ≤ (348619); norm_num
  · show ((348619:ℝ)) ≤ (348643); norm_num
  · show ((348643:ℝ)) ≤ (348667); norm_num
  · show ((348667:ℝ)) ≤ (348690); norm_num
  · show ((348690:ℝ)) ≤ (348714); norm_num
  · show ((348714:ℝ)) ≤ (348738); norm_num
  · show ((348738:ℝ)) ≤ (348762); norm_num
  · show ((348762:ℝ)) ≤ (348786); norm_num
  · show ((348786:ℝ)) ≤ (348810); norm_num
  · show ((348810:ℝ)) ≤ (348833); norm_num
  · show ((348833:ℝ)) ≤ (348857); norm_num
  · show ((348857:ℝ)) ≤ (348881); norm_num
  · show ((348881:ℝ)) ≤ (348905); norm_num
  · show ((348905:ℝ)) ≤ (348929); norm_num
  · show ((348929:ℝ)) ≤ (348952); norm_num
  · show ((348952:ℝ)) ≤ (348976); norm_num
  · show ((348976:ℝ)) ≤ (349000); norm_num
  · show ((349000:ℝ)) ≤ (349000); norm_num
  · exact le_refl _

/-- The lower edges of the 42 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 1391999 / 4
  | 1 => 348024
  | 2 => 348048
  | 3 => 348071
  | 4 => 1392379 / 4
  | 5 => 1392475 / 4
  | 6 => 348143
  | 7 => 348167
  | 8 => 348190
  | 9 => 348214
  | 10 => 348238
  | 11 => 1393047 / 4
  | 12 => 348286
  | 13 => 348310
  | 14 => 348333
  | 15 => 348357
  | 16 => 348381
  | 17 => 348405
  | 18 => 348429
  | 19 => 348452
  | 20 => 348476
  | 21 => 348500
  | 22 => 348524
  | 23 => 348548
  | 24 => 348571
  | 25 => 348595
  | 26 => 348619
  | 27 => 348643
  | 28 => 1394667 / 4
  | 29 => 348690
  | 30 => 348714
  | 31 => 348738
  | 32 => 1395047 / 4
  | 33 => 348786
  | 34 => 348810
  | 35 => 1395331 / 4
  | 36 => 348857
  | 37 => 348881
  | 38 => 1395619 / 4
  | 39 => 348929
  | 40 => 348952
  | 41 => 348976
  | _ => 348976

/-- The upper edges of the 42 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 1392097 / 4
  | 1 => 348048
  | 2 => 348071
  | 3 => 348095
  | 4 => 348119
  | 5 => 348143
  | 6 => 348167
  | 7 => 348190
  | 8 => 348214
  | 9 => 348238
  | 10 => 348262
  | 11 => 348286
  | 12 => 348310
  | 13 => 348333
  | 14 => 348357
  | 15 => 348381
  | 16 => 1393621 / 4
  | 17 => 348429
  | 18 => 348452
  | 19 => 348476
  | 20 => 348500
  | 21 => 348524
  | 22 => 348548
  | 23 => 348571
  | 24 => 348595
  | 25 => 1394477 / 4
  | 26 => 348643
  | 27 => 348667
  | 28 => 1394761 / 4
  | 29 => 348714
  | 30 => 348738
  | 31 => 348762
  | 32 => 348786
  | 33 => 348810
  | 34 => 348833
  | 35 => 1395429 / 4
  | 36 => 348881
  | 37 => 348905
  | 38 => 348929
  | 39 => 1395809 / 4
  | 40 => 348976
  | 41 => 349000
  | _ => 349000

set_option maxHeartbeats 1600000 in
/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 42 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 349000` (`log 349000 ≤ 13`, `2.7^13 ≥ 349000`). -/
theorem haC_349000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 349000 := by
  have hlog : Real.log 349000 ≤ 13 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h13 : Real.exp 13 = (Real.exp 1) ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 13 ≤ (Real.exp 1) ^ 13 := pow_le_pow_left₀ (by norm_num) he1 13
    rw [h13]; nlinarith [hpow]
  have hpos : 0 < Real.log 349000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 349000
      ≤ (1 / 4000000) * 13 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[348000, 349000]` segment's band hypothesis: every band `i < 42` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 42 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 42 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[348000, 349000]` SEGMENT: every zero with `348000 ≤ Im ≤ 349000` is on the line. -/
theorem segment_348000_349000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 349000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (348000:ℝ) ≤ ρ.im → ρ.im ≤ 349000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 348000 349000 bndSeg 42 (by norm_num) bndSeg_mono rfl rfl haC_349000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 349000 via the HEIGHT CHAIN**: `[0,348000]` ∘ `[348000,349000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_349000_of_bands
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
    (hbands_110000 : AllZeros_h110000.BandHyp)
    (hbands_111000 : AllZeros_h111000.BandHyp)
    (hbands_112000 : AllZeros_h112000.BandHyp)
    (hbands_113000 : AllZeros_h113000.BandHyp)
    (hbands_114000 : AllZeros_h114000.BandHyp)
    (hbands_115000 : AllZeros_h115000.BandHyp)
    (hbands_116000 : AllZeros_h116000.BandHyp)
    (hbands_117000 : AllZeros_h117000.BandHyp)
    (hbands_118000 : AllZeros_h118000.BandHyp)
    (hbands_119000 : AllZeros_h119000.BandHyp)
    (hbands_120000 : AllZeros_h120000.BandHyp)
    (hbands_121000 : AllZeros_h121000.BandHyp)
    (hbands_122000 : AllZeros_h122000.BandHyp)
    (hbands_123000 : AllZeros_h123000.BandHyp)
    (hbands_124000 : AllZeros_h124000.BandHyp)
    (hbands_125000 : AllZeros_h125000.BandHyp)
    (hbands_126000 : AllZeros_h126000.BandHyp)
    (hbands_127000 : AllZeros_h127000.BandHyp)
    (hbands_128000 : AllZeros_h128000.BandHyp)
    (hbands_129000 : AllZeros_h129000.BandHyp)
    (hbands_130000 : AllZeros_h130000.BandHyp)
    (hbands_131000 : AllZeros_h131000.BandHyp)
    (hbands_132000 : AllZeros_h132000.BandHyp)
    (hbands_133000 : AllZeros_h133000.BandHyp)
    (hbands_134000 : AllZeros_h134000.BandHyp)
    (hbands_135000 : AllZeros_h135000.BandHyp)
    (hbands_136000 : AllZeros_h136000.BandHyp)
    (hbands_137000 : AllZeros_h137000.BandHyp)
    (hbands_138000 : AllZeros_h138000.BandHyp)
    (hbands_139000 : AllZeros_h139000.BandHyp)
    (hbands_140000 : AllZeros_h140000.BandHyp)
    (hbands_141000 : AllZeros_h141000.BandHyp)
    (hbands_142000 : AllZeros_h142000.BandHyp)
    (hbands_143000 : AllZeros_h143000.BandHyp)
    (hbands_144000 : AllZeros_h144000.BandHyp)
    (hbands_145000 : AllZeros_h145000.BandHyp)
    (hbands_146000 : AllZeros_h146000.BandHyp)
    (hbands_147000 : AllZeros_h147000.BandHyp)
    (hbands_148000 : AllZeros_h148000.BandHyp)
    (hbands_149000 : AllZeros_h149000.BandHyp)
    (hbands_150000 : AllZeros_h150000.BandHyp)
    (hbands_151000 : AllZeros_h151000.BandHyp)
    (hbands_152000 : AllZeros_h152000.BandHyp)
    (hbands_153000 : AllZeros_h153000.BandHyp)
    (hbands_154000 : AllZeros_h154000.BandHyp)
    (hbands_155000 : AllZeros_h155000.BandHyp)
    (hbands_156000 : AllZeros_h156000.BandHyp)
    (hbands_157000 : AllZeros_h157000.BandHyp)
    (hbands_158000 : AllZeros_h158000.BandHyp)
    (hbands_159000 : AllZeros_h159000.BandHyp)
    (hbands_160000 : AllZeros_h160000.BandHyp)
    (hbands_161000 : AllZeros_h161000.BandHyp)
    (hbands_162000 : AllZeros_h162000.BandHyp)
    (hbands_163000 : AllZeros_h163000.BandHyp)
    (hbands_164000 : AllZeros_h164000.BandHyp)
    (hbands_165000 : AllZeros_h165000.BandHyp)
    (hbands_166000 : AllZeros_h166000.BandHyp)
    (hbands_167000 : AllZeros_h167000.BandHyp)
    (hbands_168000 : AllZeros_h168000.BandHyp)
    (hbands_169000 : AllZeros_h169000.BandHyp)
    (hbands_170000 : AllZeros_h170000.BandHyp)
    (hbands_171000 : AllZeros_h171000.BandHyp)
    (hbands_172000 : AllZeros_h172000.BandHyp)
    (hbands_173000 : AllZeros_h173000.BandHyp)
    (hbands_174000 : AllZeros_h174000.BandHyp)
    (hbands_175000 : AllZeros_h175000.BandHyp)
    (hbands_176000 : AllZeros_h176000.BandHyp)
    (hbands_177000 : AllZeros_h177000.BandHyp)
    (hbands_178000 : AllZeros_h178000.BandHyp)
    (hbands_179000 : AllZeros_h179000.BandHyp)
    (hbands_180000 : AllZeros_h180000.BandHyp)
    (hbands_181000 : AllZeros_h181000.BandHyp)
    (hbands_182000 : AllZeros_h182000.BandHyp)
    (hbands_183000 : AllZeros_h183000.BandHyp)
    (hbands_184000 : AllZeros_h184000.BandHyp)
    (hbands_185000 : AllZeros_h185000.BandHyp)
    (hbands_186000 : AllZeros_h186000.BandHyp)
    (hbands_187000 : AllZeros_h187000.BandHyp)
    (hbands_188000 : AllZeros_h188000.BandHyp)
    (hbands_189000 : AllZeros_h189000.BandHyp)
    (hbands_190000 : AllZeros_h190000.BandHyp)
    (hbands_191000 : AllZeros_h191000.BandHyp)
    (hbands_192000 : AllZeros_h192000.BandHyp)
    (hbands_193000 : AllZeros_h193000.BandHyp)
    (hbands_194000 : AllZeros_h194000.BandHyp)
    (hbands_195000 : AllZeros_h195000.BandHyp)
    (hbands_196000 : AllZeros_h196000.BandHyp)
    (hbands_197000 : AllZeros_h197000.BandHyp)
    (hbands_198000 : AllZeros_h198000.BandHyp)
    (hbands_199000 : AllZeros_h199000.BandHyp)
    (hbands_200000 : AllZeros_h200000.BandHyp)
    (hbands_201000 : AllZeros_h201000.BandHyp)
    (hbands_202000 : AllZeros_h202000.BandHyp)
    (hbands_203000 : AllZeros_h203000.BandHyp)
    (hbands_204000 : AllZeros_h204000.BandHyp)
    (hbands_205000 : AllZeros_h205000.BandHyp)
    (hbands_206000 : AllZeros_h206000.BandHyp)
    (hbands_207000 : AllZeros_h207000.BandHyp)
    (hbands_208000 : AllZeros_h208000.BandHyp)
    (hbands_209000 : AllZeros_h209000.BandHyp)
    (hbands_210000 : AllZeros_h210000.BandHyp)
    (hbands_211000 : AllZeros_h211000.BandHyp)
    (hbands_212000 : AllZeros_h212000.BandHyp)
    (hbands_213000 : AllZeros_h213000.BandHyp)
    (hbands_214000 : AllZeros_h214000.BandHyp)
    (hbands_215000 : AllZeros_h215000.BandHyp)
    (hbands_216000 : AllZeros_h216000.BandHyp)
    (hbands_217000 : AllZeros_h217000.BandHyp)
    (hbands_218000 : AllZeros_h218000.BandHyp)
    (hbands_219000 : AllZeros_h219000.BandHyp)
    (hbands_220000 : AllZeros_h220000.BandHyp)
    (hbands_221000 : AllZeros_h221000.BandHyp)
    (hbands_222000 : AllZeros_h222000.BandHyp)
    (hbands_223000 : AllZeros_h223000.BandHyp)
    (hbands_224000 : AllZeros_h224000.BandHyp)
    (hbands_225000 : AllZeros_h225000.BandHyp)
    (hbands_226000 : AllZeros_h226000.BandHyp)
    (hbands_227000 : AllZeros_h227000.BandHyp)
    (hbands_228000 : AllZeros_h228000.BandHyp)
    (hbands_229000 : AllZeros_h229000.BandHyp)
    (hbands_230000 : AllZeros_h230000.BandHyp)
    (hbands_231000 : AllZeros_h231000.BandHyp)
    (hbands_232000 : AllZeros_h232000.BandHyp)
    (hbands_233000 : AllZeros_h233000.BandHyp)
    (hbands_234000 : AllZeros_h234000.BandHyp)
    (hbands_235000 : AllZeros_h235000.BandHyp)
    (hbands_236000 : AllZeros_h236000.BandHyp)
    (hbands_237000 : AllZeros_h237000.BandHyp)
    (hbands_238000 : AllZeros_h238000.BandHyp)
    (hbands_239000 : AllZeros_h239000.BandHyp)
    (hbands_240000 : AllZeros_h240000.BandHyp)
    (hbands_241000 : AllZeros_h241000.BandHyp)
    (hbands_242000 : AllZeros_h242000.BandHyp)
    (hbands_243000 : AllZeros_h243000.BandHyp)
    (hbands_244000 : AllZeros_h244000.BandHyp)
    (hbands_245000 : AllZeros_h245000.BandHyp)
    (hbands_246000 : AllZeros_h246000.BandHyp)
    (hbands_247000 : AllZeros_h247000.BandHyp)
    (hbands_248000 : AllZeros_h248000.BandHyp)
    (hbands_249000 : AllZeros_h249000.BandHyp)
    (hbands_250000 : AllZeros_h250000.BandHyp)
    (hbands_251000 : AllZeros_h251000.BandHyp)
    (hbands_252000 : AllZeros_h252000.BandHyp)
    (hbands_253000 : AllZeros_h253000.BandHyp)
    (hbands_254000 : AllZeros_h254000.BandHyp)
    (hbands_255000 : AllZeros_h255000.BandHyp)
    (hbands_256000 : AllZeros_h256000.BandHyp)
    (hbands_257000 : AllZeros_h257000.BandHyp)
    (hbands_258000 : AllZeros_h258000.BandHyp)
    (hbands_259000 : AllZeros_h259000.BandHyp)
    (hbands_260000 : AllZeros_h260000.BandHyp)
    (hbands_261000 : AllZeros_h261000.BandHyp)
    (hbands_262000 : AllZeros_h262000.BandHyp)
    (hbands_263000 : AllZeros_h263000.BandHyp)
    (hbands_264000 : AllZeros_h264000.BandHyp)
    (hbands_265000 : AllZeros_h265000.BandHyp)
    (hbands_266000 : AllZeros_h266000.BandHyp)
    (hbands_267000 : AllZeros_h267000.BandHyp)
    (hbands_268000 : AllZeros_h268000.BandHyp)
    (hbands_269000 : AllZeros_h269000.BandHyp)
    (hbands_270000 : AllZeros_h270000.BandHyp)
    (hbands_271000 : AllZeros_h271000.BandHyp)
    (hbands_272000 : AllZeros_h272000.BandHyp)
    (hbands_273000 : AllZeros_h273000.BandHyp)
    (hbands_274000 : AllZeros_h274000.BandHyp)
    (hbands_275000 : AllZeros_h275000.BandHyp)
    (hbands_276000 : AllZeros_h276000.BandHyp)
    (hbands_277000 : AllZeros_h277000.BandHyp)
    (hbands_278000 : AllZeros_h278000.BandHyp)
    (hbands_279000 : AllZeros_h279000.BandHyp)
    (hbands_280000 : AllZeros_h280000.BandHyp)
    (hbands_281000 : AllZeros_h281000.BandHyp)
    (hbands_282000 : AllZeros_h282000.BandHyp)
    (hbands_283000 : AllZeros_h283000.BandHyp)
    (hbands_284000 : AllZeros_h284000.BandHyp)
    (hbands_285000 : AllZeros_h285000.BandHyp)
    (hbands_286000 : AllZeros_h286000.BandHyp)
    (hbands_287000 : AllZeros_h287000.BandHyp)
    (hbands_288000 : AllZeros_h288000.BandHyp)
    (hbands_289000 : AllZeros_h289000.BandHyp)
    (hbands_290000 : AllZeros_h290000.BandHyp)
    (hbands_291000 : AllZeros_h291000.BandHyp)
    (hbands_292000 : AllZeros_h292000.BandHyp)
    (hbands_293000 : AllZeros_h293000.BandHyp)
    (hbands_294000 : AllZeros_h294000.BandHyp)
    (hbands_295000 : AllZeros_h295000.BandHyp)
    (hbands_296000 : AllZeros_h296000.BandHyp)
    (hbands_297000 : AllZeros_h297000.BandHyp)
    (hbands_298000 : AllZeros_h298000.BandHyp)
    (hbands_299000 : AllZeros_h299000.BandHyp)
    (hbands_300000 : AllZeros_h300000.BandHyp)
    (hbands_301000 : AllZeros_h301000.BandHyp)
    (hbands_302000 : AllZeros_h302000.BandHyp)
    (hbands_303000 : AllZeros_h303000.BandHyp)
    (hbands_304000 : AllZeros_h304000.BandHyp)
    (hbands_305000 : AllZeros_h305000.BandHyp)
    (hbands_306000 : AllZeros_h306000.BandHyp)
    (hbands_307000 : AllZeros_h307000.BandHyp)
    (hbands_308000 : AllZeros_h308000.BandHyp)
    (hbands_309000 : AllZeros_h309000.BandHyp)
    (hbands_310000 : AllZeros_h310000.BandHyp)
    (hbands_311000 : AllZeros_h311000.BandHyp)
    (hbands_312000 : AllZeros_h312000.BandHyp)
    (hbands_313000 : AllZeros_h313000.BandHyp)
    (hbands_314000 : AllZeros_h314000.BandHyp)
    (hbands_315000 : AllZeros_h315000.BandHyp)
    (hbands_316000 : AllZeros_h316000.BandHyp)
    (hbands_317000 : AllZeros_h317000.BandHyp)
    (hbands_318000 : AllZeros_h318000.BandHyp)
    (hbands_319000 : AllZeros_h319000.BandHyp)
    (hbands_320000 : AllZeros_h320000.BandHyp)
    (hbands_321000 : AllZeros_h321000.BandHyp)
    (hbands_322000 : AllZeros_h322000.BandHyp)
    (hbands_323000 : AllZeros_h323000.BandHyp)
    (hbands_324000 : AllZeros_h324000.BandHyp)
    (hbands_325000 : AllZeros_h325000.BandHyp)
    (hbands_326000 : AllZeros_h326000.BandHyp)
    (hbands_327000 : AllZeros_h327000.BandHyp)
    (hbands_328000 : AllZeros_h328000.BandHyp)
    (hbands_329000 : AllZeros_h329000.BandHyp)
    (hbands_330000 : AllZeros_h330000.BandHyp)
    (hbands_331000 : AllZeros_h331000.BandHyp)
    (hbands_332000 : AllZeros_h332000.BandHyp)
    (hbands_333000 : AllZeros_h333000.BandHyp)
    (hbands_334000 : AllZeros_h334000.BandHyp)
    (hbands_335000 : AllZeros_h335000.BandHyp)
    (hbands_336000 : AllZeros_h336000.BandHyp)
    (hbands_337000 : AllZeros_h337000.BandHyp)
    (hbands_338000 : AllZeros_h338000.BandHyp)
    (hbands_339000 : AllZeros_h339000.BandHyp)
    (hbands_340000 : AllZeros_h340000.BandHyp)
    (hbands_341000 : AllZeros_h341000.BandHyp)
    (hbands_342000 : AllZeros_h342000.BandHyp)
    (hbands_343000 : AllZeros_h343000.BandHyp)
    (hbands_344000 : AllZeros_h344000.BandHyp)
    (hbands_345000 : AllZeros_h345000.BandHyp)
    (hbands_346000 : AllZeros_h346000.BandHyp)
    (hbands_347000 : AllZeros_h347000.BandHyp)
    (hbands_348000 : AllZeros_h348000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 349000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 349000 → ρ.re = 1 / 2 := by
  have hγ348000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 348000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 348000 349000
    (AllZeros_h348000.all_nontrivial_zeros_up_to_height_348000_of_bands
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
      hbands_110000
      hbands_111000
      hbands_112000
      hbands_113000
      hbands_114000
      hbands_115000
      hbands_116000
      hbands_117000
      hbands_118000
      hbands_119000
      hbands_120000
      hbands_121000
      hbands_122000
      hbands_123000
      hbands_124000
      hbands_125000
      hbands_126000
      hbands_127000
      hbands_128000
      hbands_129000
      hbands_130000
      hbands_131000
      hbands_132000
      hbands_133000
      hbands_134000
      hbands_135000
      hbands_136000
      hbands_137000
      hbands_138000
      hbands_139000
      hbands_140000
      hbands_141000
      hbands_142000
      hbands_143000
      hbands_144000
      hbands_145000
      hbands_146000
      hbands_147000
      hbands_148000
      hbands_149000
      hbands_150000
      hbands_151000
      hbands_152000
      hbands_153000
      hbands_154000
      hbands_155000
      hbands_156000
      hbands_157000
      hbands_158000
      hbands_159000
      hbands_160000
      hbands_161000
      hbands_162000
      hbands_163000
      hbands_164000
      hbands_165000
      hbands_166000
      hbands_167000
      hbands_168000
      hbands_169000
      hbands_170000
      hbands_171000
      hbands_172000
      hbands_173000
      hbands_174000
      hbands_175000
      hbands_176000
      hbands_177000
      hbands_178000
      hbands_179000
      hbands_180000
      hbands_181000
      hbands_182000
      hbands_183000
      hbands_184000
      hbands_185000
      hbands_186000
      hbands_187000
      hbands_188000
      hbands_189000
      hbands_190000
      hbands_191000
      hbands_192000
      hbands_193000
      hbands_194000
      hbands_195000
      hbands_196000
      hbands_197000
      hbands_198000
      hbands_199000
      hbands_200000
      hbands_201000
      hbands_202000
      hbands_203000
      hbands_204000
      hbands_205000
      hbands_206000
      hbands_207000
      hbands_208000
      hbands_209000
      hbands_210000
      hbands_211000
      hbands_212000
      hbands_213000
      hbands_214000
      hbands_215000
      hbands_216000
      hbands_217000
      hbands_218000
      hbands_219000
      hbands_220000
      hbands_221000
      hbands_222000
      hbands_223000
      hbands_224000
      hbands_225000
      hbands_226000
      hbands_227000
      hbands_228000
      hbands_229000
      hbands_230000
      hbands_231000
      hbands_232000
      hbands_233000
      hbands_234000
      hbands_235000
      hbands_236000
      hbands_237000
      hbands_238000
      hbands_239000
      hbands_240000
      hbands_241000
      hbands_242000
      hbands_243000
      hbands_244000
      hbands_245000
      hbands_246000
      hbands_247000
      hbands_248000
      hbands_249000
      hbands_250000
      hbands_251000
      hbands_252000
      hbands_253000
      hbands_254000
      hbands_255000
      hbands_256000
      hbands_257000
      hbands_258000
      hbands_259000
      hbands_260000
      hbands_261000
      hbands_262000
      hbands_263000
      hbands_264000
      hbands_265000
      hbands_266000
      hbands_267000
      hbands_268000
      hbands_269000
      hbands_270000
      hbands_271000
      hbands_272000
      hbands_273000
      hbands_274000
      hbands_275000
      hbands_276000
      hbands_277000
      hbands_278000
      hbands_279000
      hbands_280000
      hbands_281000
      hbands_282000
      hbands_283000
      hbands_284000
      hbands_285000
      hbands_286000
      hbands_287000
      hbands_288000
      hbands_289000
      hbands_290000
      hbands_291000
      hbands_292000
      hbands_293000
      hbands_294000
      hbands_295000
      hbands_296000
      hbands_297000
      hbands_298000
      hbands_299000
      hbands_300000
      hbands_301000
      hbands_302000
      hbands_303000
      hbands_304000
      hbands_305000
      hbands_306000
      hbands_307000
      hbands_308000
      hbands_309000
      hbands_310000
      hbands_311000
      hbands_312000
      hbands_313000
      hbands_314000
      hbands_315000
      hbands_316000
      hbands_317000
      hbands_318000
      hbands_319000
      hbands_320000
      hbands_321000
      hbands_322000
      hbands_323000
      hbands_324000
      hbands_325000
      hbands_326000
      hbands_327000
      hbands_328000
      hbands_329000
      hbands_330000
      hbands_331000
      hbands_332000
      hbands_333000
      hbands_334000
      hbands_335000
      hbands_336000
      hbands_337000
      hbands_338000
      hbands_339000
      hbands_340000
      hbands_341000
      hbands_342000
      hbands_343000
      hbands_344000
      hbands_345000
      hbands_346000
      hbands_347000
      hbands_348000
      hγ348000)
    (segment_348000_349000 hbands hγ)

end AllZeros_h349000
