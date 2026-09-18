/-  Height-chain step: all nontrivial zeta zeros up to height 31000 on Re = 1/2 --
    `AllZeros_h30000` + a `[30000, 31000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h30000
import RHInBoxT_1d4000000_3999999d4000000_30000_120121d4
import RHInBoxT_1d4000000_3999999d4000000_30030_30061
import RHInBoxT_1d4000000_3999999d4000000_30061_30091
import RHInBoxT_1d4000000_3999999d4000000_120363d4_30121
import RHInBoxT_1d4000000_3999999d4000000_30121_30152
import RHInBoxT_1d4000000_3999999d4000000_30152_30182
import RHInBoxT_1d4000000_3999999d4000000_30182_30212
import RHInBoxT_1d4000000_3999999d4000000_30212_30242
import RHInBoxT_1d4000000_3999999d4000000_30242_30273
import RHInBoxT_1d4000000_3999999d4000000_30273_121213d4
import RHInBoxT_1d4000000_3999999d4000000_30303_30333
import RHInBoxT_1d4000000_3999999d4000000_30333_30364
import RHInBoxT_1d4000000_3999999d4000000_30364_30394
import RHInBoxT_1d4000000_3999999d4000000_30394_30424
import RHInBoxT_1d4000000_3999999d4000000_30424_30455
import RHInBoxT_1d4000000_3999999d4000000_30455_30485
import RHInBoxT_1d4000000_3999999d4000000_30485_30515
import RHInBoxT_1d4000000_3999999d4000000_30515_30545
import RHInBoxT_1d4000000_3999999d4000000_30545_30576
import RHInBoxT_1d4000000_3999999d4000000_30576_30606
import RHInBoxT_1d4000000_3999999d4000000_30606_30636
import RHInBoxT_1d4000000_3999999d4000000_122543d4_122669d4
import RHInBoxT_1d4000000_3999999d4000000_30667_30697
import RHInBoxT_1d4000000_3999999d4000000_30697_30727
import RHInBoxT_1d4000000_3999999d4000000_30727_30758
import RHInBoxT_1d4000000_3999999d4000000_30758_123153d4
import RHInBoxT_1d4000000_3999999d4000000_30788_30818
import RHInBoxT_1d4000000_3999999d4000000_30818_30848
import RHInBoxT_1d4000000_3999999d4000000_30848_30879
import RHInBoxT_1d4000000_3999999d4000000_30879_30909
import RHInBoxT_1d4000000_3999999d4000000_123635d4_30939
import RHInBoxT_1d4000000_3999999d4000000_30939_30970
import RHInBoxT_1d4000000_3999999d4000000_30970_31000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h31000

/-- The 33-band NOMINAL partition of `[30000, 31000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 30000
  | 1 => 30030
  | 2 => 30061
  | 3 => 30091
  | 4 => 30121
  | 5 => 30152
  | 6 => 30182
  | 7 => 30212
  | 8 => 30242
  | 9 => 30273
  | 10 => 30303
  | 11 => 30333
  | 12 => 30364
  | 13 => 30394
  | 14 => 30424
  | 15 => 30455
  | 16 => 30485
  | 17 => 30515
  | 18 => 30545
  | 19 => 30576
  | 20 => 30606
  | 21 => 30636
  | 22 => 30667
  | 23 => 30697
  | 24 => 30727
  | 25 => 30758
  | 26 => 30788
  | 27 => 30818
  | 28 => 30848
  | 29 => 30879
  | 30 => 30909
  | 31 => 30939
  | 32 => 30970
  | 33 => 31000
  | _ => 31000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((30000:ℝ)) ≤ (30030); norm_num
  · show ((30030:ℝ)) ≤ (30061); norm_num
  · show ((30061:ℝ)) ≤ (30091); norm_num
  · show ((30091:ℝ)) ≤ (30121); norm_num
  · show ((30121:ℝ)) ≤ (30152); norm_num
  · show ((30152:ℝ)) ≤ (30182); norm_num
  · show ((30182:ℝ)) ≤ (30212); norm_num
  · show ((30212:ℝ)) ≤ (30242); norm_num
  · show ((30242:ℝ)) ≤ (30273); norm_num
  · show ((30273:ℝ)) ≤ (30303); norm_num
  · show ((30303:ℝ)) ≤ (30333); norm_num
  · show ((30333:ℝ)) ≤ (30364); norm_num
  · show ((30364:ℝ)) ≤ (30394); norm_num
  · show ((30394:ℝ)) ≤ (30424); norm_num
  · show ((30424:ℝ)) ≤ (30455); norm_num
  · show ((30455:ℝ)) ≤ (30485); norm_num
  · show ((30485:ℝ)) ≤ (30515); norm_num
  · show ((30515:ℝ)) ≤ (30545); norm_num
  · show ((30545:ℝ)) ≤ (30576); norm_num
  · show ((30576:ℝ)) ≤ (30606); norm_num
  · show ((30606:ℝ)) ≤ (30636); norm_num
  · show ((30636:ℝ)) ≤ (30667); norm_num
  · show ((30667:ℝ)) ≤ (30697); norm_num
  · show ((30697:ℝ)) ≤ (30727); norm_num
  · show ((30727:ℝ)) ≤ (30758); norm_num
  · show ((30758:ℝ)) ≤ (30788); norm_num
  · show ((30788:ℝ)) ≤ (30818); norm_num
  · show ((30818:ℝ)) ≤ (30848); norm_num
  · show ((30848:ℝ)) ≤ (30879); norm_num
  · show ((30879:ℝ)) ≤ (30909); norm_num
  · show ((30909:ℝ)) ≤ (30939); norm_num
  · show ((30939:ℝ)) ≤ (30970); norm_num
  · show ((30970:ℝ)) ≤ (31000); norm_num
  · show ((31000:ℝ)) ≤ (31000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 30000
  | 1 => 30030
  | 2 => 30061
  | 3 => 120363 / 4
  | 4 => 30121
  | 5 => 30152
  | 6 => 30182
  | 7 => 30212
  | 8 => 30242
  | 9 => 30273
  | 10 => 30303
  | 11 => 30333
  | 12 => 30364
  | 13 => 30394
  | 14 => 30424
  | 15 => 30455
  | 16 => 30485
  | 17 => 30515
  | 18 => 30545
  | 19 => 30576
  | 20 => 30606
  | 21 => 122543 / 4
  | 22 => 30667
  | 23 => 30697
  | 24 => 30727
  | 25 => 30758
  | 26 => 30788
  | 27 => 30818
  | 28 => 30848
  | 29 => 30879
  | 30 => 123635 / 4
  | 31 => 30939
  | 32 => 30970
  | _ => 30970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 120121 / 4
  | 1 => 30061
  | 2 => 30091
  | 3 => 30121
  | 4 => 30152
  | 5 => 30182
  | 6 => 30212
  | 7 => 30242
  | 8 => 30273
  | 9 => 121213 / 4
  | 10 => 30333
  | 11 => 30364
  | 12 => 30394
  | 13 => 30424
  | 14 => 30455
  | 15 => 30485
  | 16 => 30515
  | 17 => 30545
  | 18 => 30576
  | 19 => 30606
  | 20 => 30636
  | 21 => 122669 / 4
  | 22 => 30697
  | 23 => 30727
  | 24 => 30758
  | 25 => 123153 / 4
  | 26 => 30818
  | 27 => 30848
  | 28 => 30879
  | 29 => 30909
  | 30 => 30939
  | 31 => 30970
  | 32 => 31000
  | _ => 31000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 31000` (`log 31000 ≤ 11`, `2.7^11 ≥ 31000`). -/
theorem haC_31000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 31000 := by
  have hlog : Real.log 31000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 31000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 31000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[30000, 31000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[30000, 31000]` SEGMENT: every zero with `30000 ≤ Im ≤ 31000` is on the line. -/
theorem segment_30000_31000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 31000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (30000:ℝ) ≤ ρ.im → ρ.im ≤ 31000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 30000 31000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_31000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 31000 via the HEIGHT CHAIN**: `[0,30000]` ∘ `[30000,31000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_31000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 31000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 31000 → ρ.re = 1 / 2 := by
  have hγ30000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 30000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 30000 31000
    (AllZeros_h30000.all_nontrivial_zeros_up_to_height_30000_of_bands
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
      hγ30000)
    (segment_30000_31000 hbands hγ)

end AllZeros_h31000
