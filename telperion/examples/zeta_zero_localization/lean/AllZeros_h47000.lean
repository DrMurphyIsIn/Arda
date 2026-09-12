/-  Height-chain step: all nontrivial zeta zeros up to height 47000 on Re = 1/2 --
    `AllZeros_h46000` + a `[46000, 47000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h46000
import RHInBoxT_1d4000000_3999999d4000000_46000_46029
import RHInBoxT_1d4000000_3999999d4000000_184115d4_46059
import RHInBoxT_1d4000000_3999999d4000000_46059_184353d4
import RHInBoxT_1d4000000_3999999d4000000_46088_184473d4
import RHInBoxT_1d4000000_3999999d4000000_46118_92295d2
import RHInBoxT_1d4000000_3999999d4000000_46147_46176
import RHInBoxT_1d4000000_3999999d4000000_46176_184825d4
import RHInBoxT_1d4000000_3999999d4000000_46206_46235
import RHInBoxT_1d4000000_3999999d4000000_184939d4_46265
import RHInBoxT_1d4000000_3999999d4000000_185059d4_46294
import RHInBoxT_1d4000000_3999999d4000000_46294_46324
import RHInBoxT_1d4000000_3999999d4000000_46324_46353
import RHInBoxT_1d4000000_3999999d4000000_46353_46382
import RHInBoxT_1d4000000_3999999d4000000_46382_46412
import RHInBoxT_1d4000000_3999999d4000000_185647d4_46441
import RHInBoxT_1d4000000_3999999d4000000_185763d4_46471
import RHInBoxT_1d4000000_3999999d4000000_46471_46500
import RHInBoxT_1d4000000_3999999d4000000_46500_46529
import RHInBoxT_1d4000000_3999999d4000000_186115d4_46559
import RHInBoxT_1d4000000_3999999d4000000_46559_186353d4
import RHInBoxT_1d4000000_3999999d4000000_46588_46618
import RHInBoxT_1d4000000_3999999d4000000_46618_46647
import RHInBoxT_1d4000000_3999999d4000000_46647_186705d4
import RHInBoxT_1d4000000_3999999d4000000_46676_46706
import RHInBoxT_1d4000000_3999999d4000000_46706_46735
import RHInBoxT_1d4000000_3999999d4000000_46735_187061d4
import RHInBoxT_1d4000000_3999999d4000000_46765_46794
import RHInBoxT_1d4000000_3999999d4000000_46794_46824
import RHInBoxT_1d4000000_3999999d4000000_46824_46853
import RHInBoxT_1d4000000_3999999d4000000_93705d2_46882
import RHInBoxT_1d4000000_3999999d4000000_187527d4_46912
import RHInBoxT_1d4000000_3999999d4000000_187647d4_46941
import RHInBoxT_1d4000000_3999999d4000000_46941_46971
import RHInBoxT_1d4000000_3999999d4000000_46971_47000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h47000

/-- The 34-band NOMINAL partition of `[46000, 47000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 46000
  | 1 => 46029
  | 2 => 46059
  | 3 => 46088
  | 4 => 46118
  | 5 => 46147
  | 6 => 46176
  | 7 => 46206
  | 8 => 46235
  | 9 => 46265
  | 10 => 46294
  | 11 => 46324
  | 12 => 46353
  | 13 => 46382
  | 14 => 46412
  | 15 => 46441
  | 16 => 46471
  | 17 => 46500
  | 18 => 46529
  | 19 => 46559
  | 20 => 46588
  | 21 => 46618
  | 22 => 46647
  | 23 => 46676
  | 24 => 46706
  | 25 => 46735
  | 26 => 46765
  | 27 => 46794
  | 28 => 46824
  | 29 => 46853
  | 30 => 46882
  | 31 => 46912
  | 32 => 46941
  | 33 => 46971
  | 34 => 47000
  | _ => 47000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((46000:ℝ)) ≤ (46029); norm_num
  · show ((46029:ℝ)) ≤ (46059); norm_num
  · show ((46059:ℝ)) ≤ (46088); norm_num
  · show ((46088:ℝ)) ≤ (46118); norm_num
  · show ((46118:ℝ)) ≤ (46147); norm_num
  · show ((46147:ℝ)) ≤ (46176); norm_num
  · show ((46176:ℝ)) ≤ (46206); norm_num
  · show ((46206:ℝ)) ≤ (46235); norm_num
  · show ((46235:ℝ)) ≤ (46265); norm_num
  · show ((46265:ℝ)) ≤ (46294); norm_num
  · show ((46294:ℝ)) ≤ (46324); norm_num
  · show ((46324:ℝ)) ≤ (46353); norm_num
  · show ((46353:ℝ)) ≤ (46382); norm_num
  · show ((46382:ℝ)) ≤ (46412); norm_num
  · show ((46412:ℝ)) ≤ (46441); norm_num
  · show ((46441:ℝ)) ≤ (46471); norm_num
  · show ((46471:ℝ)) ≤ (46500); norm_num
  · show ((46500:ℝ)) ≤ (46529); norm_num
  · show ((46529:ℝ)) ≤ (46559); norm_num
  · show ((46559:ℝ)) ≤ (46588); norm_num
  · show ((46588:ℝ)) ≤ (46618); norm_num
  · show ((46618:ℝ)) ≤ (46647); norm_num
  · show ((46647:ℝ)) ≤ (46676); norm_num
  · show ((46676:ℝ)) ≤ (46706); norm_num
  · show ((46706:ℝ)) ≤ (46735); norm_num
  · show ((46735:ℝ)) ≤ (46765); norm_num
  · show ((46765:ℝ)) ≤ (46794); norm_num
  · show ((46794:ℝ)) ≤ (46824); norm_num
  · show ((46824:ℝ)) ≤ (46853); norm_num
  · show ((46853:ℝ)) ≤ (46882); norm_num
  · show ((46882:ℝ)) ≤ (46912); norm_num
  · show ((46912:ℝ)) ≤ (46941); norm_num
  · show ((46941:ℝ)) ≤ (46971); norm_num
  · show ((46971:ℝ)) ≤ (47000); norm_num
  · show ((47000:ℝ)) ≤ (47000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 46000
  | 1 => 184115 / 4
  | 2 => 46059
  | 3 => 46088
  | 4 => 46118
  | 5 => 46147
  | 6 => 46176
  | 7 => 46206
  | 8 => 184939 / 4
  | 9 => 185059 / 4
  | 10 => 46294
  | 11 => 46324
  | 12 => 46353
  | 13 => 46382
  | 14 => 185647 / 4
  | 15 => 185763 / 4
  | 16 => 46471
  | 17 => 46500
  | 18 => 186115 / 4
  | 19 => 46559
  | 20 => 46588
  | 21 => 46618
  | 22 => 46647
  | 23 => 46676
  | 24 => 46706
  | 25 => 46735
  | 26 => 46765
  | 27 => 46794
  | 28 => 46824
  | 29 => 93705 / 2
  | 30 => 187527 / 4
  | 31 => 187647 / 4
  | 32 => 46941
  | 33 => 46971
  | _ => 46971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 46029
  | 1 => 46059
  | 2 => 184353 / 4
  | 3 => 184473 / 4
  | 4 => 92295 / 2
  | 5 => 46176
  | 6 => 184825 / 4
  | 7 => 46235
  | 8 => 46265
  | 9 => 46294
  | 10 => 46324
  | 11 => 46353
  | 12 => 46382
  | 13 => 46412
  | 14 => 46441
  | 15 => 46471
  | 16 => 46500
  | 17 => 46529
  | 18 => 46559
  | 19 => 186353 / 4
  | 20 => 46618
  | 21 => 46647
  | 22 => 186705 / 4
  | 23 => 46706
  | 24 => 46735
  | 25 => 187061 / 4
  | 26 => 46794
  | 27 => 46824
  | 28 => 46853
  | 29 => 46882
  | 30 => 46912
  | 31 => 46941
  | 32 => 46971
  | 33 => 47000
  | _ => 47000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 47000` (`log 47000 ≤ 11`, `2.7^11 ≥ 47000`). -/
theorem haC_47000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 47000 := by
  have hlog : Real.log 47000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 47000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 47000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[46000, 47000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[46000, 47000]` SEGMENT: every zero with `46000 ≤ Im ≤ 47000` is on the line. -/
theorem segment_46000_47000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 47000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (46000:ℝ) ≤ ρ.im → ρ.im ≤ 47000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 46000 47000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_47000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 47000 via the HEIGHT CHAIN**: `[0,46000]` ∘ `[46000,47000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_47000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 47000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 47000 → ρ.re = 1 / 2 := by
  have hγ46000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 46000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 46000 47000
    (AllZeros_h46000.all_nontrivial_zeros_up_to_height_46000_of_bands
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
      hγ46000)
    (segment_46000_47000 hbands hγ)

end AllZeros_h47000
