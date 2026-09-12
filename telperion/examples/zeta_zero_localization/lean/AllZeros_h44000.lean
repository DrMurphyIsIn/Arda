/-  Height-chain step: all nontrivial zeta zeros up to height 44000 on Re = 1/2 --
    `AllZeros_h43000` + a `[43000, 44000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h43000
import RHInBoxT_1d4000000_3999999d4000000_43000_43029
import RHInBoxT_1d4000000_3999999d4000000_86057d2_43059
import RHInBoxT_1d4000000_3999999d4000000_43059_43088
import RHInBoxT_1d4000000_3999999d4000000_43088_43118
import RHInBoxT_1d4000000_3999999d4000000_43118_43147
import RHInBoxT_1d4000000_3999999d4000000_172587d4_43176
import RHInBoxT_1d4000000_3999999d4000000_43176_43206
import RHInBoxT_1d4000000_3999999d4000000_172823d4_43235
import RHInBoxT_1d4000000_3999999d4000000_43235_43265
import RHInBoxT_1d4000000_3999999d4000000_43265_173177d4
import RHInBoxT_1d4000000_3999999d4000000_43294_43324
import RHInBoxT_1d4000000_3999999d4000000_43324_43353
import RHInBoxT_1d4000000_3999999d4000000_43353_173529d4
import RHInBoxT_1d4000000_3999999d4000000_43382_43412
import RHInBoxT_1d4000000_3999999d4000000_43412_43441
import RHInBoxT_1d4000000_3999999d4000000_43441_43471
import RHInBoxT_1d4000000_3999999d4000000_43471_43500
import RHInBoxT_1d4000000_3999999d4000000_43500_43529
import RHInBoxT_1d4000000_3999999d4000000_43529_43559
import RHInBoxT_1d4000000_3999999d4000000_43559_43588
import RHInBoxT_1d4000000_3999999d4000000_43588_43618
import RHInBoxT_1d4000000_3999999d4000000_43618_43647
import RHInBoxT_1d4000000_3999999d4000000_43647_43676
import RHInBoxT_1d4000000_3999999d4000000_43676_43706
import RHInBoxT_1d4000000_3999999d4000000_43706_43735
import RHInBoxT_1d4000000_3999999d4000000_174939d4_43765
import RHInBoxT_1d4000000_3999999d4000000_43765_43794
import RHInBoxT_1d4000000_3999999d4000000_43794_175297d4
import RHInBoxT_1d4000000_3999999d4000000_43824_43853
import RHInBoxT_1d4000000_3999999d4000000_43853_43882
import RHInBoxT_1d4000000_3999999d4000000_43882_43912
import RHInBoxT_1d4000000_3999999d4000000_43912_43941
import RHInBoxT_1d4000000_3999999d4000000_175763d4_43971
import RHInBoxT_1d4000000_3999999d4000000_43971_44000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h44000

/-- The 34-band NOMINAL partition of `[43000, 44000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 43000
  | 1 => 43029
  | 2 => 43059
  | 3 => 43088
  | 4 => 43118
  | 5 => 43147
  | 6 => 43176
  | 7 => 43206
  | 8 => 43235
  | 9 => 43265
  | 10 => 43294
  | 11 => 43324
  | 12 => 43353
  | 13 => 43382
  | 14 => 43412
  | 15 => 43441
  | 16 => 43471
  | 17 => 43500
  | 18 => 43529
  | 19 => 43559
  | 20 => 43588
  | 21 => 43618
  | 22 => 43647
  | 23 => 43676
  | 24 => 43706
  | 25 => 43735
  | 26 => 43765
  | 27 => 43794
  | 28 => 43824
  | 29 => 43853
  | 30 => 43882
  | 31 => 43912
  | 32 => 43941
  | 33 => 43971
  | 34 => 44000
  | _ => 44000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((43000:ℝ)) ≤ (43029); norm_num
  · show ((43029:ℝ)) ≤ (43059); norm_num
  · show ((43059:ℝ)) ≤ (43088); norm_num
  · show ((43088:ℝ)) ≤ (43118); norm_num
  · show ((43118:ℝ)) ≤ (43147); norm_num
  · show ((43147:ℝ)) ≤ (43176); norm_num
  · show ((43176:ℝ)) ≤ (43206); norm_num
  · show ((43206:ℝ)) ≤ (43235); norm_num
  · show ((43235:ℝ)) ≤ (43265); norm_num
  · show ((43265:ℝ)) ≤ (43294); norm_num
  · show ((43294:ℝ)) ≤ (43324); norm_num
  · show ((43324:ℝ)) ≤ (43353); norm_num
  · show ((43353:ℝ)) ≤ (43382); norm_num
  · show ((43382:ℝ)) ≤ (43412); norm_num
  · show ((43412:ℝ)) ≤ (43441); norm_num
  · show ((43441:ℝ)) ≤ (43471); norm_num
  · show ((43471:ℝ)) ≤ (43500); norm_num
  · show ((43500:ℝ)) ≤ (43529); norm_num
  · show ((43529:ℝ)) ≤ (43559); norm_num
  · show ((43559:ℝ)) ≤ (43588); norm_num
  · show ((43588:ℝ)) ≤ (43618); norm_num
  · show ((43618:ℝ)) ≤ (43647); norm_num
  · show ((43647:ℝ)) ≤ (43676); norm_num
  · show ((43676:ℝ)) ≤ (43706); norm_num
  · show ((43706:ℝ)) ≤ (43735); norm_num
  · show ((43735:ℝ)) ≤ (43765); norm_num
  · show ((43765:ℝ)) ≤ (43794); norm_num
  · show ((43794:ℝ)) ≤ (43824); norm_num
  · show ((43824:ℝ)) ≤ (43853); norm_num
  · show ((43853:ℝ)) ≤ (43882); norm_num
  · show ((43882:ℝ)) ≤ (43912); norm_num
  · show ((43912:ℝ)) ≤ (43941); norm_num
  · show ((43941:ℝ)) ≤ (43971); norm_num
  · show ((43971:ℝ)) ≤ (44000); norm_num
  · show ((44000:ℝ)) ≤ (44000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 43000
  | 1 => 86057 / 2
  | 2 => 43059
  | 3 => 43088
  | 4 => 43118
  | 5 => 172587 / 4
  | 6 => 43176
  | 7 => 172823 / 4
  | 8 => 43235
  | 9 => 43265
  | 10 => 43294
  | 11 => 43324
  | 12 => 43353
  | 13 => 43382
  | 14 => 43412
  | 15 => 43441
  | 16 => 43471
  | 17 => 43500
  | 18 => 43529
  | 19 => 43559
  | 20 => 43588
  | 21 => 43618
  | 22 => 43647
  | 23 => 43676
  | 24 => 43706
  | 25 => 174939 / 4
  | 26 => 43765
  | 27 => 43794
  | 28 => 43824
  | 29 => 43853
  | 30 => 43882
  | 31 => 43912
  | 32 => 175763 / 4
  | 33 => 43971
  | _ => 43971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 43029
  | 1 => 43059
  | 2 => 43088
  | 3 => 43118
  | 4 => 43147
  | 5 => 43176
  | 6 => 43206
  | 7 => 43235
  | 8 => 43265
  | 9 => 173177 / 4
  | 10 => 43324
  | 11 => 43353
  | 12 => 173529 / 4
  | 13 => 43412
  | 14 => 43441
  | 15 => 43471
  | 16 => 43500
  | 17 => 43529
  | 18 => 43559
  | 19 => 43588
  | 20 => 43618
  | 21 => 43647
  | 22 => 43676
  | 23 => 43706
  | 24 => 43735
  | 25 => 43765
  | 26 => 43794
  | 27 => 175297 / 4
  | 28 => 43853
  | 29 => 43882
  | 30 => 43912
  | 31 => 43941
  | 32 => 43971
  | 33 => 44000
  | _ => 44000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 44000` (`log 44000 ≤ 11`, `2.7^11 ≥ 44000`). -/
theorem haC_44000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 44000 := by
  have hlog : Real.log 44000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 44000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 44000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[43000, 44000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[43000, 44000]` SEGMENT: every zero with `43000 ≤ Im ≤ 44000` is on the line. -/
theorem segment_43000_44000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 44000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (43000:ℝ) ≤ ρ.im → ρ.im ≤ 44000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 43000 44000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_44000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 44000 via the HEIGHT CHAIN**: `[0,43000]` ∘ `[43000,44000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_44000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 44000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 44000 → ρ.re = 1 / 2 := by
  have hγ43000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 43000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 43000 44000
    (AllZeros_h43000.all_nontrivial_zeros_up_to_height_43000_of_bands
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
      hγ43000)
    (segment_43000_44000 hbands hγ)

end AllZeros_h44000
