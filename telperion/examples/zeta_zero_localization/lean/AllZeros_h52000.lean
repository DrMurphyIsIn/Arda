/-  Height-chain step: all nontrivial zeta zeros up to height 52000 on Re = 1/2 --
    `AllZeros_h51000` + a `[51000, 52000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h51000
import RHInBoxT_1d4000000_3999999d4000000_203999d4_204117d4
import RHInBoxT_1d4000000_3999999d4000000_51029_51059
import RHInBoxT_1d4000000_3999999d4000000_51059_51088
import RHInBoxT_1d4000000_3999999d4000000_51088_51118
import RHInBoxT_1d4000000_3999999d4000000_51118_51147
import RHInBoxT_1d4000000_3999999d4000000_51147_51176
import RHInBoxT_1d4000000_3999999d4000000_51176_204825d4
import RHInBoxT_1d4000000_3999999d4000000_51206_51235
import RHInBoxT_1d4000000_3999999d4000000_51235_51265
import RHInBoxT_1d4000000_3999999d4000000_51265_51294
import RHInBoxT_1d4000000_3999999d4000000_51294_205297d4
import RHInBoxT_1d4000000_3999999d4000000_51324_51353
import RHInBoxT_1d4000000_3999999d4000000_51353_51382
import RHInBoxT_1d4000000_3999999d4000000_51382_51412
import RHInBoxT_1d4000000_3999999d4000000_205647d4_51441
import RHInBoxT_1d4000000_3999999d4000000_51441_51471
import RHInBoxT_1d4000000_3999999d4000000_51471_51500
import RHInBoxT_1d4000000_3999999d4000000_51500_206117d4
import RHInBoxT_1d4000000_3999999d4000000_51529_51559
import RHInBoxT_1d4000000_3999999d4000000_51559_51588
import RHInBoxT_1d4000000_3999999d4000000_51588_51618
import RHInBoxT_1d4000000_3999999d4000000_51618_51647
import RHInBoxT_1d4000000_3999999d4000000_206587d4_51676
import RHInBoxT_1d4000000_3999999d4000000_51676_51706
import RHInBoxT_1d4000000_3999999d4000000_51706_51735
import RHInBoxT_1d4000000_3999999d4000000_51735_51765
import RHInBoxT_1d4000000_3999999d4000000_51765_51794
import RHInBoxT_1d4000000_3999999d4000000_51794_51824
import RHInBoxT_1d4000000_3999999d4000000_51824_51853
import RHInBoxT_1d4000000_3999999d4000000_51853_51882
import RHInBoxT_1d4000000_3999999d4000000_51882_51912
import RHInBoxT_1d4000000_3999999d4000000_51912_51941
import RHInBoxT_1d4000000_3999999d4000000_51941_51971
import RHInBoxT_1d4000000_3999999d4000000_51971_52000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h52000

/-- The 34-band NOMINAL partition of `[51000, 52000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 51000
  | 1 => 51029
  | 2 => 51059
  | 3 => 51088
  | 4 => 51118
  | 5 => 51147
  | 6 => 51176
  | 7 => 51206
  | 8 => 51235
  | 9 => 51265
  | 10 => 51294
  | 11 => 51324
  | 12 => 51353
  | 13 => 51382
  | 14 => 51412
  | 15 => 51441
  | 16 => 51471
  | 17 => 51500
  | 18 => 51529
  | 19 => 51559
  | 20 => 51588
  | 21 => 51618
  | 22 => 51647
  | 23 => 51676
  | 24 => 51706
  | 25 => 51735
  | 26 => 51765
  | 27 => 51794
  | 28 => 51824
  | 29 => 51853
  | 30 => 51882
  | 31 => 51912
  | 32 => 51941
  | 33 => 51971
  | 34 => 52000
  | _ => 52000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((51000:ℝ)) ≤ (51029); norm_num
  · show ((51029:ℝ)) ≤ (51059); norm_num
  · show ((51059:ℝ)) ≤ (51088); norm_num
  · show ((51088:ℝ)) ≤ (51118); norm_num
  · show ((51118:ℝ)) ≤ (51147); norm_num
  · show ((51147:ℝ)) ≤ (51176); norm_num
  · show ((51176:ℝ)) ≤ (51206); norm_num
  · show ((51206:ℝ)) ≤ (51235); norm_num
  · show ((51235:ℝ)) ≤ (51265); norm_num
  · show ((51265:ℝ)) ≤ (51294); norm_num
  · show ((51294:ℝ)) ≤ (51324); norm_num
  · show ((51324:ℝ)) ≤ (51353); norm_num
  · show ((51353:ℝ)) ≤ (51382); norm_num
  · show ((51382:ℝ)) ≤ (51412); norm_num
  · show ((51412:ℝ)) ≤ (51441); norm_num
  · show ((51441:ℝ)) ≤ (51471); norm_num
  · show ((51471:ℝ)) ≤ (51500); norm_num
  · show ((51500:ℝ)) ≤ (51529); norm_num
  · show ((51529:ℝ)) ≤ (51559); norm_num
  · show ((51559:ℝ)) ≤ (51588); norm_num
  · show ((51588:ℝ)) ≤ (51618); norm_num
  · show ((51618:ℝ)) ≤ (51647); norm_num
  · show ((51647:ℝ)) ≤ (51676); norm_num
  · show ((51676:ℝ)) ≤ (51706); norm_num
  · show ((51706:ℝ)) ≤ (51735); norm_num
  · show ((51735:ℝ)) ≤ (51765); norm_num
  · show ((51765:ℝ)) ≤ (51794); norm_num
  · show ((51794:ℝ)) ≤ (51824); norm_num
  · show ((51824:ℝ)) ≤ (51853); norm_num
  · show ((51853:ℝ)) ≤ (51882); norm_num
  · show ((51882:ℝ)) ≤ (51912); norm_num
  · show ((51912:ℝ)) ≤ (51941); norm_num
  · show ((51941:ℝ)) ≤ (51971); norm_num
  · show ((51971:ℝ)) ≤ (52000); norm_num
  · show ((52000:ℝ)) ≤ (52000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 203999 / 4
  | 1 => 51029
  | 2 => 51059
  | 3 => 51088
  | 4 => 51118
  | 5 => 51147
  | 6 => 51176
  | 7 => 51206
  | 8 => 51235
  | 9 => 51265
  | 10 => 51294
  | 11 => 51324
  | 12 => 51353
  | 13 => 51382
  | 14 => 205647 / 4
  | 15 => 51441
  | 16 => 51471
  | 17 => 51500
  | 18 => 51529
  | 19 => 51559
  | 20 => 51588
  | 21 => 51618
  | 22 => 206587 / 4
  | 23 => 51676
  | 24 => 51706
  | 25 => 51735
  | 26 => 51765
  | 27 => 51794
  | 28 => 51824
  | 29 => 51853
  | 30 => 51882
  | 31 => 51912
  | 32 => 51941
  | 33 => 51971
  | _ => 51971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 204117 / 4
  | 1 => 51059
  | 2 => 51088
  | 3 => 51118
  | 4 => 51147
  | 5 => 51176
  | 6 => 204825 / 4
  | 7 => 51235
  | 8 => 51265
  | 9 => 51294
  | 10 => 205297 / 4
  | 11 => 51353
  | 12 => 51382
  | 13 => 51412
  | 14 => 51441
  | 15 => 51471
  | 16 => 51500
  | 17 => 206117 / 4
  | 18 => 51559
  | 19 => 51588
  | 20 => 51618
  | 21 => 51647
  | 22 => 51676
  | 23 => 51706
  | 24 => 51735
  | 25 => 51765
  | 26 => 51794
  | 27 => 51824
  | 28 => 51853
  | 29 => 51882
  | 30 => 51912
  | 31 => 51941
  | 32 => 51971
  | 33 => 52000
  | _ => 52000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 52000` (`log 52000 ≤ 11`, `2.7^11 ≥ 52000`). -/
theorem haC_52000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 52000 := by
  have hlog : Real.log 52000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 52000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 52000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[51000, 52000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[51000, 52000]` SEGMENT: every zero with `51000 ≤ Im ≤ 52000` is on the line. -/
theorem segment_51000_52000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 52000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (51000:ℝ) ≤ ρ.im → ρ.im ≤ 52000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 51000 52000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_52000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 52000 via the HEIGHT CHAIN**: `[0,51000]` ∘ `[51000,52000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_52000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 52000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 52000 → ρ.re = 1 / 2 := by
  have hγ51000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 51000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 51000 52000
    (AllZeros_h51000.all_nontrivial_zeros_up_to_height_51000_of_bands
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
      hγ51000)
    (segment_51000_52000 hbands hγ)

end AllZeros_h52000
