/-  Height-chain step: all nontrivial zeta zeros up to height 50000 on Re = 1/2 --
    `AllZeros_h49000` + a `[49000, 50000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h49000
import RHInBoxT_1d4000000_3999999d4000000_49000_49029
import RHInBoxT_1d4000000_3999999d4000000_49029_49059
import RHInBoxT_1d4000000_3999999d4000000_49059_49088
import RHInBoxT_1d4000000_3999999d4000000_49088_49118
import RHInBoxT_1d4000000_3999999d4000000_49118_49147
import RHInBoxT_1d4000000_3999999d4000000_49147_49176
import RHInBoxT_1d4000000_3999999d4000000_49176_49206
import RHInBoxT_1d4000000_3999999d4000000_49206_196941d4
import RHInBoxT_1d4000000_3999999d4000000_49235_49265
import RHInBoxT_1d4000000_3999999d4000000_49265_49294
import RHInBoxT_1d4000000_3999999d4000000_49294_49324
import RHInBoxT_1d4000000_3999999d4000000_49324_49353
import RHInBoxT_1d4000000_3999999d4000000_49353_49382
import RHInBoxT_1d4000000_3999999d4000000_49382_49412
import RHInBoxT_1d4000000_3999999d4000000_49412_49441
import RHInBoxT_1d4000000_3999999d4000000_49441_49471
import RHInBoxT_1d4000000_3999999d4000000_49471_49500
import RHInBoxT_1d4000000_3999999d4000000_49500_49529
import RHInBoxT_1d4000000_3999999d4000000_49529_49559
import RHInBoxT_1d4000000_3999999d4000000_198235d4_49588
import RHInBoxT_1d4000000_3999999d4000000_49588_49618
import RHInBoxT_1d4000000_3999999d4000000_49618_49647
import RHInBoxT_1d4000000_3999999d4000000_49647_49676
import RHInBoxT_1d4000000_3999999d4000000_49676_49706
import RHInBoxT_1d4000000_3999999d4000000_49706_49735
import RHInBoxT_1d4000000_3999999d4000000_49735_49765
import RHInBoxT_1d4000000_3999999d4000000_49765_49794
import RHInBoxT_1d4000000_3999999d4000000_49794_49824
import RHInBoxT_1d4000000_3999999d4000000_199295d4_199413d4
import RHInBoxT_1d4000000_3999999d4000000_49853_49882
import RHInBoxT_1d4000000_3999999d4000000_49882_49912
import RHInBoxT_1d4000000_3999999d4000000_49912_49941
import RHInBoxT_1d4000000_3999999d4000000_49941_49971
import RHInBoxT_1d4000000_3999999d4000000_49971_50000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h50000

/-- The 34-band NOMINAL partition of `[49000, 50000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 49000
  | 1 => 49029
  | 2 => 49059
  | 3 => 49088
  | 4 => 49118
  | 5 => 49147
  | 6 => 49176
  | 7 => 49206
  | 8 => 49235
  | 9 => 49265
  | 10 => 49294
  | 11 => 49324
  | 12 => 49353
  | 13 => 49382
  | 14 => 49412
  | 15 => 49441
  | 16 => 49471
  | 17 => 49500
  | 18 => 49529
  | 19 => 49559
  | 20 => 49588
  | 21 => 49618
  | 22 => 49647
  | 23 => 49676
  | 24 => 49706
  | 25 => 49735
  | 26 => 49765
  | 27 => 49794
  | 28 => 49824
  | 29 => 49853
  | 30 => 49882
  | 31 => 49912
  | 32 => 49941
  | 33 => 49971
  | 34 => 50000
  | _ => 50000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((49000:ℝ)) ≤ (49029); norm_num
  · show ((49029:ℝ)) ≤ (49059); norm_num
  · show ((49059:ℝ)) ≤ (49088); norm_num
  · show ((49088:ℝ)) ≤ (49118); norm_num
  · show ((49118:ℝ)) ≤ (49147); norm_num
  · show ((49147:ℝ)) ≤ (49176); norm_num
  · show ((49176:ℝ)) ≤ (49206); norm_num
  · show ((49206:ℝ)) ≤ (49235); norm_num
  · show ((49235:ℝ)) ≤ (49265); norm_num
  · show ((49265:ℝ)) ≤ (49294); norm_num
  · show ((49294:ℝ)) ≤ (49324); norm_num
  · show ((49324:ℝ)) ≤ (49353); norm_num
  · show ((49353:ℝ)) ≤ (49382); norm_num
  · show ((49382:ℝ)) ≤ (49412); norm_num
  · show ((49412:ℝ)) ≤ (49441); norm_num
  · show ((49441:ℝ)) ≤ (49471); norm_num
  · show ((49471:ℝ)) ≤ (49500); norm_num
  · show ((49500:ℝ)) ≤ (49529); norm_num
  · show ((49529:ℝ)) ≤ (49559); norm_num
  · show ((49559:ℝ)) ≤ (49588); norm_num
  · show ((49588:ℝ)) ≤ (49618); norm_num
  · show ((49618:ℝ)) ≤ (49647); norm_num
  · show ((49647:ℝ)) ≤ (49676); norm_num
  · show ((49676:ℝ)) ≤ (49706); norm_num
  · show ((49706:ℝ)) ≤ (49735); norm_num
  · show ((49735:ℝ)) ≤ (49765); norm_num
  · show ((49765:ℝ)) ≤ (49794); norm_num
  · show ((49794:ℝ)) ≤ (49824); norm_num
  · show ((49824:ℝ)) ≤ (49853); norm_num
  · show ((49853:ℝ)) ≤ (49882); norm_num
  · show ((49882:ℝ)) ≤ (49912); norm_num
  · show ((49912:ℝ)) ≤ (49941); norm_num
  · show ((49941:ℝ)) ≤ (49971); norm_num
  · show ((49971:ℝ)) ≤ (50000); norm_num
  · show ((50000:ℝ)) ≤ (50000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 49000
  | 1 => 49029
  | 2 => 49059
  | 3 => 49088
  | 4 => 49118
  | 5 => 49147
  | 6 => 49176
  | 7 => 49206
  | 8 => 49235
  | 9 => 49265
  | 10 => 49294
  | 11 => 49324
  | 12 => 49353
  | 13 => 49382
  | 14 => 49412
  | 15 => 49441
  | 16 => 49471
  | 17 => 49500
  | 18 => 49529
  | 19 => 198235 / 4
  | 20 => 49588
  | 21 => 49618
  | 22 => 49647
  | 23 => 49676
  | 24 => 49706
  | 25 => 49735
  | 26 => 49765
  | 27 => 49794
  | 28 => 199295 / 4
  | 29 => 49853
  | 30 => 49882
  | 31 => 49912
  | 32 => 49941
  | 33 => 49971
  | _ => 49971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 49029
  | 1 => 49059
  | 2 => 49088
  | 3 => 49118
  | 4 => 49147
  | 5 => 49176
  | 6 => 49206
  | 7 => 196941 / 4
  | 8 => 49265
  | 9 => 49294
  | 10 => 49324
  | 11 => 49353
  | 12 => 49382
  | 13 => 49412
  | 14 => 49441
  | 15 => 49471
  | 16 => 49500
  | 17 => 49529
  | 18 => 49559
  | 19 => 49588
  | 20 => 49618
  | 21 => 49647
  | 22 => 49676
  | 23 => 49706
  | 24 => 49735
  | 25 => 49765
  | 26 => 49794
  | 27 => 49824
  | 28 => 199413 / 4
  | 29 => 49882
  | 30 => 49912
  | 31 => 49941
  | 32 => 49971
  | 33 => 50000
  | _ => 50000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 50000` (`log 50000 ≤ 11`, `2.7^11 ≥ 50000`). -/
theorem haC_50000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 50000 := by
  have hlog : Real.log 50000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 50000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 50000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[49000, 50000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[49000, 50000]` SEGMENT: every zero with `49000 ≤ Im ≤ 50000` is on the line. -/
theorem segment_49000_50000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 50000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (49000:ℝ) ≤ ρ.im → ρ.im ≤ 50000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 49000 50000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_50000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 50000 via the HEIGHT CHAIN**: `[0,49000]` ∘ `[49000,50000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_50000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 50000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 50000 → ρ.re = 1 / 2 := by
  have hγ49000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 49000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 49000 50000
    (AllZeros_h49000.all_nontrivial_zeros_up_to_height_49000_of_bands
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
      hγ49000)
    (segment_49000_50000 hbands hγ)

end AllZeros_h50000
