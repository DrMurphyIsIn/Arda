/-  Height-chain step: all nontrivial zeta zeros up to height 64000 on Re = 1/2 --
    `AllZeros_h63000` + a `[63000, 64000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h63000
import RHInBoxT_1d4000000_3999999d4000000_251999d4_63029
import RHInBoxT_1d4000000_3999999d4000000_63029_63057
import RHInBoxT_1d4000000_3999999d4000000_252227d4_63086
import RHInBoxT_1d4000000_3999999d4000000_63086_63114
import RHInBoxT_1d4000000_3999999d4000000_63114_63143
import RHInBoxT_1d4000000_3999999d4000000_252571d4_63171
import RHInBoxT_1d4000000_3999999d4000000_63171_63200
import RHInBoxT_1d4000000_3999999d4000000_63200_63229
import RHInBoxT_1d4000000_3999999d4000000_252915d4_63257
import RHInBoxT_1d4000000_3999999d4000000_253027d4_63286
import RHInBoxT_1d4000000_3999999d4000000_253143d4_63314
import RHInBoxT_1d4000000_3999999d4000000_253255d4_63343
import RHInBoxT_1d4000000_3999999d4000000_63343_63371
import RHInBoxT_1d4000000_3999999d4000000_63371_253601d4
import RHInBoxT_1d4000000_3999999d4000000_63400_63429
import RHInBoxT_1d4000000_3999999d4000000_63429_63457
import RHInBoxT_1d4000000_3999999d4000000_63457_63486
import RHInBoxT_1d4000000_3999999d4000000_63486_63514
import RHInBoxT_1d4000000_3999999d4000000_254055d4_63543
import RHInBoxT_1d4000000_3999999d4000000_63543_63571
import RHInBoxT_1d4000000_3999999d4000000_63571_63600
import RHInBoxT_1d4000000_3999999d4000000_254399d4_63629
import RHInBoxT_1d4000000_3999999d4000000_63629_63657
import RHInBoxT_1d4000000_3999999d4000000_63657_63686
import RHInBoxT_1d4000000_3999999d4000000_254743d4_63714
import RHInBoxT_1d4000000_3999999d4000000_63714_63743
import RHInBoxT_1d4000000_3999999d4000000_63743_63771
import RHInBoxT_1d4000000_3999999d4000000_63771_63800
import RHInBoxT_1d4000000_3999999d4000000_255199d4_63829
import RHInBoxT_1d4000000_3999999d4000000_255315d4_255429d4
import RHInBoxT_1d4000000_3999999d4000000_63857_63886
import RHInBoxT_1d4000000_3999999d4000000_63886_63914
import RHInBoxT_1d4000000_3999999d4000000_63914_63943
import RHInBoxT_1d4000000_3999999d4000000_63943_63971
import RHInBoxT_1d4000000_3999999d4000000_255883d4_64000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h64000

/-- The 35-band NOMINAL partition of `[63000, 64000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 63000
  | 1 => 63029
  | 2 => 63057
  | 3 => 63086
  | 4 => 63114
  | 5 => 63143
  | 6 => 63171
  | 7 => 63200
  | 8 => 63229
  | 9 => 63257
  | 10 => 63286
  | 11 => 63314
  | 12 => 63343
  | 13 => 63371
  | 14 => 63400
  | 15 => 63429
  | 16 => 63457
  | 17 => 63486
  | 18 => 63514
  | 19 => 63543
  | 20 => 63571
  | 21 => 63600
  | 22 => 63629
  | 23 => 63657
  | 24 => 63686
  | 25 => 63714
  | 26 => 63743
  | 27 => 63771
  | 28 => 63800
  | 29 => 63829
  | 30 => 63857
  | 31 => 63886
  | 32 => 63914
  | 33 => 63943
  | 34 => 63971
  | 35 => 64000
  | _ => 64000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((63000:ℝ)) ≤ (63029); norm_num
  · show ((63029:ℝ)) ≤ (63057); norm_num
  · show ((63057:ℝ)) ≤ (63086); norm_num
  · show ((63086:ℝ)) ≤ (63114); norm_num
  · show ((63114:ℝ)) ≤ (63143); norm_num
  · show ((63143:ℝ)) ≤ (63171); norm_num
  · show ((63171:ℝ)) ≤ (63200); norm_num
  · show ((63200:ℝ)) ≤ (63229); norm_num
  · show ((63229:ℝ)) ≤ (63257); norm_num
  · show ((63257:ℝ)) ≤ (63286); norm_num
  · show ((63286:ℝ)) ≤ (63314); norm_num
  · show ((63314:ℝ)) ≤ (63343); norm_num
  · show ((63343:ℝ)) ≤ (63371); norm_num
  · show ((63371:ℝ)) ≤ (63400); norm_num
  · show ((63400:ℝ)) ≤ (63429); norm_num
  · show ((63429:ℝ)) ≤ (63457); norm_num
  · show ((63457:ℝ)) ≤ (63486); norm_num
  · show ((63486:ℝ)) ≤ (63514); norm_num
  · show ((63514:ℝ)) ≤ (63543); norm_num
  · show ((63543:ℝ)) ≤ (63571); norm_num
  · show ((63571:ℝ)) ≤ (63600); norm_num
  · show ((63600:ℝ)) ≤ (63629); norm_num
  · show ((63629:ℝ)) ≤ (63657); norm_num
  · show ((63657:ℝ)) ≤ (63686); norm_num
  · show ((63686:ℝ)) ≤ (63714); norm_num
  · show ((63714:ℝ)) ≤ (63743); norm_num
  · show ((63743:ℝ)) ≤ (63771); norm_num
  · show ((63771:ℝ)) ≤ (63800); norm_num
  · show ((63800:ℝ)) ≤ (63829); norm_num
  · show ((63829:ℝ)) ≤ (63857); norm_num
  · show ((63857:ℝ)) ≤ (63886); norm_num
  · show ((63886:ℝ)) ≤ (63914); norm_num
  · show ((63914:ℝ)) ≤ (63943); norm_num
  · show ((63943:ℝ)) ≤ (63971); norm_num
  · show ((63971:ℝ)) ≤ (64000); norm_num
  · show ((64000:ℝ)) ≤ (64000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 251999 / 4
  | 1 => 63029
  | 2 => 252227 / 4
  | 3 => 63086
  | 4 => 63114
  | 5 => 252571 / 4
  | 6 => 63171
  | 7 => 63200
  | 8 => 252915 / 4
  | 9 => 253027 / 4
  | 10 => 253143 / 4
  | 11 => 253255 / 4
  | 12 => 63343
  | 13 => 63371
  | 14 => 63400
  | 15 => 63429
  | 16 => 63457
  | 17 => 63486
  | 18 => 254055 / 4
  | 19 => 63543
  | 20 => 63571
  | 21 => 254399 / 4
  | 22 => 63629
  | 23 => 63657
  | 24 => 254743 / 4
  | 25 => 63714
  | 26 => 63743
  | 27 => 63771
  | 28 => 255199 / 4
  | 29 => 255315 / 4
  | 30 => 63857
  | 31 => 63886
  | 32 => 63914
  | 33 => 63943
  | 34 => 255883 / 4
  | _ => 255883 / 4

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 63029
  | 1 => 63057
  | 2 => 63086
  | 3 => 63114
  | 4 => 63143
  | 5 => 63171
  | 6 => 63200
  | 7 => 63229
  | 8 => 63257
  | 9 => 63286
  | 10 => 63314
  | 11 => 63343
  | 12 => 63371
  | 13 => 253601 / 4
  | 14 => 63429
  | 15 => 63457
  | 16 => 63486
  | 17 => 63514
  | 18 => 63543
  | 19 => 63571
  | 20 => 63600
  | 21 => 63629
  | 22 => 63657
  | 23 => 63686
  | 24 => 63714
  | 25 => 63743
  | 26 => 63771
  | 27 => 63800
  | 28 => 63829
  | 29 => 255429 / 4
  | 30 => 63886
  | 31 => 63914
  | 32 => 63943
  | 33 => 63971
  | 34 => 64000
  | _ => 64000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 64000` (`log 64000 ≤ 12`, `2.7^12 ≥ 64000`). -/
theorem haC_64000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 64000 := by
  have hlog : Real.log 64000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 64000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 64000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[63000, 64000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[63000, 64000]` SEGMENT: every zero with `63000 ≤ Im ≤ 64000` is on the line. -/
theorem segment_63000_64000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 64000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (63000:ℝ) ≤ ρ.im → ρ.im ≤ 64000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 63000 64000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_64000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 64000 via the HEIGHT CHAIN**: `[0,63000]` ∘ `[63000,64000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_64000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 64000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 64000 → ρ.re = 1 / 2 := by
  have hγ63000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 63000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 63000 64000
    (AllZeros_h63000.all_nontrivial_zeros_up_to_height_63000_of_bands
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
      hγ63000)
    (segment_63000_64000 hbands hγ)

end AllZeros_h64000
