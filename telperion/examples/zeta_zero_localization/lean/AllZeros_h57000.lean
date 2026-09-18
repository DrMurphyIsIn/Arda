/-  Height-chain step: all nontrivial zeta zeros up to height 57000 on Re = 1/2 --
    `AllZeros_h56000` + a `[56000, 57000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h56000
import RHInBoxT_1d4000000_3999999d4000000_223999d4_56029
import RHInBoxT_1d4000000_3999999d4000000_56029_56057
import RHInBoxT_1d4000000_3999999d4000000_56057_224345d4
import RHInBoxT_1d4000000_3999999d4000000_56086_56114
import RHInBoxT_1d4000000_3999999d4000000_56114_56143
import RHInBoxT_1d4000000_3999999d4000000_56143_56171
import RHInBoxT_1d4000000_3999999d4000000_224683d4_56200
import RHInBoxT_1d4000000_3999999d4000000_56200_56229
import RHInBoxT_1d4000000_3999999d4000000_56229_56257
import RHInBoxT_1d4000000_3999999d4000000_225027d4_56286
import RHInBoxT_1d4000000_3999999d4000000_56286_56314
import RHInBoxT_1d4000000_3999999d4000000_56314_56343
import RHInBoxT_1d4000000_3999999d4000000_56343_225485d4
import RHInBoxT_1d4000000_3999999d4000000_56371_56400
import RHInBoxT_1d4000000_3999999d4000000_225599d4_56429
import RHInBoxT_1d4000000_3999999d4000000_56429_56457
import RHInBoxT_1d4000000_3999999d4000000_56457_56486
import RHInBoxT_1d4000000_3999999d4000000_56486_56514
import RHInBoxT_1d4000000_3999999d4000000_56514_56543
import RHInBoxT_1d4000000_3999999d4000000_226171d4_56571
import RHInBoxT_1d4000000_3999999d4000000_56571_56600
import RHInBoxT_1d4000000_3999999d4000000_56600_56629
import RHInBoxT_1d4000000_3999999d4000000_56629_56657
import RHInBoxT_1d4000000_3999999d4000000_56657_56686
import RHInBoxT_1d4000000_3999999d4000000_56686_56714
import RHInBoxT_1d4000000_3999999d4000000_56714_56743
import RHInBoxT_1d4000000_3999999d4000000_226971d4_56771
import RHInBoxT_1d4000000_3999999d4000000_56771_56800
import RHInBoxT_1d4000000_3999999d4000000_56800_56829
import RHInBoxT_1d4000000_3999999d4000000_56829_227429d4
import RHInBoxT_1d4000000_3999999d4000000_56857_56886
import RHInBoxT_1d4000000_3999999d4000000_56886_56914
import RHInBoxT_1d4000000_3999999d4000000_56914_56943
import RHInBoxT_1d4000000_3999999d4000000_56943_56971
import RHInBoxT_1d4000000_3999999d4000000_56971_57000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h57000

/-- The 35-band NOMINAL partition of `[56000, 57000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 56000
  | 1 => 56029
  | 2 => 56057
  | 3 => 56086
  | 4 => 56114
  | 5 => 56143
  | 6 => 56171
  | 7 => 56200
  | 8 => 56229
  | 9 => 56257
  | 10 => 56286
  | 11 => 56314
  | 12 => 56343
  | 13 => 56371
  | 14 => 56400
  | 15 => 56429
  | 16 => 56457
  | 17 => 56486
  | 18 => 56514
  | 19 => 56543
  | 20 => 56571
  | 21 => 56600
  | 22 => 56629
  | 23 => 56657
  | 24 => 56686
  | 25 => 56714
  | 26 => 56743
  | 27 => 56771
  | 28 => 56800
  | 29 => 56829
  | 30 => 56857
  | 31 => 56886
  | 32 => 56914
  | 33 => 56943
  | 34 => 56971
  | 35 => 57000
  | _ => 57000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((56000:ℝ)) ≤ (56029); norm_num
  · show ((56029:ℝ)) ≤ (56057); norm_num
  · show ((56057:ℝ)) ≤ (56086); norm_num
  · show ((56086:ℝ)) ≤ (56114); norm_num
  · show ((56114:ℝ)) ≤ (56143); norm_num
  · show ((56143:ℝ)) ≤ (56171); norm_num
  · show ((56171:ℝ)) ≤ (56200); norm_num
  · show ((56200:ℝ)) ≤ (56229); norm_num
  · show ((56229:ℝ)) ≤ (56257); norm_num
  · show ((56257:ℝ)) ≤ (56286); norm_num
  · show ((56286:ℝ)) ≤ (56314); norm_num
  · show ((56314:ℝ)) ≤ (56343); norm_num
  · show ((56343:ℝ)) ≤ (56371); norm_num
  · show ((56371:ℝ)) ≤ (56400); norm_num
  · show ((56400:ℝ)) ≤ (56429); norm_num
  · show ((56429:ℝ)) ≤ (56457); norm_num
  · show ((56457:ℝ)) ≤ (56486); norm_num
  · show ((56486:ℝ)) ≤ (56514); norm_num
  · show ((56514:ℝ)) ≤ (56543); norm_num
  · show ((56543:ℝ)) ≤ (56571); norm_num
  · show ((56571:ℝ)) ≤ (56600); norm_num
  · show ((56600:ℝ)) ≤ (56629); norm_num
  · show ((56629:ℝ)) ≤ (56657); norm_num
  · show ((56657:ℝ)) ≤ (56686); norm_num
  · show ((56686:ℝ)) ≤ (56714); norm_num
  · show ((56714:ℝ)) ≤ (56743); norm_num
  · show ((56743:ℝ)) ≤ (56771); norm_num
  · show ((56771:ℝ)) ≤ (56800); norm_num
  · show ((56800:ℝ)) ≤ (56829); norm_num
  · show ((56829:ℝ)) ≤ (56857); norm_num
  · show ((56857:ℝ)) ≤ (56886); norm_num
  · show ((56886:ℝ)) ≤ (56914); norm_num
  · show ((56914:ℝ)) ≤ (56943); norm_num
  · show ((56943:ℝ)) ≤ (56971); norm_num
  · show ((56971:ℝ)) ≤ (57000); norm_num
  · show ((57000:ℝ)) ≤ (57000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 223999 / 4
  | 1 => 56029
  | 2 => 56057
  | 3 => 56086
  | 4 => 56114
  | 5 => 56143
  | 6 => 224683 / 4
  | 7 => 56200
  | 8 => 56229
  | 9 => 225027 / 4
  | 10 => 56286
  | 11 => 56314
  | 12 => 56343
  | 13 => 56371
  | 14 => 225599 / 4
  | 15 => 56429
  | 16 => 56457
  | 17 => 56486
  | 18 => 56514
  | 19 => 226171 / 4
  | 20 => 56571
  | 21 => 56600
  | 22 => 56629
  | 23 => 56657
  | 24 => 56686
  | 25 => 56714
  | 26 => 226971 / 4
  | 27 => 56771
  | 28 => 56800
  | 29 => 56829
  | 30 => 56857
  | 31 => 56886
  | 32 => 56914
  | 33 => 56943
  | 34 => 56971
  | _ => 56971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 56029
  | 1 => 56057
  | 2 => 224345 / 4
  | 3 => 56114
  | 4 => 56143
  | 5 => 56171
  | 6 => 56200
  | 7 => 56229
  | 8 => 56257
  | 9 => 56286
  | 10 => 56314
  | 11 => 56343
  | 12 => 225485 / 4
  | 13 => 56400
  | 14 => 56429
  | 15 => 56457
  | 16 => 56486
  | 17 => 56514
  | 18 => 56543
  | 19 => 56571
  | 20 => 56600
  | 21 => 56629
  | 22 => 56657
  | 23 => 56686
  | 24 => 56714
  | 25 => 56743
  | 26 => 56771
  | 27 => 56800
  | 28 => 56829
  | 29 => 227429 / 4
  | 30 => 56886
  | 31 => 56914
  | 32 => 56943
  | 33 => 56971
  | 34 => 57000
  | _ => 57000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 57000` (`log 57000 ≤ 12`, `2.7^12 ≥ 57000`). -/
theorem haC_57000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 57000 := by
  have hlog : Real.log 57000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 57000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 57000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[56000, 57000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[56000, 57000]` SEGMENT: every zero with `56000 ≤ Im ≤ 57000` is on the line. -/
theorem segment_56000_57000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 57000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (56000:ℝ) ≤ ρ.im → ρ.im ≤ 57000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 56000 57000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_57000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 57000 via the HEIGHT CHAIN**: `[0,56000]` ∘ `[56000,57000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_57000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 57000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 57000 → ρ.re = 1 / 2 := by
  have hγ56000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 56000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 56000 57000
    (AllZeros_h56000.all_nontrivial_zeros_up_to_height_56000_of_bands
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
      hγ56000)
    (segment_56000_57000 hbands hγ)

end AllZeros_h57000
