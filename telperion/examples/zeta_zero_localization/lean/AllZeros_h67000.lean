/-  Height-chain step: all nontrivial zeta zeros up to height 67000 on Re = 1/2 --
    `AllZeros_h66000` + a `[66000, 67000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h66000
import RHInBoxT_1d4000000_3999999d4000000_66000_66029
import RHInBoxT_1d4000000_3999999d4000000_66029_66057
import RHInBoxT_1d4000000_3999999d4000000_66057_66086
import RHInBoxT_1d4000000_3999999d4000000_66086_66114
import RHInBoxT_1d4000000_3999999d4000000_66114_66143
import RHInBoxT_1d4000000_3999999d4000000_264571d4_66171
import RHInBoxT_1d4000000_3999999d4000000_66171_66200
import RHInBoxT_1d4000000_3999999d4000000_66200_66229
import RHInBoxT_1d4000000_3999999d4000000_66229_66257
import RHInBoxT_1d4000000_3999999d4000000_66257_66286
import RHInBoxT_1d4000000_3999999d4000000_66286_66314
import RHInBoxT_1d4000000_3999999d4000000_66314_66343
import RHInBoxT_1d4000000_3999999d4000000_66343_66371
import RHInBoxT_1d4000000_3999999d4000000_66371_66400
import RHInBoxT_1d4000000_3999999d4000000_66400_66429
import RHInBoxT_1d4000000_3999999d4000000_66429_66457
import RHInBoxT_1d4000000_3999999d4000000_66457_265945d4
import RHInBoxT_1d4000000_3999999d4000000_66486_66514
import RHInBoxT_1d4000000_3999999d4000000_66514_66543
import RHInBoxT_1d4000000_3999999d4000000_66543_66571
import RHInBoxT_1d4000000_3999999d4000000_66571_66600
import RHInBoxT_1d4000000_3999999d4000000_66600_66629
import RHInBoxT_1d4000000_3999999d4000000_66629_66657
import RHInBoxT_1d4000000_3999999d4000000_66657_66686
import RHInBoxT_1d4000000_3999999d4000000_266743d4_266857d4
import RHInBoxT_1d4000000_3999999d4000000_66714_266973d4
import RHInBoxT_1d4000000_3999999d4000000_66743_66771
import RHInBoxT_1d4000000_3999999d4000000_66771_267201d4
import RHInBoxT_1d4000000_3999999d4000000_66800_66829
import RHInBoxT_1d4000000_3999999d4000000_66829_66857
import RHInBoxT_1d4000000_3999999d4000000_66857_66886
import RHInBoxT_1d4000000_3999999d4000000_66886_66914
import RHInBoxT_1d4000000_3999999d4000000_66914_66943
import RHInBoxT_1d4000000_3999999d4000000_66943_66971
import RHInBoxT_1d4000000_3999999d4000000_66971_67000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h67000

/-- The 35-band NOMINAL partition of `[66000, 67000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 66000
  | 1 => 66029
  | 2 => 66057
  | 3 => 66086
  | 4 => 66114
  | 5 => 66143
  | 6 => 66171
  | 7 => 66200
  | 8 => 66229
  | 9 => 66257
  | 10 => 66286
  | 11 => 66314
  | 12 => 66343
  | 13 => 66371
  | 14 => 66400
  | 15 => 66429
  | 16 => 66457
  | 17 => 66486
  | 18 => 66514
  | 19 => 66543
  | 20 => 66571
  | 21 => 66600
  | 22 => 66629
  | 23 => 66657
  | 24 => 66686
  | 25 => 66714
  | 26 => 66743
  | 27 => 66771
  | 28 => 66800
  | 29 => 66829
  | 30 => 66857
  | 31 => 66886
  | 32 => 66914
  | 33 => 66943
  | 34 => 66971
  | 35 => 67000
  | _ => 67000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((66000:ℝ)) ≤ (66029); norm_num
  · show ((66029:ℝ)) ≤ (66057); norm_num
  · show ((66057:ℝ)) ≤ (66086); norm_num
  · show ((66086:ℝ)) ≤ (66114); norm_num
  · show ((66114:ℝ)) ≤ (66143); norm_num
  · show ((66143:ℝ)) ≤ (66171); norm_num
  · show ((66171:ℝ)) ≤ (66200); norm_num
  · show ((66200:ℝ)) ≤ (66229); norm_num
  · show ((66229:ℝ)) ≤ (66257); norm_num
  · show ((66257:ℝ)) ≤ (66286); norm_num
  · show ((66286:ℝ)) ≤ (66314); norm_num
  · show ((66314:ℝ)) ≤ (66343); norm_num
  · show ((66343:ℝ)) ≤ (66371); norm_num
  · show ((66371:ℝ)) ≤ (66400); norm_num
  · show ((66400:ℝ)) ≤ (66429); norm_num
  · show ((66429:ℝ)) ≤ (66457); norm_num
  · show ((66457:ℝ)) ≤ (66486); norm_num
  · show ((66486:ℝ)) ≤ (66514); norm_num
  · show ((66514:ℝ)) ≤ (66543); norm_num
  · show ((66543:ℝ)) ≤ (66571); norm_num
  · show ((66571:ℝ)) ≤ (66600); norm_num
  · show ((66600:ℝ)) ≤ (66629); norm_num
  · show ((66629:ℝ)) ≤ (66657); norm_num
  · show ((66657:ℝ)) ≤ (66686); norm_num
  · show ((66686:ℝ)) ≤ (66714); norm_num
  · show ((66714:ℝ)) ≤ (66743); norm_num
  · show ((66743:ℝ)) ≤ (66771); norm_num
  · show ((66771:ℝ)) ≤ (66800); norm_num
  · show ((66800:ℝ)) ≤ (66829); norm_num
  · show ((66829:ℝ)) ≤ (66857); norm_num
  · show ((66857:ℝ)) ≤ (66886); norm_num
  · show ((66886:ℝ)) ≤ (66914); norm_num
  · show ((66914:ℝ)) ≤ (66943); norm_num
  · show ((66943:ℝ)) ≤ (66971); norm_num
  · show ((66971:ℝ)) ≤ (67000); norm_num
  · show ((67000:ℝ)) ≤ (67000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 66000
  | 1 => 66029
  | 2 => 66057
  | 3 => 66086
  | 4 => 66114
  | 5 => 264571 / 4
  | 6 => 66171
  | 7 => 66200
  | 8 => 66229
  | 9 => 66257
  | 10 => 66286
  | 11 => 66314
  | 12 => 66343
  | 13 => 66371
  | 14 => 66400
  | 15 => 66429
  | 16 => 66457
  | 17 => 66486
  | 18 => 66514
  | 19 => 66543
  | 20 => 66571
  | 21 => 66600
  | 22 => 66629
  | 23 => 66657
  | 24 => 266743 / 4
  | 25 => 66714
  | 26 => 66743
  | 27 => 66771
  | 28 => 66800
  | 29 => 66829
  | 30 => 66857
  | 31 => 66886
  | 32 => 66914
  | 33 => 66943
  | 34 => 66971
  | _ => 66971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 66029
  | 1 => 66057
  | 2 => 66086
  | 3 => 66114
  | 4 => 66143
  | 5 => 66171
  | 6 => 66200
  | 7 => 66229
  | 8 => 66257
  | 9 => 66286
  | 10 => 66314
  | 11 => 66343
  | 12 => 66371
  | 13 => 66400
  | 14 => 66429
  | 15 => 66457
  | 16 => 265945 / 4
  | 17 => 66514
  | 18 => 66543
  | 19 => 66571
  | 20 => 66600
  | 21 => 66629
  | 22 => 66657
  | 23 => 66686
  | 24 => 266857 / 4
  | 25 => 266973 / 4
  | 26 => 66771
  | 27 => 267201 / 4
  | 28 => 66829
  | 29 => 66857
  | 30 => 66886
  | 31 => 66914
  | 32 => 66943
  | 33 => 66971
  | 34 => 67000
  | _ => 67000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 67000` (`log 67000 ≤ 12`, `2.7^12 ≥ 67000`). -/
theorem haC_67000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 67000 := by
  have hlog : Real.log 67000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 67000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 67000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[66000, 67000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[66000, 67000]` SEGMENT: every zero with `66000 ≤ Im ≤ 67000` is on the line. -/
theorem segment_66000_67000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 67000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (66000:ℝ) ≤ ρ.im → ρ.im ≤ 67000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 66000 67000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_67000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 67000 via the HEIGHT CHAIN**: `[0,66000]` ∘ `[66000,67000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_67000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 67000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 67000 → ρ.re = 1 / 2 := by
  have hγ66000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 66000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 66000 67000
    (AllZeros_h66000.all_nontrivial_zeros_up_to_height_66000_of_bands
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
      hγ66000)
    (segment_66000_67000 hbands hγ)

end AllZeros_h67000
