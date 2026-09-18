/-  Height-chain step: all nontrivial zeta zeros up to height 69000 on Re = 1/2 --
    `AllZeros_h68000` + a `[68000, 69000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h68000
import RHInBoxT_1d4000000_3999999d4000000_68000_272117d4
import RHInBoxT_1d4000000_3999999d4000000_68029_68057
import RHInBoxT_1d4000000_3999999d4000000_272227d4_68086
import RHInBoxT_1d4000000_3999999d4000000_68086_68114
import RHInBoxT_1d4000000_3999999d4000000_68114_68143
import RHInBoxT_1d4000000_3999999d4000000_68143_68171
import RHInBoxT_1d4000000_3999999d4000000_68171_272801d4
import RHInBoxT_1d4000000_3999999d4000000_68200_68229
import RHInBoxT_1d4000000_3999999d4000000_68229_68257
import RHInBoxT_1d4000000_3999999d4000000_68257_68286
import RHInBoxT_1d4000000_3999999d4000000_68286_68314
import RHInBoxT_1d4000000_3999999d4000000_273255d4_68343
import RHInBoxT_1d4000000_3999999d4000000_68343_68371
import RHInBoxT_1d4000000_3999999d4000000_68371_68400
import RHInBoxT_1d4000000_3999999d4000000_68400_68429
import RHInBoxT_1d4000000_3999999d4000000_68429_68457
import RHInBoxT_1d4000000_3999999d4000000_68457_68486
import RHInBoxT_1d4000000_3999999d4000000_68486_68514
import RHInBoxT_1d4000000_3999999d4000000_68514_68543
import RHInBoxT_1d4000000_3999999d4000000_68543_68571
import RHInBoxT_1d4000000_3999999d4000000_68571_68600
import RHInBoxT_1d4000000_3999999d4000000_68600_274517d4
import RHInBoxT_1d4000000_3999999d4000000_68629_68657
import RHInBoxT_1d4000000_3999999d4000000_68657_68686
import RHInBoxT_1d4000000_3999999d4000000_274743d4_274857d4
import RHInBoxT_1d4000000_3999999d4000000_68714_68743
import RHInBoxT_1d4000000_3999999d4000000_274971d4_68771
import RHInBoxT_1d4000000_3999999d4000000_68771_68800
import RHInBoxT_1d4000000_3999999d4000000_68800_68829
import RHInBoxT_1d4000000_3999999d4000000_275315d4_68857
import RHInBoxT_1d4000000_3999999d4000000_68857_68886
import RHInBoxT_1d4000000_3999999d4000000_275543d4_68914
import RHInBoxT_1d4000000_3999999d4000000_68914_68943
import RHInBoxT_1d4000000_3999999d4000000_68943_68971
import RHInBoxT_1d4000000_3999999d4000000_68971_69000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h69000

/-- The 35-band NOMINAL partition of `[68000, 69000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 68000
  | 1 => 68029
  | 2 => 68057
  | 3 => 68086
  | 4 => 68114
  | 5 => 68143
  | 6 => 68171
  | 7 => 68200
  | 8 => 68229
  | 9 => 68257
  | 10 => 68286
  | 11 => 68314
  | 12 => 68343
  | 13 => 68371
  | 14 => 68400
  | 15 => 68429
  | 16 => 68457
  | 17 => 68486
  | 18 => 68514
  | 19 => 68543
  | 20 => 68571
  | 21 => 68600
  | 22 => 68629
  | 23 => 68657
  | 24 => 68686
  | 25 => 68714
  | 26 => 68743
  | 27 => 68771
  | 28 => 68800
  | 29 => 68829
  | 30 => 68857
  | 31 => 68886
  | 32 => 68914
  | 33 => 68943
  | 34 => 68971
  | 35 => 69000
  | _ => 69000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((68000:ℝ)) ≤ (68029); norm_num
  · show ((68029:ℝ)) ≤ (68057); norm_num
  · show ((68057:ℝ)) ≤ (68086); norm_num
  · show ((68086:ℝ)) ≤ (68114); norm_num
  · show ((68114:ℝ)) ≤ (68143); norm_num
  · show ((68143:ℝ)) ≤ (68171); norm_num
  · show ((68171:ℝ)) ≤ (68200); norm_num
  · show ((68200:ℝ)) ≤ (68229); norm_num
  · show ((68229:ℝ)) ≤ (68257); norm_num
  · show ((68257:ℝ)) ≤ (68286); norm_num
  · show ((68286:ℝ)) ≤ (68314); norm_num
  · show ((68314:ℝ)) ≤ (68343); norm_num
  · show ((68343:ℝ)) ≤ (68371); norm_num
  · show ((68371:ℝ)) ≤ (68400); norm_num
  · show ((68400:ℝ)) ≤ (68429); norm_num
  · show ((68429:ℝ)) ≤ (68457); norm_num
  · show ((68457:ℝ)) ≤ (68486); norm_num
  · show ((68486:ℝ)) ≤ (68514); norm_num
  · show ((68514:ℝ)) ≤ (68543); norm_num
  · show ((68543:ℝ)) ≤ (68571); norm_num
  · show ((68571:ℝ)) ≤ (68600); norm_num
  · show ((68600:ℝ)) ≤ (68629); norm_num
  · show ((68629:ℝ)) ≤ (68657); norm_num
  · show ((68657:ℝ)) ≤ (68686); norm_num
  · show ((68686:ℝ)) ≤ (68714); norm_num
  · show ((68714:ℝ)) ≤ (68743); norm_num
  · show ((68743:ℝ)) ≤ (68771); norm_num
  · show ((68771:ℝ)) ≤ (68800); norm_num
  · show ((68800:ℝ)) ≤ (68829); norm_num
  · show ((68829:ℝ)) ≤ (68857); norm_num
  · show ((68857:ℝ)) ≤ (68886); norm_num
  · show ((68886:ℝ)) ≤ (68914); norm_num
  · show ((68914:ℝ)) ≤ (68943); norm_num
  · show ((68943:ℝ)) ≤ (68971); norm_num
  · show ((68971:ℝ)) ≤ (69000); norm_num
  · show ((69000:ℝ)) ≤ (69000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 68000
  | 1 => 68029
  | 2 => 272227 / 4
  | 3 => 68086
  | 4 => 68114
  | 5 => 68143
  | 6 => 68171
  | 7 => 68200
  | 8 => 68229
  | 9 => 68257
  | 10 => 68286
  | 11 => 273255 / 4
  | 12 => 68343
  | 13 => 68371
  | 14 => 68400
  | 15 => 68429
  | 16 => 68457
  | 17 => 68486
  | 18 => 68514
  | 19 => 68543
  | 20 => 68571
  | 21 => 68600
  | 22 => 68629
  | 23 => 68657
  | 24 => 274743 / 4
  | 25 => 68714
  | 26 => 274971 / 4
  | 27 => 68771
  | 28 => 68800
  | 29 => 275315 / 4
  | 30 => 68857
  | 31 => 275543 / 4
  | 32 => 68914
  | 33 => 68943
  | 34 => 68971
  | _ => 68971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 272117 / 4
  | 1 => 68057
  | 2 => 68086
  | 3 => 68114
  | 4 => 68143
  | 5 => 68171
  | 6 => 272801 / 4
  | 7 => 68229
  | 8 => 68257
  | 9 => 68286
  | 10 => 68314
  | 11 => 68343
  | 12 => 68371
  | 13 => 68400
  | 14 => 68429
  | 15 => 68457
  | 16 => 68486
  | 17 => 68514
  | 18 => 68543
  | 19 => 68571
  | 20 => 68600
  | 21 => 274517 / 4
  | 22 => 68657
  | 23 => 68686
  | 24 => 274857 / 4
  | 25 => 68743
  | 26 => 68771
  | 27 => 68800
  | 28 => 68829
  | 29 => 68857
  | 30 => 68886
  | 31 => 68914
  | 32 => 68943
  | 33 => 68971
  | 34 => 69000
  | _ => 69000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 69000` (`log 69000 ≤ 12`, `2.7^12 ≥ 69000`). -/
theorem haC_69000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 69000 := by
  have hlog : Real.log 69000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 69000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 69000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[68000, 69000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[68000, 69000]` SEGMENT: every zero with `68000 ≤ Im ≤ 69000` is on the line. -/
theorem segment_68000_69000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 69000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (68000:ℝ) ≤ ρ.im → ρ.im ≤ 69000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 68000 69000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_69000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 69000 via the HEIGHT CHAIN**: `[0,68000]` ∘ `[68000,69000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_69000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 69000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 69000 → ρ.re = 1 / 2 := by
  have hγ68000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 68000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 68000 69000
    (AllZeros_h68000.all_nontrivial_zeros_up_to_height_68000_of_bands
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
      hγ68000)
    (segment_68000_69000 hbands hγ)

end AllZeros_h69000
