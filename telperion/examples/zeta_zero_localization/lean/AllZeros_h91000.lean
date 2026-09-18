/-  Height-chain step: all nontrivial zeta zeros up to height 91000 on Re = 1/2 --
    `AllZeros_h90000` + a `[90000, 91000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h90000
import RHInBoxT_1d4000000_3999999d4000000_90000_90028
import RHInBoxT_1d4000000_3999999d4000000_360111d4_90056
import RHInBoxT_1d4000000_3999999d4000000_90056_90083
import RHInBoxT_1d4000000_3999999d4000000_90083_90111
import RHInBoxT_1d4000000_3999999d4000000_90111_90139
import RHInBoxT_1d4000000_3999999d4000000_90139_90167
import RHInBoxT_1d4000000_3999999d4000000_90167_90194
import RHInBoxT_1d4000000_3999999d4000000_90194_90222
import RHInBoxT_1d4000000_3999999d4000000_90222_90250
import RHInBoxT_1d4000000_3999999d4000000_90250_90278
import RHInBoxT_1d4000000_3999999d4000000_90278_90306
import RHInBoxT_1d4000000_3999999d4000000_90306_90333
import RHInBoxT_1d4000000_3999999d4000000_361331d4_90361
import RHInBoxT_1d4000000_3999999d4000000_361443d4_90389
import RHInBoxT_1d4000000_3999999d4000000_90389_90417
import RHInBoxT_1d4000000_3999999d4000000_90417_90444
import RHInBoxT_1d4000000_3999999d4000000_90444_90472
import RHInBoxT_1d4000000_3999999d4000000_90472_90500
import RHInBoxT_1d4000000_3999999d4000000_361999d4_90528
import RHInBoxT_1d4000000_3999999d4000000_90528_90556
import RHInBoxT_1d4000000_3999999d4000000_90556_362333d4
import RHInBoxT_1d4000000_3999999d4000000_90583_90611
import RHInBoxT_1d4000000_3999999d4000000_90611_90639
import RHInBoxT_1d4000000_3999999d4000000_90639_90667
import RHInBoxT_1d4000000_3999999d4000000_362667d4_90694
import RHInBoxT_1d4000000_3999999d4000000_90694_90722
import RHInBoxT_1d4000000_3999999d4000000_90722_363001d4
import RHInBoxT_1d4000000_3999999d4000000_90750_90778
import RHInBoxT_1d4000000_3999999d4000000_90778_90806
import RHInBoxT_1d4000000_3999999d4000000_90806_90833
import RHInBoxT_1d4000000_3999999d4000000_363331d4_90861
import RHInBoxT_1d4000000_3999999d4000000_90861_90889
import RHInBoxT_1d4000000_3999999d4000000_90889_90917
import RHInBoxT_1d4000000_3999999d4000000_90917_90944
import RHInBoxT_1d4000000_3999999d4000000_90944_90972
import RHInBoxT_1d4000000_3999999d4000000_90972_91000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h91000

/-- The 36-band NOMINAL partition of `[90000, 91000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 90000
  | 1 => 90028
  | 2 => 90056
  | 3 => 90083
  | 4 => 90111
  | 5 => 90139
  | 6 => 90167
  | 7 => 90194
  | 8 => 90222
  | 9 => 90250
  | 10 => 90278
  | 11 => 90306
  | 12 => 90333
  | 13 => 90361
  | 14 => 90389
  | 15 => 90417
  | 16 => 90444
  | 17 => 90472
  | 18 => 90500
  | 19 => 90528
  | 20 => 90556
  | 21 => 90583
  | 22 => 90611
  | 23 => 90639
  | 24 => 90667
  | 25 => 90694
  | 26 => 90722
  | 27 => 90750
  | 28 => 90778
  | 29 => 90806
  | 30 => 90833
  | 31 => 90861
  | 32 => 90889
  | 33 => 90917
  | 34 => 90944
  | 35 => 90972
  | 36 => 91000
  | _ => 91000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((90000:ℝ)) ≤ (90028); norm_num
  · show ((90028:ℝ)) ≤ (90056); norm_num
  · show ((90056:ℝ)) ≤ (90083); norm_num
  · show ((90083:ℝ)) ≤ (90111); norm_num
  · show ((90111:ℝ)) ≤ (90139); norm_num
  · show ((90139:ℝ)) ≤ (90167); norm_num
  · show ((90167:ℝ)) ≤ (90194); norm_num
  · show ((90194:ℝ)) ≤ (90222); norm_num
  · show ((90222:ℝ)) ≤ (90250); norm_num
  · show ((90250:ℝ)) ≤ (90278); norm_num
  · show ((90278:ℝ)) ≤ (90306); norm_num
  · show ((90306:ℝ)) ≤ (90333); norm_num
  · show ((90333:ℝ)) ≤ (90361); norm_num
  · show ((90361:ℝ)) ≤ (90389); norm_num
  · show ((90389:ℝ)) ≤ (90417); norm_num
  · show ((90417:ℝ)) ≤ (90444); norm_num
  · show ((90444:ℝ)) ≤ (90472); norm_num
  · show ((90472:ℝ)) ≤ (90500); norm_num
  · show ((90500:ℝ)) ≤ (90528); norm_num
  · show ((90528:ℝ)) ≤ (90556); norm_num
  · show ((90556:ℝ)) ≤ (90583); norm_num
  · show ((90583:ℝ)) ≤ (90611); norm_num
  · show ((90611:ℝ)) ≤ (90639); norm_num
  · show ((90639:ℝ)) ≤ (90667); norm_num
  · show ((90667:ℝ)) ≤ (90694); norm_num
  · show ((90694:ℝ)) ≤ (90722); norm_num
  · show ((90722:ℝ)) ≤ (90750); norm_num
  · show ((90750:ℝ)) ≤ (90778); norm_num
  · show ((90778:ℝ)) ≤ (90806); norm_num
  · show ((90806:ℝ)) ≤ (90833); norm_num
  · show ((90833:ℝ)) ≤ (90861); norm_num
  · show ((90861:ℝ)) ≤ (90889); norm_num
  · show ((90889:ℝ)) ≤ (90917); norm_num
  · show ((90917:ℝ)) ≤ (90944); norm_num
  · show ((90944:ℝ)) ≤ (90972); norm_num
  · show ((90972:ℝ)) ≤ (91000); norm_num
  · show ((91000:ℝ)) ≤ (91000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 90000
  | 1 => 360111 / 4
  | 2 => 90056
  | 3 => 90083
  | 4 => 90111
  | 5 => 90139
  | 6 => 90167
  | 7 => 90194
  | 8 => 90222
  | 9 => 90250
  | 10 => 90278
  | 11 => 90306
  | 12 => 361331 / 4
  | 13 => 361443 / 4
  | 14 => 90389
  | 15 => 90417
  | 16 => 90444
  | 17 => 90472
  | 18 => 361999 / 4
  | 19 => 90528
  | 20 => 90556
  | 21 => 90583
  | 22 => 90611
  | 23 => 90639
  | 24 => 362667 / 4
  | 25 => 90694
  | 26 => 90722
  | 27 => 90750
  | 28 => 90778
  | 29 => 90806
  | 30 => 363331 / 4
  | 31 => 90861
  | 32 => 90889
  | 33 => 90917
  | 34 => 90944
  | 35 => 90972
  | _ => 90972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 90028
  | 1 => 90056
  | 2 => 90083
  | 3 => 90111
  | 4 => 90139
  | 5 => 90167
  | 6 => 90194
  | 7 => 90222
  | 8 => 90250
  | 9 => 90278
  | 10 => 90306
  | 11 => 90333
  | 12 => 90361
  | 13 => 90389
  | 14 => 90417
  | 15 => 90444
  | 16 => 90472
  | 17 => 90500
  | 18 => 90528
  | 19 => 90556
  | 20 => 362333 / 4
  | 21 => 90611
  | 22 => 90639
  | 23 => 90667
  | 24 => 90694
  | 25 => 90722
  | 26 => 363001 / 4
  | 27 => 90778
  | 28 => 90806
  | 29 => 90833
  | 30 => 90861
  | 31 => 90889
  | 32 => 90917
  | 33 => 90944
  | 34 => 90972
  | 35 => 91000
  | _ => 91000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 91000` (`log 91000 ≤ 12`, `2.7^12 ≥ 91000`). -/
theorem haC_91000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 91000 := by
  have hlog : Real.log 91000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 91000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 91000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[90000, 91000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[90000, 91000]` SEGMENT: every zero with `90000 ≤ Im ≤ 91000` is on the line. -/
theorem segment_90000_91000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 91000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (90000:ℝ) ≤ ρ.im → ρ.im ≤ 91000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 90000 91000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_91000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 91000 via the HEIGHT CHAIN**: `[0,90000]` ∘ `[90000,91000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_91000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 91000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 91000 → ρ.re = 1 / 2 := by
  have hγ90000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 90000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 90000 91000
    (AllZeros_h90000.all_nontrivial_zeros_up_to_height_90000_of_bands
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
      hγ90000)
    (segment_90000_91000 hbands hγ)

end AllZeros_h91000
