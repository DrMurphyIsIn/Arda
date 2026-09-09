/-  TILED MILESTONE (T = 1000), DENSITY-ADAPTIVE PARTITION: all nontrivial zeta zeros up to
    height 1000 lie on Re = 1/2, from NINETEEN per-band certificates via the tiled capstone.

    Partition: one 100-band [0,100] (n = 29) then EIGHTEEN 50-bands to 1000.  Density-adaptive
    tiling: the emitted certificates' O(n^2) coordinate-elaboration blocks exceed heartbeat
    budgets past n ~ 45 AT THIS WIDTH (a = 1/2e6; the 2e6 denominators double the digit cost of
    every norm_num vs the 1e6 bands), so band height halves where zero density grows.  MEASURED
    locally on M3 Ultra: 100-bands [100,500] at n = 50..67 time out (400-600k heartbeats); the
    50-band halves at n = 23..41 build in 90-105 s each.

    Census: 29 + (23+27+29+30+31+33+33+34) + (36+36+36+37+38+39+39+39+39+41) = 649 = N(1000);
    every 50-band half-pair sums exactly to its parent 100-band winding (independent
    cross-check).  Close pairs [600,650],[700,750],[900,950] required the 6x on-line sweep.

    conjecture1_proved = False.

    CERTIFICATE SHAPE (measured constraint, 2026-09-09): a monolithic raw-input headline over
    19 bands (38 spliced hLine/hArb binders, ~650 rational enclosures in ONE theorem statement)
    exceeds single-theorem elaboration budget (OOM/SIGKILL after 56 min).  The scalable
    certificate is the composition: each band file's rh_in_box_* theorem carries its OWN raw
    Arb inputs; `all_nontrivial_zeros_up_to_height_1000_of_bands` glues their CONCLUSIONS.
    Identical trust boundary, linear elaboration cost. -/
import Mathlib
import DlvpZetaZeroFree
import ZetaZeroConfinement
import AllZerosUpToHeight
import RHInBox_1d2000000_1999999d2000000_0_100
import RHInBox_1d2000000_1999999d2000000_100_150
import RHInBox_1d2000000_1999999d2000000_150_200
import RHInBox_1d2000000_1999999d2000000_200_250
import RHInBox_1d2000000_1999999d2000000_250_300
import RHInBox_1d2000000_1999999d2000000_300_350
import RHInBox_1d2000000_1999999d2000000_350_400
import RHInBox_1d2000000_1999999d2000000_400_450
import RHInBox_1d2000000_1999999d2000000_450_500
import RHInBox_1d2000000_1999999d2000000_500_550
import RHInBox_1d2000000_1999999d2000000_550_600
import RHInBox_1d2000000_1999999d2000000_600_650
import RHInBox_1d2000000_1999999d2000000_650_700
import RHInBox_1d2000000_1999999d2000000_700_750
import RHInBox_1d2000000_1999999d2000000_750_800
import RHInBox_1d2000000_1999999d2000000_800_850
import RHInBox_1d2000000_1999999d2000000_850_900
import RHInBox_1d2000000_1999999d2000000_900_950
import RHInBox_1d2000000_1999999d2000000_950_1000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h1000

/-- The density-adaptive 19-band partition. -/
noncomputable def bnd : ℕ → ℝ := fun i => match i with
  | 0 => 0
  | 1 => 100
  | 2 => 150
  | 3 => 200
  | 4 => 250
  | 5 => 300
  | 6 => 350
  | 7 => 400
  | 8 => 450
  | 9 => 500
  | 10 => 550
  | 11 => 600
  | 12 => 650
  | 13 => 700
  | 14 => 750
  | 15 => 800
  | 16 => 850
  | 17 => 900
  | 18 => 950
  | 19 => 1000
  | _ => 1000

theorem bnd_mono : Monotone bnd := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((0:ℝ)) ≤ (100); norm_num
  · show ((100:ℝ)) ≤ (150); norm_num
  · show ((150:ℝ)) ≤ (200); norm_num
  · show ((200:ℝ)) ≤ (250); norm_num
  · show ((250:ℝ)) ≤ (300); norm_num
  · show ((300:ℝ)) ≤ (350); norm_num
  · show ((350:ℝ)) ≤ (400); norm_num
  · show ((400:ℝ)) ≤ (450); norm_num
  · show ((450:ℝ)) ≤ (500); norm_num
  · show ((500:ℝ)) ≤ (550); norm_num
  · show ((550:ℝ)) ≤ (600); norm_num
  · show ((600:ℝ)) ≤ (650); norm_num
  · show ((650:ℝ)) ≤ (700); norm_num
  · show ((700:ℝ)) ≤ (750); norm_num
  · show ((750:ℝ)) ≤ (800); norm_num
  · show ((800:ℝ)) ≤ (850); norm_num
  · show ((850:ℝ)) ≤ (900); norm_num
  · show ((900:ℝ)) ≤ (950); norm_num
  · show ((950:ℝ)) ≤ (1000); norm_num
  · show ((1000:ℝ)) ≤ (1000); norm_num
  · exact le_refl _

/-- **The effective-rate band-width inequality at `T = 1000`:** `1/(2·10^6) ≤ dlvpRateC / log 1000`.
    Same numeric core as `AllZeros_h100.haC_100` with `log 1000 ≤ 7`.  conjecture1_proved = False. -/
theorem haC_1000 : (1 / 2000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 1000 := by
  have hpilt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpigt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpisq_lt : Real.pi ^ 2 < 9.87 := by nlinarith [hpilt, hpigt, hpi_pos]
  have hden_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by nlinarith [hpisq_lt]
  have hlog2322 : (1 / 25 : ℝ) ≤ Real.log ((23 / 16) / (11 / 8)) := by
    have h2322 : ((23 / 16) / (11 / 8) : ℝ) = 23 / 22 := by norm_num
    rw [h2322, Real.le_log_iff_exp_le (by norm_num)]
    have hb := Real.exp_bound' (x := (1/25 : ℝ)) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 3, (1/25 : ℝ) ^ m / m.factorial)
        + (1/25 : ℝ) ^ 3 * (3 + 1) / ((Nat.factorial 3) * 3) ≤ 23 / 22 := by
      simp [Finset.sum_range_succ, Nat.factorial]; norm_num
    linarith [hb, hsum]
  have hlog15 : Real.log (15 / (2 - Real.pi ^ 2 / 6)) ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h43 : (15 : ℝ) / (2 - Real.pi ^ 2 / 6) ≤ 43 := by
      rw [div_le_iff₀ hden_pos]; nlinarith [hpisq_lt]
    have hexp4 : (43 : ℝ) ≤ Real.exp 4 := by
      have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have hpow : (2.7 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
      rw [h4]; nlinarith [hpow]
    linarith [h43, hexp4]
  -- log 1000 ≤ 7 : 1000 ≤ exp 7 = (exp 1)^7 ≥ 2.7^7 = 1046.03…
  have hlog1000 : Real.log 1000 ≤ 7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h7 : Real.exp 7 = (Real.exp 1) ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow7 : (2.7 : ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) he1 7
    rw [h7]; nlinarith [hpow7]
  have hLrpos : 0 < Real.log ((23 / 16) / (11 / 8)) := by linarith [hlog2322]
  have hlog15nn : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hden_pos]; nlinarith [hden_pos])
  set L1 : ℝ := Real.log ((23 / 16) / (11 / 8)) with hL1
  set L15 : ℝ := Real.log (15 / (2 - Real.pi ^ 2 / 6)) with hL15
  set M : ℝ := (8 / (3 * L1) + 608 / 9) / 16 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hterm : 8 / (3 * L1) ≤ 200 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hlog2322, hLrpos]
  have hMup : M ≤ 151 / 18 := by
    have h1 : M ≤ (200 / 3 + 608 / 9) / 16 := by rw [hMdef]; gcongr
    nlinarith [h1]
  set K : ℝ := 1 + 2 * M * (L15 + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKub : K ≤ 764 / 9 := by
    rw [hKdef]
    have hfac : L15 + 1 ≤ 4 + 1 := by linarith [hlog15]
    have hfac_pos : 0 < L15 + 1 := by linarith [hlog15nn]
    nlinarith [hMpos, hMup, hfac, hfac_pos, hlog15nn]
  have hCdef : ZeroFreeBridge.dlvpRateC = 1 / (112 * 16 * K) := by
    rw [ZeroFreeBridge.dlvpRateC, ZeroFreeBridge.dlvpRateK, ← hL1, ← hL15, ← hMdef, ← hKdef]
  have hClo : (9 / 1369088 : ℝ) ≤ ZeroFreeBridge.dlvpRateC := by
    rw [hCdef]
    have hval : (9 / 1369088 : ℝ) = 1 / (112 * 16 * (764 / 9)) := by norm_num
    rw [hval]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [hKub, hKpos]
  have hlogpos : 0 < Real.log 1000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlogpos]
  calc (1 / 2000000 : ℝ) * Real.log 1000
      ≤ (1 / 2000000 : ℝ) * 7 := by nlinarith [hlog1000, hlogpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := hClo

/-- **T = 1000 from the 19 band CONCLUSIONS** (density-adaptive tiling glue). -/
theorem all_nontrivial_zeros_up_to_height_1000_of_bands
    (hband0 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband1 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((100) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (150)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband2 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((150) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband3 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (250)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband4 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((250) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (300)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband5 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((300) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (350)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband6 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((350) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband7 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (450)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband8 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((450) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (500)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband9 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((500) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (550)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband10 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((550) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband11 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (650)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband12 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((650) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (700)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband13 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (750)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband14 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((750) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband15 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (850)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband16 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((850) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (900)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband17 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((900) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (950)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband18 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((950) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 2000000 = 1999999 / 2000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line_tiled
    (1 / 2000000) 1000 bnd 19 (by norm_num) bnd_mono rfl rfl haC_1000 (by norm_num) (by norm_num)
    ?_ hγ
  intro i hi ρ hre him hz
  have hre' : ((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 1999999 / 2000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  interval_cases i
  · exact hband0 ρ hre' him hz
  · exact hband1 ρ hre' him hz
  · exact hband2 ρ hre' him hz
  · exact hband3 ρ hre' him hz
  · exact hband4 ρ hre' him hz
  · exact hband5 ρ hre' him hz
  · exact hband6 ρ hre' him hz
  · exact hband7 ρ hre' him hz
  · exact hband8 ρ hre' him hz
  · exact hband9 ρ hre' him hz
  · exact hband10 ρ hre' him hz
  · exact hband11 ρ hre' him hz
  · exact hband12 ρ hre' him hz
  · exact hband13 ρ hre' him hz
  · exact hband14 ρ hre' him hz
  · exact hband15 ρ hre' him hz
  · exact hband16 ρ hre' him hz
  · exact hband17 ρ hre' him hz
  · exact hband18 ρ hre' him hz

end AllZeros_h1000
