/-  TILED MILESTONE (T = 2000): all nontrivial zeta zeros up to height 2000 lie on Re = 1/2,
    from THIRTY-NINE per-band certificates via the tiled capstone — 1517 zeros.

    Partition: the 19 bands of AllZeros_h1000 ([0,100] + 50-bands to 1000) + TWENTY fresh
    50-bands [1000,2000] (n = 40..46 each; five needed the 6x close-pair sweep: [1300,1350],
    [1400,1450], [1750,1800], [1850,1900], [1950,2000]).  Census: 649 + 868 = 1517 = N(2000);
    the [1000,2000] half-bands independently re-sum the earlier fat-band windings (868 = 868).

    `haC_2000` uses the SHARED rational bound `ZeroFreeBridge.dlvpRateC_lower` (9/1369088 ≤ c),
    so the height instantiation is one `log 2000 ≤ 8` estimate — the first consumer of the
    factored numeric core.  Certificate shape per the measured binder-budget law: per-band
    theorems carry raw Arb inputs; this file glues CONCLUSIONS only.
    conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
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
import RHInBox_1d2000000_1999999d2000000_1000_1050
import RHInBox_1d2000000_1999999d2000000_1050_1100
import RHInBox_1d2000000_1999999d2000000_1100_1150
import RHInBox_1d2000000_1999999d2000000_1150_1200
import RHInBox_1d2000000_1999999d2000000_1200_1250
import RHInBox_1d2000000_1999999d2000000_1250_1300
import RHInBox_1d2000000_1999999d2000000_1300_1350
import RHInBox_1d2000000_1999999d2000000_1350_1400
import RHInBox_1d2000000_1999999d2000000_1400_1450
import RHInBox_1d2000000_1999999d2000000_1450_1500
import RHInBox_1d2000000_1999999d2000000_1500_1550
import RHInBox_1d2000000_1999999d2000000_1550_1600
import RHInBox_1d2000000_1999999d2000000_1600_1650
import RHInBox_1d2000000_1999999d2000000_1650_1700
import RHInBox_1d2000000_1999999d2000000_1700_1750
import RHInBox_1d2000000_1999999d2000000_1750_1800
import RHInBox_1d2000000_1999999d2000000_1800_1850
import RHInBox_1d2000000_1999999d2000000_1850_1900
import RHInBox_1d2000000_1999999d2000000_1900_1950
import RHInBox_1d2000000_1999999d2000000_1950_2000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h2000

/-- The density-adaptive 39-band partition of `[0, 2000]`. -/
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
  | 20 => 1050
  | 21 => 1100
  | 22 => 1150
  | 23 => 1200
  | 24 => 1250
  | 25 => 1300
  | 26 => 1350
  | 27 => 1400
  | 28 => 1450
  | 29 => 1500
  | 30 => 1550
  | 31 => 1600
  | 32 => 1650
  | 33 => 1700
  | 34 => 1750
  | 35 => 1800
  | 36 => 1850
  | 37 => 1900
  | 38 => 1950
  | 39 => 2000
  | _ => 2000

theorem bnd_mono : Monotone bnd := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
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
  · show ((1000:ℝ)) ≤ (1050); norm_num
  · show ((1050:ℝ)) ≤ (1100); norm_num
  · show ((1100:ℝ)) ≤ (1150); norm_num
  · show ((1150:ℝ)) ≤ (1200); norm_num
  · show ((1200:ℝ)) ≤ (1250); norm_num
  · show ((1250:ℝ)) ≤ (1300); norm_num
  · show ((1300:ℝ)) ≤ (1350); norm_num
  · show ((1350:ℝ)) ≤ (1400); norm_num
  · show ((1400:ℝ)) ≤ (1450); norm_num
  · show ((1450:ℝ)) ≤ (1500); norm_num
  · show ((1500:ℝ)) ≤ (1550); norm_num
  · show ((1550:ℝ)) ≤ (1600); norm_num
  · show ((1600:ℝ)) ≤ (1650); norm_num
  · show ((1650:ℝ)) ≤ (1700); norm_num
  · show ((1700:ℝ)) ≤ (1750); norm_num
  · show ((1750:ℝ)) ≤ (1800); norm_num
  · show ((1800:ℝ)) ≤ (1850); norm_num
  · show ((1850:ℝ)) ≤ (1900); norm_num
  · show ((1900:ℝ)) ≤ (1950); norm_num
  · show ((1950:ℝ)) ≤ (2000); norm_num
  · show ((2000:ℝ)) ≤ (2000); norm_num
  · exact le_refl _

/-- `1/(2·10⁶) ≤ dlvpRateC / log 2000` — via the shared `dlvpRateC_lower` and `log 2000 ≤ 8`
    (`2.7⁸ ≈ 2824 ≥ 2000`).  conjecture1_proved = False. -/
theorem haC_2000 : (1 / 2000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 2000 := by
  have hlog : Real.log 2000 ≤ 8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h8 : Real.exp 8 = (Real.exp 1) ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 8 ≤ (Real.exp 1) ^ 8 := pow_le_pow_left₀ (by norm_num) he1 8
    rw [h8]; nlinarith [hpow]
  have hpos : 0 < Real.log 2000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 2000000 : ℝ) * Real.log 2000
      ≤ (1 / 2000000) * 8 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- **T = 2000 from the 39 band CONCLUSIONS** — 1517 zeros.  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_2000_of_bands
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
    (hband19 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1050)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband20 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1050) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1100)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband21 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1100) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1150)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband22 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1150) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband23 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1250)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband24 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1250) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1300)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband25 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1300) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1350)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband26 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1350) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband27 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1450)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband28 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1450) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1500)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband29 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1500) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1550)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband30 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1550) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband31 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1650)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband32 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1650) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1700)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband33 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1750)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband34 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1750) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband35 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1850)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband36 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1850) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1900)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband37 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1900) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1950)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband38 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1950) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 2000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 2000000 = 1999999 / 2000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line_tiled
    (1 / 2000000) 2000 bnd 39 (by norm_num) bnd_mono rfl rfl haC_2000 (by norm_num) (by norm_num)
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
  · exact hband19 ρ hre' him hz
  · exact hband20 ρ hre' him hz
  · exact hband21 ρ hre' him hz
  · exact hband22 ρ hre' him hz
  · exact hband23 ρ hre' him hz
  · exact hband24 ρ hre' him hz
  · exact hband25 ρ hre' him hz
  · exact hband26 ρ hre' him hz
  · exact hband27 ρ hre' him hz
  · exact hband28 ρ hre' him hz
  · exact hband29 ρ hre' him hz
  · exact hband30 ρ hre' him hz
  · exact hband31 ρ hre' him hz
  · exact hband32 ρ hre' him hz
  · exact hband33 ρ hre' him hz
  · exact hband34 ρ hre' him hz
  · exact hband35 ρ hre' him hz
  · exact hband36 ρ hre' him hz
  · exact hband37 ρ hre' him hz
  · exact hband38 ρ hre' him hz

end AllZeros_h2000
