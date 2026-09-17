/- telperion 0.1.6 | family BraggFloor | input-hash f5987a075cfd7817
   15 theorems, 15 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import RvMRoutePFalsify
import RvMCompanionPrime
import RvMCompanionBraggLimit

namespace BraggFloor

open Complex

open RvMWeierstrass in
-- bragg_below_floor_refutes_rh: the falsifiability face of the diffraction ladder.  Through
-- the CONDITIONAL reduction taylorCoeff_companion_bragg_of_exhaustion_limits (hypothesis
-- hcomp, the RH-hard exhaustion/extraction seam — NEVER discharged), a certified Bragg
-- datum strictly below the archimedean floor refutes RH via companion_below_floor_refutes_rh.
-- Not expected to fire; emitted so the ladder is falsifiable, not confirmation-only.
-- conjecture1_proved = False.
theorem bragg_below_floor_refutes_rh (n : ℕ) (braggVal : ℝ)
    (hcomp : (LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n).re = braggVal)
    (hbelow : braggVal < -(1 + (LiCriterion.taylorCoeff Complex.Gammaℝ n).re)) :
    ¬RiemannHypothesis :=
  companion_below_floor_refutes_rh n (hcomp ▸ hbelow)

-- bragg_rung_0: Route P Brick D3 diffraction rung, order n=0.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=17316248623/31250000000 ≥ -(1+Re taylorCoeff Γℝ 0).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 0).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_0 : ((17316248623 / 31250000000) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_6: Route P Brick D3 diffraction rung, order n=6.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=88932680667/250000000000 ≥ -(1+Re taylorCoeff Γℝ 6).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 6).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_6 : ((88932680667 / 250000000000) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_7: Route P Brick D3 diffraction rung, order n=7.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-52249832569/2500000000000 ≥ -(1+Re taylorCoeff Γℝ 7).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 7).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_7 : ((-(52249832569 / 2500000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_8: Route P Brick D3 diffraction rung, order n=8.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-460319641591/1000000000000 ≥ -(1+Re taylorCoeff Γℝ 8).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 8).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_8 : ((-(460319641591 / 1000000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_9: Route P Brick D3 diffraction rung, order n=9.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-119441959937/125000000000 ≥ -(1+Re taylorCoeff Γℝ 9).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 9).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_9 : ((-(119441959937 / 125000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_10: Route P Brick D3 diffraction rung, order n=10.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-150091806239/100000000000 ≥ -(1+Re taylorCoeff Γℝ 10).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 10).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_10 : ((-(150091806239 / 100000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_11: Route P Brick D3 diffraction rung, order n=11.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-26148213421/12500000000 ≥ -(1+Re taylorCoeff Γℝ 11).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 11).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_11 : ((-(26148213421 / 12500000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_12: Route P Brick D3 diffraction rung, order n=12.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-272451874073/100000000000 ≥ -(1+Re taylorCoeff Γℝ 12).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 12).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_12 : ((-(272451874073 / 100000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_13: Route P Brick D3 diffraction rung, order n=13.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-339566826609/100000000000 ≥ -(1+Re taylorCoeff Γℝ 13).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 13).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_13 : ((-(339566826609 / 100000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_14: Route P Brick D3 diffraction rung, order n=14.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-205127047547/50000000000 ≥ -(1+Re taylorCoeff Γℝ 14).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 14).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_14 : ((-(205127047547 / 50000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_15: Route P Brick D3 diffraction rung, order n=15.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-121068664687/25000000000 ≥ -(1+Re taylorCoeff Γℝ 15).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 15).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_15 : ((-(121068664687 / 25000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_16: Route P Brick D3 diffraction rung, order n=16.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-561419765951/100000000000 ≥ -(1+Re taylorCoeff Γℝ 16).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 16).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_16 : ((-(561419765951 / 100000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_17: Route P Brick D3 diffraction rung, order n=17.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-641505465531/100000000000 ≥ -(1+Re taylorCoeff Γℝ 17).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 17).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_17 : ((-(641505465531 / 100000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_18: Route P Brick D3 diffraction rung, order n=18.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-724368381993/100000000000 ≥ -(1+Re taylorCoeff Γℝ 18).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 18).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_18 : ((-(724368381993 / 100000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

-- bragg_rung_19: Route P Brick D3 diffraction rung, order n=19.  At base point s0=2 the truncated log-prime (von Mangoldt / Bragg) amplitude over p^k ≤ 5000,
-- bounded below by braggLo=113952196637/200000000000, net of the certified tail tailHi=190343863829/100000000000000, clears the explicit archimedean floor floorHi=-809862405929/100000000000 ≥ -(1+Re taylorCoeff Γℝ 19).
-- Trust seam: braggLo/tailHi/floorHi are Arb (python-flint) enclosures — the documented non-kernel input.
-- This is a FINITE inequality (category-b), proves NOTHING about RH; the passage to (taylorCoeff zetaPoleCompanion 19).re runs through the CONDITIONAL, RH-hard
-- taylorCoeff_companion_bragg_of_exhaustion_limits (never discharged here).  conjecture1_proved = False.
theorem bragg_rung_19 : ((-(809862405929 / 100000000000)) : ℝ) ≤ (113952196637 / 200000000000) - (190343863829 / 100000000000000) := by norm_num

end BraggFloor
