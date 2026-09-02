/- telperion 0.1.6 | family LogDerivRegion | input-hash 0e95d5b76587c2aa
   4 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace LogDerivRegion

/-- de la Vallee Poussin CORE ESTIMATE (A=1, L=1, k=1),
    ported from `dlvp_core_estimate` with the three `-Re ζ'/ζ` values abstracted
    to reals `Pσ, Pσt, Pσ2t` (Mathlib-only; identical linear-arithmetic content).
    From 3-4-1 positivity + pole/zero/double bounds, the order-k zero satisfies
    `4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5AL`. -/
theorem dlvp_region_unit_core (σ β Pσ Pσt Pσ2t : ℝ) (hσ : 1 < σ)
    (hpos : 0 ≤ 3 * Pσ + 4 * Pσt + Pσ2t)
    (hpole : Pσ ≤ 1 / (σ - 1) + 1)
    (hzero : Pσt ≤ 1 * 1 - 1 / (σ - β))
    (htwo : Pσ2t ≤ 1 * 1) :
    (4 : ℝ) * (1 / (σ - β)) ≤ 3 / (σ - 1) + 3 * 1 + 5 * (1 * 1) := by
  rw [show (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  linarith [hpos, hpole, hzero, htwo]
/-- REGION GAP (cleared form) for A=1, L=1: with an order-k≥1 zero,
    the core estimate pushes the zero left of the 1-line.  Ported verbatim from the
    Mathlib-only `dlvp_region_gap`; `B = 3A + 5AL`, cross-multiplied. -/
theorem dlvp_region_unit_gap (σ β : ℝ) (k : ℤ) (hk : 1 ≤ k) (hσ : 1 < σ) (hβσ : β < σ)
    (hcore : (4 : ℝ) * ((k : ℝ) / (σ - β))
      ≤ 3 / (σ - 1) + (3 * 1 + 5 * (1 * 1))) :
    (σ - 1) * (1 - (σ - 1) * (3 * 1 + 5 * (1 * 1)))
      ≤ (1 - β) * (3 + (σ - 1) * (3 * 1 + 5 * (1 * 1))) := by
  have hd : (0 : ℝ) < σ - 1 := by linarith
  have hd' : σ - 1 ≠ 0 := hd.ne'
  have hsb : (0 : ℝ) < σ - β := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set B := (3 * 1 + 5 * (1 * 1) : ℝ) with hBdef
  have lhs_eq : 4 * ((k : ℝ) / (σ - β)) = (4 * (k : ℝ)) / (σ - β) := by ring
  have rhs_eq : 3 / (σ - 1) + B = (3 + B * (σ - 1)) / (σ - 1) := by field_simp
  rw [lhs_eq, rhs_eq, div_le_iff₀ hsb, div_mul_eq_mul_div, le_div_iff₀ hd] at hcore
  have key : 4 * (σ - 1) ≤ (3 + B * (σ - 1)) * (σ - β) := by nlinarith [hcore, hk1, hd, hsb]
  nlinarith [key, hd, hsb]
/-- de la Vallee Poussin CORE ESTIMATE (A=2, L=3, k=2),
    ported from `dlvp_core_estimate` with the three `-Re ζ'/ζ` values abstracted
    to reals `Pσ, Pσt, Pσ2t` (Mathlib-only; identical linear-arithmetic content).
    From 3-4-1 positivity + pole/zero/double bounds, the order-k zero satisfies
    `4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5AL`. -/
theorem dlvp_region_A2L3k2_core (σ β Pσ Pσt Pσ2t : ℝ) (hσ : 1 < σ)
    (hpos : 0 ≤ 3 * Pσ + 4 * Pσt + Pσ2t)
    (hpole : Pσ ≤ 1 / (σ - 1) + 2)
    (hzero : Pσt ≤ 2 * 3 - 2 / (σ - β))
    (htwo : Pσ2t ≤ 2 * 3) :
    (4 : ℝ) * (2 / (σ - β)) ≤ 3 / (σ - 1) + 3 * 2 + 5 * (2 * 3) := by
  rw [show (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  linarith [hpos, hpole, hzero, htwo]
/-- REGION GAP (cleared form) for A=2, L=3: with an order-k≥1 zero,
    the core estimate pushes the zero left of the 1-line.  Ported verbatim from the
    Mathlib-only `dlvp_region_gap`; `B = 3A + 5AL`, cross-multiplied. -/
theorem dlvp_region_A2L3k2_gap (σ β : ℝ) (k : ℤ) (hk : 1 ≤ k) (hσ : 1 < σ) (hβσ : β < σ)
    (hcore : (4 : ℝ) * ((k : ℝ) / (σ - β))
      ≤ 3 / (σ - 1) + (3 * 2 + 5 * (2 * 3))) :
    (σ - 1) * (1 - (σ - 1) * (3 * 2 + 5 * (2 * 3)))
      ≤ (1 - β) * (3 + (σ - 1) * (3 * 2 + 5 * (2 * 3))) := by
  have hd : (0 : ℝ) < σ - 1 := by linarith
  have hd' : σ - 1 ≠ 0 := hd.ne'
  have hsb : (0 : ℝ) < σ - β := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set B := (3 * 2 + 5 * (2 * 3) : ℝ) with hBdef
  have lhs_eq : 4 * ((k : ℝ) / (σ - β)) = (4 * (k : ℝ)) / (σ - β) := by ring
  have rhs_eq : 3 / (σ - 1) + B = (3 + B * (σ - 1)) / (σ - 1) := by field_simp
  rw [lhs_eq, rhs_eq, div_le_iff₀ hsb, div_mul_eq_mul_div, le_div_iff₀ hd] at hcore
  have key : 4 * (σ - 1) ≤ (3 + B * (σ - 1)) * (σ - β) := by nlinarith [hcore, hk1, hd, hsb]
  nlinarith [key, hd, hsb]

end LogDerivRegion
