/- telperion 0.1.6 | family AffineParamEndpoint | input-hash 90adcf95bf2b01f6
   4 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace AffineParamEndpoint

-- (1) ABSTRACT CORE.  An affine map `A + μ·B` that is nonneg at both
-- endpoints of `[lo,hi]` is nonneg throughout, via the identity
--   (hi−lo)(A+μB) = (hi−μ)(A+loB) + (μ−lo)(A+hiB),  both summands ≥ 0.
theorem affine_endpoint_nonneg (A B lo hi μ : ℝ)
    (hlo : lo ≤ μ) (hhi : μ ≤ hi)
    (hL : 0 ≤ A + lo * B) (hH : 0 ≤ A + hi * B) :
    0 ≤ A + μ * B := by
  -- (hi−μ)(A+loB) ≥ 0 and (μ−lo)(A+hiB) ≥ 0; their sum is
  -- (hi−lo)(A+μB).  Case-split on the interval being nondegenerate.
  have hprodL : 0 ≤ (hi - μ) * (A + lo * B) :=
    mul_nonneg (sub_nonneg.mpr hhi) hL
  have hprodH : 0 ≤ (μ - lo) * (A + hi * B) :=
    mul_nonneg (sub_nonneg.mpr hlo) hH
  rcases (le_trans hlo hhi).lt_or_eq with hlt | heq
  · -- lo < hi: divide the summed identity by (hi − lo) > 0.
    nlinarith [hprodL, hprodH, sub_pos.mpr hlt]
  · -- lo = hi forces μ = lo = hi, so A + μB = A + lo·B ≥ 0.
    have hμlo : μ = lo := le_antisymm (heq ▸ hhi) hlo
    rw [hμlo]; exact hL

-- (2) bV-SHAPED SCLStep APPLICATION.  With `f = bell`, `g = bY` opaque,
-- `x = node cs`, `c = cherry`: endpoint-wise `≤` at `lo` and `hi` lifts
-- to `≤` at every interior price `μ`.  Reduces to (1) with
-- `A = f c − f x`, `B = g c − g x` (the affine gap G(μ) = A + μ·B).
theorem bV_interval_of_endpoints {α : Type*} (f g : α → ℝ) (x c : α)
    (lo hi μ : ℝ) (hlo : lo ≤ μ) (hhi : μ ≤ hi)
    (hL : (f x + lo * g x) ≤ (f c + lo * g c))
    (hH : (f x + hi * g x) ≤ (f c + hi * g c)) :
    (f x + μ * g x) ≤ (f c + μ * g c) := by
  have hL' : 0 ≤ (f c - f x) + lo * (g c - g x) := by nlinarith [hL]
  have hH' : 0 ≤ (f c - f x) + hi * (g c - g x) := by nlinarith [hH]
  have hcore : 0 ≤ (f c - f x) + μ * (g c - g x) :=
    affine_endpoint_nonneg (f c - f x) (g c - g x) lo hi μ hlo hhi hL' hH'
  nlinarith [hcore]

-- (3) CONCRETE RATIONAL SANITY INSTANCE `scl_gap_ascending`.  Instantiates the
-- abstract core at the REAL SCLStep interval endpoints lo = 456/3703,
-- hi = 3/7 and the interior price μ = 1/4: with A = 1, B = 2
-- both endpoint values are ≥ 0, so the gap A + μ·B ≥ 0.
example : (0 : ℝ) ≤ (1) + (1/4) * (2) :=
  affine_endpoint_nonneg (1) (2) (456/3703) (3/7) (1/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- (3) CONCRETE RATIONAL SANITY INSTANCE `scl_gap_descending`.  Instantiates the
-- abstract core at the REAL SCLStep interval endpoints lo = 456/3703,
-- hi = 3/7 and the interior price μ = 3/8: with A = 1, B = -1
-- both endpoint values are ≥ 0, so the gap A + μ·B ≥ 0.
example : (0 : ℝ) ≤ (1) + (3/8) * (-1) :=
  affine_endpoint_nonneg (1) (-1) (456/3703) (3/7) (3/8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end AffineParamEndpoint
