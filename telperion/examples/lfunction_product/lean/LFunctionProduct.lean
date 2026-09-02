/- telperion 0.1.6 | family LFunctionProduct | input-hash 43297720abd43d69
   1 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace LFunctionProduct

-- zeta_norm_product_341: nonneg-cosine -> L-product lower bound, ζ.
-- cosine tuple a_k = [3, 4, 1] (all ≥ 0); FEJÉR-ADMISSIBLE:
--   Σ a_k cos kθ = p(cos θ) ≥ 0 with p(x) = 2*(x + 1)**2
--   (Handelman/Fejér–Riesz witness on [−1,1]: 2*(1+x)^2).
-- The classical 3-4-1: 3 + 4 cos θ + cos 2θ = 2(1+cos θ)^2 ≥ 0.
-- Coupled to DirichletCharacter.norm_LFunction_product_ge_one
-- (modulus 1) + LFunction_modOne_eq (@[simp]) + norm_mul/norm_pow.
theorem zeta_norm_product_341 {x : ℝ} (hx : 0 < x) (y : ℝ) :
    (1:ℝ) ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + Complex.I * y)‖ ^ 4
        * ‖riemannZeta (1 + x + 2 * Complex.I * y)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one
    (χ := (1 : DirichletCharacter ℂ 1)) hx y
  rw [ge_iff_le] at h
  have htriv : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  rw [htriv] at h
  simp only [DirichletCharacter.LFunction_modOne_eq, norm_mul, norm_pow] at h
  exact h

end LFunctionProduct
