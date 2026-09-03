/- telperion 0.1.6 | family SeparableConvex | input-hash 48f7726c144173a0
   5 theorems, 13 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SeparableConvex

-- Separable-convex MINIMUM at the homogeneous point S/n (Jensen); box bounds scope the slice.
theorem sepconv_jensen_sq3 (x1 x2 x3 : ℝ) (hlo1 : (0 : ℝ) ≤ x1) (hhi1 : x1 ≤ 3) (hlo2 : (0 : ℝ) ≤ x2) (hhi2 : x2 ≤ 3) (hlo3 : (0 : ℝ) ≤ x3) (hhi3 : x3 ≤ 3) (hsum : x1 + x2 + x3 = 3) :
    (3 : ℝ) ≤ (x1 ^ 2) + (x2 ^ 2) + (x3 ^ 2) := by
  have h1 : (0:ℝ) ≤ (x1 ^ 2) - ((-1) + 2 * x1) := by
    have e1 : (x1 ^ 2) - ((-1) + 2 * x1) = 1 * (x1 - 1)^2 := by ring
    rw [e1]; positivity
  have h2 : (0:ℝ) ≤ (x2 ^ 2) - ((-1) + 2 * x2) := by
    have e2 : (x2 ^ 2) - ((-1) + 2 * x2) = 1 * (x2 - 1)^2 := by ring
    rw [e2]; positivity
  have h3 : (0:ℝ) ≤ (x3 ^ 2) - ((-1) + 2 * x3) := by
    have e3 : (x3 ^ 2) - ((-1) + 2 * x3) = 1 * (x3 - 1)^2 := by ring
    rw [e3]; positivity
  linarith [h1, h2, h3, hsum]
-- Separable-convex MINIMUM at the homogeneous point S/n (Jensen); box bounds scope the slice.
theorem sepconv_quartic_box (x1 x2 : ℝ) (hlo1 : ((1 / 2) : ℝ) ≤ x1) (hhi1 : x1 ≤ (3 / 2)) (hlo2 : ((1 / 2) : ℝ) ≤ x2) (hhi2 : x2 ≤ (3 / 2)) (hsum : x1 + x2 = 2) :
    (2 : ℝ) ≤ (x1 ^ 4) + (x2 ^ 4) := by
  have h1 : (0:ℝ) ≤ (x1 ^ 4) - ((-3) + 4 * x1) := by
    have e1 : (x1 ^ 4) - ((-3) + 4 * x1) = 1 * (x1 ^ 2 - 1)^2 + 2 * (x1 - 1)^2 := by ring
    rw [e1]; positivity
  have h2 : (0:ℝ) ≤ (x2 ^ 4) - ((-3) + 4 * x2) := by
    have e2 : (x2 ^ 4) - ((-3) + 4 * x2) = 1 * (x2 ^ 2 - 1)^2 + 2 * (x2 - 1)^2 := by ring
    rw [e2]; positivity
  linarith [h1, h2, hsum]
-- Separable-convex MAXIMUM at the VERTEX (push n−1 coords to the common bound u; last carries the residual).
-- Parameterizes the proven VertexLemmaFull.glemma_push_to_bound spreading exchange + vertex_bound chain.
theorem sepconv_max_sq3 (x1 x2 x3 : ℝ) (hlo1 : (0 : ℝ) ≤ x1) (hhi1 : x1 ≤ 3) (hlo2 : (0 : ℝ) ≤ x2) (hhi2 : x2 ≤ 3) (hlo3 : (0 : ℝ) ≤ x3) (hhi3 : x3 ≤ 3) (hsum : x1 + x2 + x3 = 6) :
    (1 * (x1)^2) + (1 * (x2)^2) + (1 * (x3)^2) ≤ (18 : ℝ) := by
  have e1 : (1 * (x1)^2) + (1 * (x2)^2) ≤ (1 * ((x1) + x2 - 3)^2) + (9) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 - (x1)) (by linarith : (0:ℝ) ≤ 3 - (x2))]
  have e2 : (1 * ((x1) + x2 - 3)^2) + (1 * (x3)^2) ≤ (1 * (((x1) + x2 - 3) + x3 - 3)^2) + (9) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 - ((x1) + x2 - 3)) (by linarith : (0:ℝ) ≤ 3 - (x3))]
  have hres : (((x1) + x2 - 3) + x3 - 3) = 0 := by linarith
  rw [hres] at e2
  norm_num at e2
  linarith [e1, e2]
-- Separable-convex MAXIMUM at the VERTEX (push n−1 coords to the common bound u; last carries the residual).
-- Parameterizes the proven VertexLemmaFull.glemma_push_to_bound spreading exchange + vertex_bound chain.
theorem sepconv_max_quartic (x1 x2 x3 : ℝ) (hlo1 : (0 : ℝ) ≤ x1) (hhi1 : x1 ≤ 2) (hlo2 : (0 : ℝ) ≤ x2) (hhi2 : x2 ≤ 2) (hlo3 : (0 : ℝ) ≤ x3) (hhi3 : x3 ≤ 2) (hsum : x1 + x2 + x3 = 5) :
    (1 * (x1)^4) + (1 * (x2)^4) + (1 * (x3)^4) ≤ (33 : ℝ) := by
  have e1 : (1 * (x1)^4) + (1 * (x2)^4) ≤ (1 * ((x1) + x2 - 2)^4) + (16) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2)),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2))) (sq_nonneg ((x1) + (x2))),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2))) (sq_nonneg ((x1) - (x2)))]
  have e2 : (1 * ((x1) + x2 - 2)^4) + (1 * (x3)^4) ≤ (1 * (((x1) + x2 - 2) + x3 - 2)^4) + (16) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - ((x1) + x2 - 2)) (by linarith : (0:ℝ) ≤ 2 - (x3)),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - ((x1) + x2 - 2)) (by linarith : (0:ℝ) ≤ 2 - (x3))) (sq_nonneg (((x1) + x2 - 2) + (x3))),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - ((x1) + x2 - 2)) (by linarith : (0:ℝ) ≤ 2 - (x3))) (sq_nonneg (((x1) + x2 - 2) - (x3)))]
  have hres : (((x1) + x2 - 2) + x3 - 2) = 1 := by linarith
  rw [hres] at e2
  norm_num at e2
  linarith [e1, e2]
-- Separable-convex MAXIMUM at the VERTEX (push n−1 coords to the common bound u; last carries the residual).
-- Parameterizes the proven VertexLemmaFull.glemma_push_to_bound spreading exchange + vertex_bound chain.
theorem sepconv_max_deg6 (x1 x2 : ℝ) (hlo1 : (1 : ℝ) ≤ x1) (hhi1 : x1 ≤ 2) (hlo2 : (1 : ℝ) ≤ x2) (hhi2 : x2 ≤ 2) (hsum : x1 + x2 = 3) :
    (1 * (x1)^2 + 1 * (x1)^6) + (1 * (x2)^2 + 1 * (x2)^6) ≤ (70 : ℝ) := by
  have e1 : (1 * (x1)^2 + 1 * (x1)^6) + (1 * (x2)^2 + 1 * (x2)^6) ≤ (1 * ((x1) + x2 - 2)^2 + 1 * ((x1) + x2 - 2)^6) + (68) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2)),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2))) (sq_nonneg ((x1) + (x2))),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2))) (sq_nonneg ((x1) - (x2))),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2))) (sq_nonneg ((x1)^2 + (x2)^2)),
               mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (x1)) (by linarith : (0:ℝ) ≤ 2 - (x2))) (sq_nonneg ((x1)^2 - (x2)^2))]
  have hres : ((x1) + x2 - 2) = 1 := by linarith
  rw [hres] at e1
  norm_num at e1
  linarith [e1]

end SeparableConvex
