/- telperion 0.1.6 | family CavityExchange | input-hash d6eaa46d022ba67f
   3 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace CavityExchange

/-- **Bilinear box → four corners.**  For a form `Φ(x,y) = a + b·x + c·y + e·x·y`
    that is AFFINE in each variable separately, if `Φ ≥ 0` at all four corners of
    the box `x ∈ [x0,x1], y ∈ [y0,y1]` then `Φ ≥ 0` on the whole box.  This is the
    reusable "bilinear box → 4 corners" engine behind the Kelmans de-branch
    monotonicity step: `Aobj(t')−Aobj(t) = P·FS·FQ·Φ` with `P,FS,FQ > 0`, so the
    sign is carried by `Φ`, whose box-min sits at a vertex. -/
theorem bilinear_ge_of_corners
    (a b c e x0 x1 y0 y1 x y : ℝ)
    (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1)
    (hlt_x : x0 < x1) (hlt_y : y0 < y1)
    (hC0 : 0 ≤ a + b * x0 + c * y0 + e * (x0 * y0))
    (hC1 : 0 ≤ a + b * x1 + c * y0 + e * (x1 * y0))
    (hC2 : 0 ≤ a + b * x0 + c * y1 + e * (x0 * y1))
    (hC3 : 0 ≤ a + b * x1 + c * y1 + e * (x1 * y1)) :
    0 ≤ a + b * x + c * y + e * (x * y) := by
  -- Affine in y at fixed x ⟹ min over y is at y0 or y1; likewise affine in x.
  -- The nonnegative interval products pin the vertex domination.
  have hpx0 : 0 ≤ x - x0 := by linarith
  have hpx1 : 0 ≤ x1 - x := by linarith
  have hpy0 : 0 ≤ y - y0 := by linarith
  have hpy1 : 0 ≤ y1 - y := by linarith
  have hdx : 0 < x1 - x0 := by linarith
  have hdy : 0 < y1 - y0 := by linarith
  -- Write Φ(x,y) as the convex combination of the four corner values with the
  -- nonnegative barycentric weights (x1−x)(y1−y), (x−x0)(y1−y), … over (x1−x0)(y1−y0).
  have key :
      ((x1 - x0) * (y1 - y0)) * (a + b * x + c * y + e * (x * y))
        = (x1 - x) * (y1 - y) * (a + b * x0 + c * y0 + e * (x0 * y0))
          + (x - x0) * (y1 - y) * (a + b * x1 + c * y0 + e * (x1 * y0))
          + (x1 - x) * (y - y0) * (a + b * x0 + c * y1 + e * (x0 * y1))
          + (x - x0) * (y - y0) * (a + b * x1 + c * y1 + e * (x1 * y1)) := by
    ring
  have hw0 : 0 ≤ (x1 - x) * (y1 - y) := mul_nonneg hpx1 hpy1
  have hw1 : 0 ≤ (x - x0) * (y1 - y) := mul_nonneg hpx0 hpy1
  have hw2 : 0 ≤ (x1 - x) * (y - y0) := mul_nonneg hpx1 hpy0
  have hw3 : 0 ≤ (x - x0) * (y - y0) := mul_nonneg hpx0 hpy0
  have hrhs :
      0 ≤ (x1 - x) * (y1 - y) * (a + b * x0 + c * y0 + e * (x0 * y0))
          + (x - x0) * (y1 - y) * (a + b * x1 + c * y0 + e * (x1 * y0))
          + (x1 - x) * (y - y0) * (a + b * x0 + c * y1 + e * (x0 * y1))
          + (x - x0) * (y - y0) * (a + b * x1 + c * y1 + e * (x1 * y1)) := by
    have t0 := mul_nonneg hw0 hC0
    have t1 := mul_nonneg hw1 hC1
    have t2 := mul_nonneg hw2 hC2
    have t3 := mul_nonneg hw3 hC3
    linarith
  have hden : 0 < (x1 - x0) * (y1 - y0) := mul_pos hdx hdy
  nlinarith [key, hrhs, hden]

-- ALL-NONNEG-COEFF Polya corner C0 of the Kelmans de-branch Φ.
-- After the nonneg domain shift (da=1+u, db=2+v, c=3+s), every coefficient is
-- nonnegative, so the polynomial is ≥ 0 for all u,v,s ≥ 0 (positivity).
-- Corner C0 reproduces R47R4KelmansCornerCert.lean faithfully; siblings share the shape.
theorem kelmans_corner_C0_nonneg (u v s : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) :
    0 ≤ 7 * u * v * s ^ 2 + 3 * u * v ^ 2 * s + 3 * u ^ 2 * v * s + 7 * u * s ^ 2 + 54 * u * v * s + 9 * u * v ^ 2 + 3 * u ^ 2 * s + 9 * u ^ 2 * v + 51 * u * s + 108 * u * v + 9 * u ^ 2 + 99 * u := by
  positivity

-- ALL-NONNEG-COEFF Polya corner C1 of the Kelmans de-branch Φ.
-- After the nonneg domain shift (da=1+u, db=2+v, c=3+s), every coefficient is
-- nonnegative, so the polynomial is ≥ 0 for all u,v,s ≥ 0 (positivity).
-- Corner C0 reproduces R47R4KelmansCornerCert.lean faithfully; siblings share the shape.
theorem kelmans_corner_C1_nonneg (u v s : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) :
    0 ≤ 5 * u * v * s ^ 2 + 4 * u ^ 2 * v * s + 2 * v * s ^ 2 + 6 * u * v * s + 13 * u * v ^ 2 + 11 * u ^ 2 * v + 8 * v * s + 17 * u * v + 19 * v := by
  positivity

-- WORKED APPLICATION of the reusable bilinear-box→4-corners engine.
-- Concrete all-corner-nonneg Φ(x,y)=1+2·x+3·y+x·y on [0,1]×[0,1];
-- corner values ['1', '3', '4', '7'] are all ≥ 0, so Φ ≥ 0 on the box.
theorem kelmans_bilinear_box_reduction (x y : ℝ)
    (hx0 : (0:ℝ) ≤ x) (hx1 : x ≤ 1) (hy0 : (0:ℝ) ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 1 + 2 * x + 3 * y + 1 * (x * y) := by
  refine bilinear_ge_of_corners 1 2 3 1 0 1 0 1 x y
    hx0 hx1 hy0 hy1 (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end CavityExchange
