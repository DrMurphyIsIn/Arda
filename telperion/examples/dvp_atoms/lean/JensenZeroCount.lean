/- telperion 0.1.6 | family JensenZeroCount | input-hash 2d33f2b9b76dc3f9
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace JensenZeroCount

-- Jensen zero-count on radii (r, R) = (1/2, 1): the number of
-- zeros of an analytic f in the inner disk is bounded by its boundary growth.
theorem jensen_count_half_one {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c |(1 : ℝ)|))
    (hfc : f c ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ Metric.sphere c |(1 : ℝ)|, ‖f z‖ ≤ M) :
    ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall c |(1 / 2 : ℝ)|) u
      ≤ Real.log (M / ‖f c‖) / Real.log ((1 : ℝ) / (1 / 2 : ℝ)) :=
  hf.sum_divisor_le (by norm_num) (by norm_num) hM hfc hbound

-- Jensen zero-count on radii (r, R) = (1/4, 3/4): the number of
-- zeros of an analytic f in the inner disk is bounded by its boundary growth.
theorem jensen_count_qtr_3qtr {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c |(3 / 4 : ℝ)|))
    (hfc : f c ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ Metric.sphere c |(3 / 4 : ℝ)|, ‖f z‖ ≤ M) :
    ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall c |(1 / 4 : ℝ)|) u
      ≤ Real.log (M / ‖f c‖) / Real.log ((3 / 4 : ℝ) / (1 / 4 : ℝ)) :=
  hf.sum_divisor_le (by norm_num) (by norm_num) hM hfc hbound

end JensenZeroCount
