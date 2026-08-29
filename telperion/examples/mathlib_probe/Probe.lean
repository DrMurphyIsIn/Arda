/- Rung 4 API: how does LSeries unfold, does Re commute with tsum, Summable.re, the ↗Λ form? -/
import Mathlib
open scoped Real

#check @LSeries
#check @LSeries_congr
#check @Complex.re_tsum
#check @Complex.reCLM
#check @ContinuousLinearMap.map_tsum
#check @Complex.hasSum_re
#check @Summable.re
#check @ArithmeticFunction.LSeriesSummable_vonMangoldt
#check @LSeriesSummable
#check @tsum_mul_left
#check @tsum_add
#check @tsum_nonneg

-- is LSeries f s definitionally ∑' n, term f s n ?
example (f : ℕ → ℂ) (s : ℂ) : LSeries f s = ∑' n, LSeries.term f s n := rfl
