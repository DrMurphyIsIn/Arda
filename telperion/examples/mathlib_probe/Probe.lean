/- D3 core: the G-monotonicity reduction lemma (heart of the SA/CA reduction). -/
import Mathlib
open scoped Real

/-- If the abundancy sigma(m)/m dominates sigma(n)/n and log log m <= log log n (as when
    m <= n), then the Robin quotient G(n) = sigma(n)/(n log log n) is dominated by G(m).
    Hence a Robin violation at n forces one at the abundancy-record m: the least Robin
    counterexample is superabundant (Akbary-Friggstad 2009). Reduction lemma only -- proves
    nothing about RH. -/
theorem robin_G_monotone
    {sm sn m n : ℝ} (hsm : 0 ≤ sm / m)
    (habund : sn / n ≤ sm / m)
    (hLm : 0 < Real.log (Real.log m))
    (hLmn : Real.log (Real.log m) ≤ Real.log (Real.log n)) :
    sn / (n * Real.log (Real.log n)) ≤ sm / (m * Real.log (Real.log m)) := by
  rw [← div_div, ← div_div]
  gcongr
