/- D3: G-monotonicity reduction lemma. If sigma(m)/m >= sigma(n)/n and log log m <=
   log log n (as when m <= n), then G(n)=sigma(n)/(n loglog n) <= G(m).  A Robin
   violation at n forces one at the abundancy-record m -- so the least Robin
   counterexample is superabundant.  Reduction lemma only; proves nothing about RH. -/
import Mathlib
open scoped Real

namespace RobinReduction

theorem robin_G_monotone
    {sm sn m n : ℝ} (hsm : 0 ≤ sm / m)
    (habund : sn / n ≤ sm / m)
    (hLm : 0 < Real.log (Real.log m))
    (hLmn : Real.log (Real.log m) ≤ Real.log (Real.log n)) :
    sn / (n * Real.log (Real.log n)) ≤ sm / (m * Real.log (Real.log m)) := by
  rw [← div_div, ← div_div]
  gcongr

end RobinReduction
