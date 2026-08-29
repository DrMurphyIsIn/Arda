/- D4: Nicolas => Robin bridge  phi(n) * sigma(n) < n^2  (= sigma(n)/n < n/phi(n)),
   the elementary connector making Nicolas's RH-equivalent criterion imply Robin's.
   Unconditionally true; finite instances at primorials. NOT itself RH-equivalent,
   proves nothing about RH.  See ROBIN_RH_MAP.md (equivalences) / ROBIN_REDUCTION_D3.md. -/
import Mathlib

namespace NicolasBridge

theorem nicolas_robin_bridge_6 :
    Nat.totient 6 * (∑ d ∈ Nat.divisors 6, d) < 6 ^ 2 := by decide

theorem nicolas_robin_bridge_30 :
    Nat.totient 30 * (∑ d ∈ Nat.divisors 30, d) < 30 ^ 2 := by decide

theorem nicolas_robin_bridge_210 :
    Nat.totient 210 * (∑ d ∈ Nat.divisors 210, d) < 210 ^ 2 := by decide

end NicolasBridge
