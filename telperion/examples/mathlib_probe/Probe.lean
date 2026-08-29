/- D4: Nicolas => Robin bridge  phi(n) * sigma(n) < n^2  (sigma = sum of divisors), the
   elementary connector that makes Nicolas's criterion imply Robin's. Unconditionally true
   for n > 1; here finite kernel instances at primorials. NOT itself RH-equivalent. -/
import Mathlib

example : Nat.totient 30 * (∑ d ∈ Nat.divisors 30, d) < 30 ^ 2 := by decide
example : Nat.totient 210 * (∑ d ∈ Nat.divisors 210, d) < 210 ^ 2 := by decide
example : Nat.totient 2310 * (∑ d ∈ Nat.divisors 2310, d) < 2310 ^ 2 := by decide
