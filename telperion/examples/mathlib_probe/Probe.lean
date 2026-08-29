/- D4 API probe: Nicolas => Robin bridge  sigma(n)*phi(n) < n^2  (n>=2), and the
   sigma/totient multiplicativity + prime-power API available in Mathlib v4.32.0. -/
import Mathlib
open scoped Real

#check @Nat.sigma_one_eq_sigmaOne
#check @ArithmeticFunction.sigma
#check @Nat.totient
#check @Nat.totient_prime_pow
#check @ArithmeticFunction.isMultiplicative_sigma
#check @Nat.ArithmeticFunction.sigma_apply
#check @Nat.sigma_one_eq_sum_divisors

-- is the Nicolas bridge (or its core) already there / provable?
example (n : ℕ) (hn : 2 ≤ n) : Nat.totient n * (∑ d ∈ n.divisors, d) < n ^ 2 := by
  sorry
