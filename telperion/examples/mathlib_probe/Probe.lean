/- Mathlib v4.32.0 probe #4: tools to LAND a genuine zeta-numerics lemma
   (bound zeta(3), no closed form, via the convergent Dirichlet series + a tail
   bound).  `#check @foo` types what exists; errors name what does not. -/
import Mathlib
open scoped Real

-- the Dirichlet series representation for Re(s) > 1
#check @riemannZeta_eq_tsum_one_div_nat_cpow
#check @riemannZeta_eq_tsum_one_div_nat_add_one_cpow
#check @zeta_eq_tsum_one_div_nat_cpow
#check @riemannZeta_two
#check @riemannZeta_four

-- summability of 1/n^k
#check @Real.summable_one_div_nat_rpow
#check @Real.summable_one_div_nat_pow
#check @summable_one_div_nat_cpow

-- partial-sum <= tsum, and tail control
#check @sum_le_tsum
#check @tsum_eq_sum_add_tsum_nat_add
#check @tsum_le_tsum
#check @tsum_lt_tsum

-- telescoping helper for the tail bound sum 1/n^3 <= sum 1/((n-1)n(n+1))
#check @tsum_geometric_of_lt_one
#check @Finset.sum_range_succ

-- Complex re / of the zeta value (zeta 3 is Complex; need to bound its re)
#check @Complex.re
#check @riemannZeta_ofReal
