/- telperion 0.1.6 | family ExpLaurentDeficit | input-hash 5df1013b28977a78
   2 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace ExpLaurentDeficit

-- THE EXP-LAURENT DEFICIT ROWS (QC_RECURRENCE section 2 row (a), section 4 item 2).
--
-- For an off-line pair at displacement d, the two one-sided clearances are the outer mirror
-- factor e^d - 1 and the inner transported-zero factor 1 - e^(-d).  Their PRODUCT -- the
-- two-sided clearance a recurrence shift must bridge -- is the RECURRENCE DEFICIT, and it
-- equals the Bragg amplification EXCESS e^d + e^(-d) - 2.  The square is the Weil-energy
-- (quadratic-form) reading of the same row.
--
-- Certificate: an exact reduction of lhs - rhs modulo the single relation e^d * e^(-d) = 1,
-- with the quotient (cofactor) carried into `linear_combination`.  Corrupt the cofactor or
-- either side and the kernel rejects the theorem.
--
-- HONEST SCOPE: unconditional, zeta-free bookkeeping between two finite instruments.  It is
-- a dictionary row, not an analytic theorem, and NOT a step toward RH (the uniform Bagchi
-- recurrence IS RH and is untouched).  conjecture1_proved = False.

-- expLaurent_recurrence_deficit: exp-Laurent identity in e^d, e^(-d), certified as an exact
-- reduction modulo the single relation e^d * e^(-d) = 1 with cofactor -1.
-- Unconditional; no enclosure, no analytic hypothesis.  conjecture1_proved = False.
theorem expLaurent_recurrence_deficit (d : ℝ) :
    (Real.exp d - 1) * (1 - Real.exp (-d)) = Real.exp d + Real.exp (-d) - 2 := by
  have hrel : Real.exp d * Real.exp (-d) = 1 := by
    rw [← Real.exp_add]; norm_num
  linear_combination (-1 : ℝ) * hrel

-- expLaurent_recurrence_deficit_sq: exp-Laurent identity in e^d, e^(-d), certified as an exact
-- reduction modulo the single relation e^d * e^(-d) = 1 with cofactor expNeg*expPos - 2*expNeg - 2*expPos + 3.
-- Unconditional; no enclosure, no analytic hypothesis.  conjecture1_proved = False.
theorem expLaurent_recurrence_deficit_sq (d : ℝ) :
    (Real.exp d - 1) ^ 2 * (1 - Real.exp (-d)) ^ 2 = (Real.exp d + Real.exp (-d) - 2) ^ 2 := by
  have hrel : Real.exp d * Real.exp (-d) = 1 := by
    rw [← Real.exp_add]; norm_num
  linear_combination ((Real.exp d * Real.exp (-d)) + 3 - (Real.exp d * 2) - (Real.exp (-d) * 2) : ℝ) * hrel

end ExpLaurentDeficit
