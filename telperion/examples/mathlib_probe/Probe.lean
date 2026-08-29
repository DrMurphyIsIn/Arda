/- Bridge crux: Re(n^{-(σ+it)}) = n^{-σ} cos(t log n).  If this closes, the 3-4-1
   certificate->zeta inequality assembles; if not, the region is a deeper grind. -/
import Mathlib
open scoped Real

#check @Complex.cpow_def_of_ne_zero
#check @Complex.exp_re
#check @Complex.natCast_log
#check @Complex.cpow_natCast

example (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.exp_re]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.log_ofReal_of_pos (by exact_mod_cast hn)]
  rw [hlog]
  simp [Complex.exp_re, Complex.exp_im, mul_comm, mul_assoc, Real.rpow_natCast]
  ring_nf
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn)]
  ring_nf
