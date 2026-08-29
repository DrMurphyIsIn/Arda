/- Bridge crux, take 2: Re(n^{-(σ+it)}) = n^{-σ} cos(t log n).  Corrected lemma names. -/
import Mathlib
open scoped Real

example (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.exp_re]
  have him : ((↑(Real.log ↑n) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))).im
      = -(t * Real.log n) := by simp; ring
  have hre : ((↑(Real.log ↑n) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = -σ * Real.log n := by simp; ring
  rw [him, hre, Real.cos_neg, Real.exp_mul, Real.exp_log hnpos, Real.rpow_def_of_pos hnpos]
  ring
