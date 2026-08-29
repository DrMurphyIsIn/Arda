/- Bridge crux, take 3: Re(n^{-(σ+it)}) = n^{-σ} cos(t log n).  Explicit re/im + reconcile. -/
import Mathlib
open scoped Real

example (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : ((↑(Real.log (n : ℝ)) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = -σ * Real.log n := by simp [Complex.mul_re]; ring
  have him : ((↑(Real.log (n : ℝ)) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))).im
      = -(t * Real.log n) := by simp [Complex.mul_im]; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.exp_re, hre, him,
      Real.cos_neg, show -σ * Real.log (n : ℝ) = Real.log (n : ℝ) * -σ from by ring,
      ← Real.rpow_def_of_pos hnpos]
