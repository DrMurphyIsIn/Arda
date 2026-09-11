/-
RvMMobius — Phase 4c foundation: iterated derivatives of the Möbius map `1/(1−z)`.

The upstream Li Taylor coefficients are built from `phi f z = f(1/(1−z))`.  Faà di Bruno on the
archimedean composition needs the iterated derivatives of the inner map `M(z) = 1/(1−z)` at `0`.
This file lands the closed form:

  * `iteratedDeriv_mobius` — `iteratedDeriv n (fun w => (1−w)⁻¹) z = n!/(1−z)^(n+1)` (for `z ≠ 1`).
  * `iteratedDeriv_mobius_zero` — `iteratedDeriv n (fun w => (1−w)⁻¹) 0 = n!`.

conjecture1_proved = False.
-/
import Mathlib

open Complex

namespace RvMWeierstrass

/-- **Iterated derivatives of the Möbius map.**  `d^n/dz^n (1−z)⁻¹ = n!/(1−z)^(n+1)` for `z ≠ 1`. -/
theorem iteratedDeriv_mobius (n : ℕ) {z : ℂ} (hz : z ≠ 1) :
    iteratedDeriv n (fun w : ℂ => (1 - w)⁻¹) z = (n.factorial : ℂ) / (1 - z) ^ (n + 1) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hne : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    -- the previous derivative agrees with the closed form on the punctured plane `w ≠ 1`
    have hnbhd : iteratedDeriv n (fun w : ℂ => (1 - w)⁻¹)
        =ᶠ[nhds z] fun w => (n.factorial : ℂ) / (1 - w) ^ (n + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw using ih hw
    rw [Filter.EventuallyEq.deriv_eq hnbhd]
    -- differentiate the closed form
    have hbase : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
    have hval : (n.factorial : ℂ) * (-(↑(n + 1) * (1 - z) ^ n * -1) / ((1 - z) ^ (n + 1)) ^ 2)
        = (((n + 1).factorial : ℕ) : ℂ) / (1 - z) ^ (n + 1 + 1) := by
      have hpow2 : ((1 - z) ^ (n + 1)) ^ 2 = (1 - z) ^ (n + 1 + 1) * (1 - z) ^ n := by
        rw [← pow_add, ← pow_mul]; congr 1; omega
      rw [Nat.factorial_succ, hpow2,
        show -(↑(n + 1) * (1 - z) ^ n * -1) = (↑(n + 1) : ℂ) * (1 - z) ^ n by ring,
        mul_div_mul_right _ _ (pow_ne_zero n hne)]
      push_cast; ring
    have hfun2 : (fun w : ℂ => (n.factorial : ℂ) / (1 - w) ^ (n + 1))
        = fun w : ℂ => (n.factorial : ℂ) * ((1 - w) ^ (n + 1))⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    have hd : HasDerivAt (fun w : ℂ => (n.factorial : ℂ) / (1 - w) ^ (n + 1))
        ((n.factorial : ℂ) * (-(↑(n + 1) * (1 - z) ^ n * -1) / ((1 - z) ^ (n + 1)) ^ 2)) z := by
      rw [hfun2]
      exact ((hbase.pow (n + 1)).inv (pow_ne_zero _ hne)).const_mul (n.factorial : ℂ)
    rw [hd.deriv, hval]

/-- `iteratedDeriv n (fun w => (1−w)⁻¹) 0 = n!` — the Möbius derivatives at the Taylor base point. -/
theorem iteratedDeriv_mobius_zero (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => (1 - w)⁻¹) 0 = (n.factorial : ℂ) := by
  rw [iteratedDeriv_mobius n (by norm_num)]; simp

end RvMWeierstrass
