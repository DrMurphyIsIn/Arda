/-
Jensen-Polya hyperbolicity: d=2 bridge lemma.

A real quadratic `a X^2 + b X + c` (a != 0) with nonnegative discriminant
`b^2 - 4 a c >= 0` is hyperbolic: its real-root multiset has cardinality 2,
which equals its degree. This is the reusable per-degree hyperbolicity bridge
consumed by the higher-degree Jensen-Polya tasks.

conjecture1_proved = False. This lemma is a rigorous but narrow building block
(the d=2 base case of the hyperbolicity ladder), not a proof of RH.
-/
import Mathlib

open Polynomial

theorem hyperbolic_deg2_of_discrim_nonneg (a b c : ℝ) (ha : a ≠ 0)
    (h : 0 ≤ b^2 - 4*a*c) :
    (Polynomial.C a * Polynomial.X^2 + Polynomial.C b * Polynomial.X + Polynomial.C c).roots.card = 2 := by
  -- s is the square root of the discriminant; s^2 = b^2 - 4ac.
  set s : ℝ := Real.sqrt (b^2 - 4*a*c) with hs_def
  have hs_sq : s * s = b^2 - 4*a*c := Real.mul_self_sqrt h
  -- The two real roots.
  set r1 : ℝ := (-b + s) / (2*a) with hr1_def
  set r2 : ℝ := (-b - s) / (2*a) with hr2_def
  have h2a : (2*a) ≠ 0 := by
    intro hc
    exact ha (by linarith [mul_eq_zero.mp hc |>.resolve_left (by norm_num)])
  -- Scalar identities: a*(r1+r2) = -b and a*(r1*r2) = c.
  have hsum : a * (r1 + r2) = -b := by
    rw [hr1_def, hr2_def]
    field_simp
    ring
  have hprod : a * (r1 * r2) = c := by
    rw [hr1_def, hr2_def, div_mul_div_comm]
    rw [show (-b + s) * (-b - s) = b^2 - s*s by ring, hs_sq]
    field_simp
    ring
  -- Factorization of the quadratic.
  have hfactor :
      (Polynomial.C a * Polynomial.X^2 + Polynomial.C b * Polynomial.X + Polynomial.C c)
        = Polynomial.C a * ((Polynomial.X - Polynomial.C r1) * (Polynomial.X - Polynomial.C r2)) := by
    have hb : Polynomial.C b = - Polynomial.C (a * (r1 + r2)) := by
      rw [hsum]; simp
    have hc : Polynomial.C c = Polynomial.C (a * (r1 * r2)) := by rw [hprod]
    rw [hb, hc]
    push_cast [Polynomial.C_mul, Polynomial.C_add]
    ring
  rw [hfactor]
  -- Compute the roots of the factored form.
  have hne1 : (Polynomial.X - Polynomial.C r1) ≠ (0 : ℝ[X]) := Polynomial.X_sub_C_ne_zero r1
  have hne2 : (Polynomial.X - Polynomial.C r2) ≠ (0 : ℝ[X]) := Polynomial.X_sub_C_ne_zero r2
  rw [Polynomial.roots_C_mul _ ha,
      Polynomial.roots_mul (mul_ne_zero hne1 hne2),
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  -- {r1} + {r2} has cardinality 2.
  simp

-- Kernel-clean check: expect only [propext, Classical.choice, Quot.sound].
#print axioms hyperbolic_deg2_of_discrim_nonneg
