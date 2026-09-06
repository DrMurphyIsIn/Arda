/- HYPERBOLICITY BRIDGE (d=2): a real quadratic with nonzero leading coefficient
   and a NONNEGATIVE discriminant is real-rooted -- its `roots` multiset has card 2.
   This is the degree-2 generalization of the Jensen zero-count bridge; it is the
   prelude lemma the `hyperbolicity` emitter (#3) chains a box-robust discriminant
   nonnegativity fact into.  Proven fresh here (sorry-free), imports Mathlib only.
   conjecture1_proved = False. -/
import Mathlib

open Polynomial

/-- A real quadratic `a X^2 + b X + c` with `a ≠ 0` and discriminant `b^2 - 4 a c ≥ 0`
    has exactly two real roots (counted with multiplicity): its `roots` multiset has
    cardinality 2.  The double-root case (discriminant 0) is handled by the multiset
    carrying the root twice. -/
theorem hyperbolic_deg2_of_discrim_nonneg (a b c : ℝ) (ha : a ≠ 0)
    (h : 0 ≤ b ^ 2 - 4 * a * c) :
    (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X
      + Polynomial.C c).roots.card = 2 := by
  -- The two real roots via the quadratic formula.
  set s : ℝ := Real.sqrt (b ^ 2 - 4 * a * c) with hs
  have hs2 : s ^ 2 = b ^ 2 - 4 * a * c := by
    rw [hs, sq, Real.mul_self_sqrt h]
  set r1 : ℝ := (-b + s) / (2 * a) with hr1
  set r2 : ℝ := (-b - s) / (2 * a) with hr2
  have h2a : (2 * a) ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha
  -- Vieta identities over ℝ: a·(r1+r2) = -b and a·(r1·r2) = c.
  have hsum : a * (r1 + r2) = -b := by
    rw [hr1, hr2]; field_simp; ring
  have hprod : a * (r1 * r2) = c := by
    rw [hr1, hr2, div_mul_div_comm,
      show (-b + s) * (-b - s) = b ^ 2 - s ^ 2 by ring, hs2,
      show (2 * a) * (2 * a) = 4 * a ^ 2 by ring]
    field_simp
    ring
  -- Factorization over ℝ[X]: everything stays inside the polynomial ring via `C`.
  have hfactor :
      Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c
        = Polynomial.C a * ((Polynomial.X - Polynomial.C r1)
            * (Polynomial.X - Polynomial.C r2)) := by
    have hb : Polynomial.C b = Polynomial.C (a * (-(r1 + r2))) := by
      rw [show a * (-(r1 + r2)) = -(a * (r1 + r2)) by ring, hsum]; ring_nf
    have hc : Polynomial.C c = Polynomial.C (a * (r1 * r2)) := by rw [hprod]
    rw [hb, hc]
    simp only [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_add]
    ring
  rw [hfactor]
  -- Count roots of C a * ((X - C r1) * (X - C r2)).
  rw [Polynomial.roots_C_mul _ ha]
  rw [Polynomial.roots_mul, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  · simp
  · -- (X - C r1) * (X - C r2) ≠ 0
    apply mul_ne_zero <;> exact Polynomial.X_sub_C_ne_zero _
