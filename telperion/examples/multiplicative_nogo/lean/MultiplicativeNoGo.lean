/-
MultiplicativeNoGo — the kernel-verified guardrail from adversarial search wylptmzxv.

The multiplicative-rigidity seed (completely-multiplicative diffraction intensities
substitute for uniform discreteness as the reality-forcing hypothesis) was REFUTED
across six angles (clean negative). Its formal heart: the zeta comb's Bragg amplitude
IS von Mangoldt Λ, and Λ is NOT completely multiplicative — Λ(2·3)=Λ(6)=0 (6 is not a
prime power) while Λ(2)·Λ(3)=log2·log3≠0. So a completely-multiplicative amplitude
describes a DIFFERENT measure than the actual Λ-comb; the substitution cannot start.

This is a PERMANENT ANTI-OVERCLAIM GUARDRAIL, not an RH route.
conjecture1_proved = False.
-/
import Mathlib

open ArithmeticFunction

namespace MultiplicativeNoGo

/-- Von Mangoldt Λ (the zeta comb's Bragg amplitude) is **not completely
multiplicative**: it fails at `2 · 3`.  Any "completely-multiplicative-amplitude
forces reality" hypothesis therefore describes a different measure than the actual
Λ-comb — the multiplicative-substitution seed cannot even begin on the zeta comb. -/
theorem not_completelyMultiplicative_vonMangoldt :
    ¬ (∀ m n : ℕ, Λ (m * n) = Λ m * Λ n) := by
  intro h
  have key := h 2 3
  rw [vonMangoldt_apply_prime (by norm_num : Nat.Prime 2),
      vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)] at key
  have hz : Λ (2 * 3 : ℕ) = 0 := by
    rw [vonMangoldt_apply, if_neg (by decide)]
  rw [hz] at key
  push_cast at key
  have hpos : (0 : ℝ) < Real.log 2 * Real.log 3 :=
    mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  linarith [key, hpos]

end MultiplicativeNoGo

#print axioms MultiplicativeNoGo.not_completelyMultiplicative_vonMangoldt
