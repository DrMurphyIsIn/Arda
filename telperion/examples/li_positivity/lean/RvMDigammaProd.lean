/-
RvMDigammaProd — Phase 2 brick 3 (the crux): the Weierstrass product equals 1/Γ.

Building on the convergence (RvMWeierstrass), this pins the constant `e^{γs}` by relating the partial
product to Mathlib's `GammaSeq` (the Gauss/Euler limit for Γ) and the Euler–Mascheroni limit
`harmonic n - log n → γ`.  This is the step that identifies the abstract product with `1/Γ`.

This file (b3 sub-brick 1): the CORE finite product identity
  `s · ∏_{n<N} (1 + s/(n+1)) = (∏_{j<N+1} (s+j)) / N!`
— pure finite algebra, the combinatorial heart of the GammaSeq relation.

conjecture1_proved = False.
-/
import Mathlib
import RvMWeierstrass

open Complex

namespace RvMWeierstrass

/-- **Core finite product identity.**  `s · ∏_{n<N} (1 + s/(n+1)) = (∏_{j<N+1} (s+j)) / N!`.
    Pure finite algebra: each factor `1+s/(n+1) = (s+n+1)/(n+1)`, the denominators multiply to `N!`,
    and peeling the `j=0` factor of `∏_{j<N+1}(s+j)` yields the `s·` prefactor. -/
theorem core_prod_identity (s : ℂ) (N : ℕ) :
    s * (∏ n ∈ Finset.range N, (1 + s / ((n : ℂ) + 1)))
      = (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ))) / ((Nat.factorial N : ℕ) : ℂ) := by
  -- rewrite each factor `1 + s/(n+1) = (s + (n+1))/(n+1)`
  have hfactor : (∏ n ∈ Finset.range N, (1 + s / ((n : ℂ) + 1)))
      = (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1)))
          / (∏ n ∈ Finset.range N, ((n : ℂ) + 1)) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun n _ => ?_)
    have h := natCast_add_one_ne_zero n
    field_simp
    ring
  -- the denominator product is N!
  have hfact : (∏ n ∈ Finset.range N, ((n : ℂ) + 1)) = ((Nat.factorial N : ℕ) : ℂ) := by
    calc (∏ n ∈ Finset.range N, ((n : ℂ) + 1))
        = ∏ n ∈ Finset.range N, (((n + 1 : ℕ)) : ℂ) := by
          refine Finset.prod_congr rfl (fun n _ => ?_); push_cast; ring
      _ = (((∏ n ∈ Finset.range N, (n + 1)) : ℕ) : ℂ) := by rw [Nat.cast_prod]
      _ = ((Nat.factorial N : ℕ) : ℂ) := by rw [Finset.prod_range_add_one_eq_factorial]
  -- peel the j=0 factor of ∏_{j<N+1}(s+j)
  have hpeel : (∏ j ∈ Finset.range (N + 1), (s + (j : ℂ)))
      = (∏ n ∈ Finset.range N, (s + ((n : ℂ) + 1))) * s := by
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [hfactor, hfact, hpeel]
  ring

end RvMWeierstrass
