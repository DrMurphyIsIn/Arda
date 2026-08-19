import Mathlib

/-!
  # Arms+ties skeleton: the tie-monotonicity (parallel crux session, 2026-08-19)

  For a hub of `p` arms (message `1/3`) and `q` ties (message `3/23`), adding a
  tie DECREASES the hub amplitude `a_hub` whenever `p ≥ 1` — so the whole
  arms+ties family is bounded by its pure-arm boundary `F_ns(p)` (the near-star
  family, a separate proven brick) and its pure-tie boundary (`family_martingale`).
  This file kernel-checks the monotonicity, the mechanism of that reduction, by
  the exact telescoping identity

      a(p,q) - a(p,q+1) = (14p - 9) / (69 (p+q+1)(p+q+2)) ≥ 0  ⟺  p ≥ 1.

  Entirely rational.  HONEST SCOPE: this is ONE lemma of the arms+ties extremal
  skeleton, itself the boundary of the OPEN near-star half of the BG closure
  step; the master inequality (general child ≤ arm/tie extreme) is the
  irreducible arithmetic core and remains open.  conjecture1_proved = False.
-/

namespace R3Cert
namespace ArmsTies

/-- Hub amplitude for `p` arms (message `1/3`) and `q` ties (message `3/23`). -/
def aHubAT (p q : ℕ) : ℚ := 1 + ((p : ℚ) / 3 + 3 * q / 23) / ((p : ℚ) + q + 1)

/-- **Tie-monotonicity**: for `p ≥ 1`, attaching one more tie does not increase
    the hub amplitude — the telescoping deficit `(14p-9)/(69(j+1)(j+2)) ≥ 0`. -/
theorem aHubAT_add_tie_le (p q : ℕ) (hp : 1 ≤ p) : aHubAT p (q + 1) ≤ aHubAT p q := by
  have hp' : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  simp only [aHubAT]
  push_cast
  rw [← sub_nonneg]
  have key : (1 + ((p : ℚ) / 3 + 3 * (q : ℚ) / 23) / ((p : ℚ) + q + 1))
      - (1 + ((p : ℚ) / 3 + 3 * ((q : ℚ) + 1) / 23) / ((p : ℚ) + (q + 1) + 1))
      = (14 * (p : ℚ) - 9) / (69 * ((p : ℚ) + q + 1) * ((p : ℚ) + q + 2)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg (by linarith) (by positivity)

end ArmsTies
end R3Cert
