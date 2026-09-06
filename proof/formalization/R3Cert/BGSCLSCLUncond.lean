import R3Cert.BGSCLHub
import R3Cert.BGSCLSubactionDispatch

/-!
  # The single-child lemma (SCL), now UNCONDITIONAL.

  The classical-branch ceiling `bg_ceiling : ∀ b, bell b ≤ 0` was closed unconditionally via the
  additive subaction (`isSubaction_ρwit`, `BGSCLSubactionDispatch.lean`).  The bridge
  `scl_of_ceiling : (∀ b, bell b ≤ 0) → ∀ b, PSCLne b` (`BGSCLHub.lean`) was already proven modulo
  that ceiling hypothesis.  Feeding `bg_ceiling` into it discharges the ceiling hypothesis and makes
  the single-child lemma (`PSCLne b`: for a non-leaf `b`, `bV μ b ≤ bV μ cherry` on the price
  interval `I`) an UNCONDITIONAL theorem.  This discharges the long-open `HYPOTHESIS(b)` / SCL
  induction of the BG asymptotic upper-bound program.

  This is the SCL leg of the BG upper bound `F(T) ≤ F*`; it does NOT by itself prove `conjecture1`
  (the finite-`n` Laplacian maximizer, which reduces to the still-open `Hnorm`/`Hdom` layers).
  `conjecture1_proved = False`.
-/

namespace R3Cert
namespace BGSCL

/-- **The single-child lemma, unconditional.**  `scl_of_ceiling` applied to the now-proven ceiling
    `bg_ceiling`.  For every non-leaf branch `b` and every price `μ ∈ I`, `bV μ b ≤ bV μ cherry`. -/
theorem scl_holds_uncond : ∀ b, PSCLne b := scl_of_ceiling bg_ceiling

end BGSCL
end R3Cert
