/-
OrdinateInsensitivity — the kernel guardrail from support-side sweep wryhnwohw.

The completed-zeta zero set is SYMMETRIC ABOUT THE CRITICAL LINE (functional equation
Λ(1−s) = Λ(s)): every zero ρ has a partner 1−ρ with real part 1 − Re ρ. So off-line
zeros (Re ≠ 1/2) come in reflected pairs {β, 1−β} straddling the line — and any
symmetric statistic of the zero set (e.g. the ordinate count S(t)) is BLIND to
off-line location. This is the formal seed of OrdinateInsensitivity: the survivor
foothold (Selberg's second moment) pins WHERE the missing idea must act; it does not
act there.

conjecture1_proved = False. A diagnostic guardrail, NOT an RH route.
-/
import Mathlib

open Complex

namespace OrdinateInsensitivity

/-- **Reflection symmetry of the completed-zeta zero set** (functional equation
`Λ(1−s) = Λ(s)`): `ρ` is a zero iff `1 − ρ` is. -/
theorem completedZeta_zero_reflect (ρ : ℂ) :
    completedRiemannZeta ρ = 0 ↔ completedRiemannZeta (1 - ρ) = 0 := by
  rw [completedRiemannZeta_one_sub]

/-- **The reflected partner.**  Every completed-zeta zero `ρ` has a zero at `1 − ρ`,
whose real part is `1 − Re ρ`.  Off-line zeros therefore come in pairs straddling the
critical line — the symmetry that makes reality a "both-or-neither-at-½" statement and
renders symmetric (ordinate) statistics blind to off-line location. -/
theorem zero_reflected_partner (ρ : ℂ) (hρ : completedRiemannZeta ρ = 0) :
    completedRiemannZeta (1 - ρ) = 0 ∧ (1 - ρ).re = 1 - ρ.re :=
  ⟨(completedZeta_zero_reflect ρ).mp hρ, by simp⟩

/-- **Off-line zeros are genuinely off-line in pairs.**  If a completed-zeta zero `ρ`
is off the critical line, its reflected partner `1 − ρ` is a DISTINCT zero, also off
the line (at the mirrored real part `1 − Re ρ`).  So off-line-ness is never solitary —
exactly the obstruction that keeps the ordinate-side foothold from reaching the wall. -/
theorem offline_zero_has_distinct_partner (ρ : ℂ) (hρ : completedRiemannZeta ρ = 0)
    (hoff : ρ.re ≠ 1 / 2) :
    completedRiemannZeta (1 - ρ) = 0 ∧ (1 - ρ) ≠ ρ ∧ (1 - ρ).re ≠ 1 / 2 := by
  refine ⟨(completedZeta_zero_reflect ρ).mp hρ, ?_, ?_⟩
  · intro h
    apply hoff
    have : (1 - ρ).re = ρ.re := by rw [h]
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  · simp only [Complex.sub_re, Complex.one_re]
    intro h
    apply hoff
    linarith

/-- **Conjugation symmetry of the zeta zero set** (Schwarz reflection
`ζ(conj s) = conj(ζ s)`): `ρ` is a zero iff `conj ρ` is — a distinct zero at the SAME
real part and the OPPOSITE ordinate.  Combined with the functional-equation reflection
above, the nontrivial zeros come in quadruples `(ρ, 1−ρ, conj ρ, 1−conj ρ)`, and the pair
`(ρ, 1−conj ρ)` sits at the SAME ordinate with mirrored real parts `{β, 1−β}` — the
precise structure that keeps any reflection-invariant real-part functional from ever
separating an on-line zero from an off-line pair. -/
theorem riemannZeta_zero_conj (ρ : ℂ) (hρ : riemannZeta ρ = 0) :
    riemannZeta (starRingEnd ℂ ρ) = 0
      ∧ (starRingEnd ℂ ρ).re = ρ.re ∧ (starRingEnd ℂ ρ).im = -ρ.im := by
  refine ⟨?_, by simp, by simp⟩
  rw [riemannZeta_conj, hρ, map_zero]

end OrdinateInsensitivity

#print axioms OrdinateInsensitivity.completedZeta_zero_reflect
#print axioms OrdinateInsensitivity.zero_reflected_partner
#print axioms OrdinateInsensitivity.offline_zero_has_distinct_partner
#print axioms OrdinateInsensitivity.riemannZeta_zero_conj
