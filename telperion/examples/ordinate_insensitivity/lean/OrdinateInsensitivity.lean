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

open Complex Real

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

/-- Gammaℝ commutes with complex conjugation (Mathlib-gap lemma). -/
theorem Gammaℝ_conj (s : ℂ) :
    Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Gammaℝ s) := by
  have hπ : (↑π : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
  simp only [Gammaℝ_def, map_mul]
  congr 1
  · rw [show -(starRingEnd ℂ s) / 2 = starRingEnd ℂ (-s / 2) by
        simp [map_div₀, map_neg, map_ofNat]]
    rw [Complex.cpow_conj (↑π) (-s / 2) hπ, Complex.conj_ofReal]
  · rw [show starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) by simp [map_div₀, map_ofNat]]
    exact Complex.Gamma_conj (s / 2)

/-- **Completed-zeta conjugation** where the archimedean factor is nonzero (covers every
nontrivial zero): `Λ(conj s) = conj(Λ s)`. -/
theorem completedRiemannZeta_conj_ne (s : ℂ) (hs : s ≠ 0)
    (hΓ : Gammaℝ (starRingEnd ℂ s) ≠ 0) :
    completedRiemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta s) := by
  have hcs : starRingEnd ℂ s ≠ 0 := by simpa using hs
  have h1 : riemannZeta (starRingEnd ℂ s)
      = completedRiemannZeta (starRingEnd ℂ s) / Gammaℝ (starRingEnd ℂ s) :=
    riemannZeta_def_of_ne_zero hcs
  have h2 : riemannZeta (starRingEnd ℂ s)
      = starRingEnd ℂ (completedRiemannZeta s) / Gammaℝ (starRingEnd ℂ s) := by
    rw [riemannZeta_conj, riemannZeta_def_of_ne_zero hs, map_div₀, Gammaℝ_conj]
  have e : completedRiemannZeta (starRingEnd ℂ s) / Gammaℝ (starRingEnd ℂ s)
      = starRingEnd ℂ (completedRiemannZeta s) / Gammaℝ (starRingEnd ℂ s) := h1 ▸ h2
  field_simp [hΓ] at e
  exact e

/-- **Same-ordinate partner** — the sharp reflection-trilogy statement.  A nontrivial
completed-zeta zero `ρ` has a zero at `1 - conj ρ`, at the SAME ordinate (`Im = ρ.im`) with
mirrored real part (`1 - ρ.re`).  So an off-line zero has an off-line partner at the identical
height — precisely why a reflection-invariant ordinate statistic (Selberg's `S(t)` second
moment) can never separate an on-line zero from an off-line pair.  conjecture1_proved = False. -/
theorem same_ordinate_partner (ρ : ℂ) (hρ : completedRiemannZeta ρ = 0)
    (hs : ρ ≠ 0) (hΓ : Gammaℝ (starRingEnd ℂ ρ) ≠ 0) :
    completedRiemannZeta (1 - starRingEnd ℂ ρ) = 0
      ∧ (1 - starRingEnd ℂ ρ).im = ρ.im
      ∧ (1 - starRingEnd ℂ ρ).re = 1 - ρ.re := by
  have hconj : completedRiemannZeta (starRingEnd ℂ ρ) = 0 := by
    rw [completedRiemannZeta_conj_ne ρ hs hΓ, hρ, map_zero]
  refine ⟨?_, by simp, by simp⟩
  rw [completedRiemannZeta_one_sub]; exact hconj

end OrdinateInsensitivity

#print axioms OrdinateInsensitivity.completedZeta_zero_reflect
#print axioms OrdinateInsensitivity.zero_reflected_partner
#print axioms OrdinateInsensitivity.offline_zero_has_distinct_partner
#print axioms OrdinateInsensitivity.riemannZeta_zero_conj
#print axioms OrdinateInsensitivity.Gammaℝ_conj
#print axioms OrdinateInsensitivity.completedRiemannZeta_conj_ne
#print axioms OrdinateInsensitivity.same_ordinate_partner
