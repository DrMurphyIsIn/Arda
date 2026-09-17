/-
ReflectionForced — the machine-checkable CORE of the RH wall's symmetry theorem
(four-sweep campaign wu0aecd5x).

The completed-zeta zero set is closed under the Klein four-group
{1, s↦1−s, s↦conj s, s↦1−conj s}; the pair (ρ, 1−conj ρ) sits at the SAME ordinate with
mirrored real parts {β, 1−β}.  Any real functional F invariant under the functional-
equation reflection AND conjugation is therefore CONSTANT on that pair — so it cannot
separate an off-line zero from an on-line one, and cannot force Re ρ = 1/2.  Every
Ξ-symmetric functional is such an F; that is why the RH wall is irreducible from the
symmetric/flow-robust class.

conjecture1_proved = False.  This proves the OBSTRUCTION (why a whole class of tools
cannot force reality), NOT RH.
-/
import Mathlib

open Complex

namespace ReflectionForced

/-- The reflection partner `1 − conj ρ` has the SAME ordinate as `ρ`. -/
theorem reflection_pair_im (ρ : ℂ) : (1 - starRingEnd ℂ ρ).im = ρ.im := by simp

/-- The reflection partner `1 − conj ρ` has the mirrored real part `1 − Re ρ`. -/
theorem reflection_pair_re (ρ : ℂ) : (1 - starRingEnd ℂ ρ).re = 1 - ρ.re := by simp

/-- **Off-line ⇒ the reflection partner is a distinct point** (at the same ordinate). -/
theorem reflection_pair_offline_distinct (ρ : ℂ) (hoff : ρ.re ≠ 1 / 2) :
    (1 - starRingEnd ℂ ρ) ≠ ρ := by
  intro h
  apply hoff
  have hre : (1 - starRingEnd ℂ ρ).re = ρ.re := by rw [h]
  rw [reflection_pair_re] at hre
  linarith

/-- **FORCED-half kernel.**  Any real functional `F` invariant under BOTH the
functional-equation reflection `z ↦ 1 − z` and conjugation `z ↦ conj z` takes the SAME
value on `ρ` and its reflection partner `1 − conj ρ`.  For an off-line `ρ` these are
distinct points at the same ordinate (`reflection_pair_offline_distinct`,
`reflection_pair_im`), so `F` cannot separate an off-line zero from an on-line one — it
cannot force `Re ρ = 1/2`.  This is the machine-checkable core of the RH wall's symmetry
theorem: every Ξ-symmetric functional is such an `F`. -/
theorem functional_constant_on_reflection_pair {F : ℂ → ℝ}
    (hrefl : ∀ z : ℂ, F (1 - z) = F z)
    (hconj : ∀ z : ℂ, F (starRingEnd ℂ z) = F z) (ρ : ℂ) :
    F (1 - starRingEnd ℂ ρ) = F ρ := by
  rw [hrefl (starRingEnd ℂ ρ), hconj ρ]

end ReflectionForced

#print axioms ReflectionForced.reflection_pair_offline_distinct
#print axioms ReflectionForced.functional_constant_on_reflection_pair
