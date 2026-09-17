/-
FamilyReflectionBlind — the AGGREGATE half of the RH-wall symmetry theorem.

Companion to ReflectionForced (the pointwise FORCED-half). Where that file shows a
reflection-invariant *pointwise* functional is constant on the pair (ρ, 1−conj ρ), this
file shows the *aggregate* analogue: any symmetric statistic (a real functional of the
zero MULTISET) is blind to reflecting a member, because the reflection ρ ↦ 1−conj ρ is an
involution and the minimal reflection-closed family {ρ, 1−conj ρ} is fixed by it. This is
the kernel core of the campaign's "aggregate / family-average" collapse mode (sweeps
wryhnwohw ordinate + wcrkqbzrj odd-kernel to family-average): one-level and n-level
densities and every symmetric zero statistic see the pair identically, cannot force reality.

conjecture1_proved = False.  Proves the OBSTRUCTION, not RH.
-/
import Mathlib

open Complex

namespace FamilyReflectionBlind

/-- The functional-equation × conjugation reflection `ρ ↦ 1 − conj ρ`
(same ordinate, mirrored real part). -/
def refl (ρ : ℂ) : ℂ := 1 - starRingEnd ℂ ρ

/-- **The reflection is an involution**: `refl (refl ρ) = ρ`. -/
theorem refl_involutive : Function.Involutive refl := by
  intro ρ
  simp [refl]

/-- **The reflection preserves the ordinate and mirrors the real part.** -/
theorem refl_re (ρ : ℂ) : (refl ρ).re = 1 - ρ.re := by simp [refl]

theorem refl_im (ρ : ℂ) : (refl ρ).im = ρ.im := by simp [refl]

/-- **The minimal reflection-closed family is the pair.**  Mapping `refl` over the
2-element multiset `{ρ, refl ρ}` returns the same multiset (it swaps the two entries,
which a multiset does not distinguish). -/
theorem reflectionPair_closed (ρ : ℂ) :
    ({ρ, refl ρ} : Multiset ℂ).map refl = {ρ, refl ρ} := by
  show (refl ρ ::ₘ refl (refl ρ) ::ₘ (0 : Multiset ℂ)) = ρ ::ₘ refl ρ ::ₘ 0
  rw [refl_involutive ρ]
  exact Multiset.cons_swap _ _ _

/-- **Aggregate statistics are reflection-blind.**  Any real functional `Φ` of the zero
MULTISET takes the same value on a reflection-closed family and its member-wise reflection.
For the minimal off-line unit `{ρ, refl ρ}` this says `Φ` cannot tell the family from its
mirror image — it cannot single out `Re ρ = 1/2`. -/
theorem symmetric_stat_reflection_blind (Φ : Multiset ℂ → ℝ) {S : Multiset ℂ}
    (hS : S.map refl = S) : Φ (S.map refl) = Φ S := by rw [hS]

/-- Instantiated at the minimal reflection-closed unit. -/
theorem reflectionPair_stat_blind (Φ : Multiset ℂ → ℝ) (ρ : ℂ) :
    Φ (({ρ, refl ρ} : Multiset ℂ).map refl) = Φ {ρ, refl ρ} :=
  symmetric_stat_reflection_blind Φ (reflectionPair_closed ρ)

/-- **Off-line ⇒ the pair is genuinely two distinct points** (same ordinate).  So the
aggregate blindness above is not vacuous: it identifies a 2-element family straddling the
critical line that no symmetric statistic can resolve. -/
theorem reflectionPair_offline_distinct (ρ : ℂ) (hoff : ρ.re ≠ 1 / 2) : refl ρ ≠ ρ := by
  intro h
  apply hoff
  have hre : (refl ρ).re = ρ.re := by rw [h]
  rw [refl_re] at hre
  linarith

end FamilyReflectionBlind

#print axioms FamilyReflectionBlind.refl_involutive
#print axioms FamilyReflectionBlind.reflectionPair_closed
#print axioms FamilyReflectionBlind.symmetric_stat_reflection_blind
#print axioms FamilyReflectionBlind.reflectionPair_stat_blind
#print axioms FamilyReflectionBlind.reflectionPair_offline_distinct
