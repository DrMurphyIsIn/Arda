/-
  WallBarrierAM.lean -- the symmetry barrier, sharply scoped.

  BARRIER RESEARCH, branch wall/barrier, 2026-09-18.  conjecture1_proved = False.

  The four-sweep wall campaign (telperion/docs/RH_WALL_SYMMETRY_THEOREM_2026-09-16.md)
  concluded "the RH wall is a symmetry theorem": any functional built from the completed
  zeta and complex conjugation is invariant under the functional-equation reflection
  rho -> 1 - conj rho, hence "cannot separate an on-line zero from an off-line pair".

  This file states and PROVES that dichotomy in its sharpest general form -- for an
  ARBITRARY reflection-invariant map into an ARBITRARY type, not merely for functionals
  built out of Xi -- and it proves the SCOPE LIMIT, which is the point of the file:

    * no_invariant_orients  (FORCED, generalized): a reflection-invariant instrument
      cannot decide WHICH SIDE of the critical line a point lies on.  This holds for
      every output type and every decision rule, so it covers every instrument the
      program builds whose soundness proof is uniform in the reflection.

    * invariant_detects     (DETECT, and the scope limit): a reflection-invariant
      functional that decides ON-LINE-NESS exactly DOES exist.  The Riemann Hypothesis
      is the assertion that no zero is off the line -- a reflection-INVARIANT predicate
      (onLine_reflect).  Therefore reflection invariance is provably NOT an obstruction
      to RH.  The symmetry theorem is a barrier against ORIENTATION only.

  Read together: "the RH wall is a symmetry theorem" is TRUE for orientation and FALSE
  for RH.  Any barrier claim that upgrades FORCED into an obstruction to RH itself
  proves too much and is refuted by `invariant_detects`.

  Nothing here is progress on RH.
-/
import Mathlib

namespace WallBarrierAM

open Complex

/-! ### The functional-equation reflection -/

/-- The functional-equation reflection on the zero set: `rho -> 1 - conj rho`.  Together
with `s -> 1 - s` and `s -> conj s` it generates the Klein four-group that the zero
multiset of a self-dual completed L-function is closed under. -/
noncomputable def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

@[simp] lemma reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by
  simp [reflect]

@[simp] lemma reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by
  simp [reflect]

lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  apply Complex.ext <;> simp

lemma reflect_involutive : Function.Involutive reflect := reflect_reflect

/-- On the critical line. -/
def OnLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- The RH predicate is reflection-INVARIANT: the reflection maps the line to itself. -/
@[simp] lemma onLine_reflect (ρ : ℂ) : OnLine (reflect ρ) ↔ OnLine ρ := by
  constructor <;> · intro h; simp only [OnLine, reflect_re] at *; linarith

/-! ### FORCED, in full generality -/

/-- **FORCED (generalized).**  Let `F` be ANY map from the complex plane to ANY type that
is invariant under the functional-equation reflection, and let `dec` be ANY decision rule
on its values.  Then `dec (F rho)` cannot agree with "`rho` lies strictly right of the
critical line" at every off-line point.

This is the wall campaign's FORCED half with the hypothesis "built out of `Xi` and
conjugation" replaced by the only property that proof ever used: reflection invariance.
The witness pair is `(0, 1)`: `reflect 0 = 1`, so any invariant instrument assigns them
the same value, while they sit on opposite sides of the line. -/
theorem no_invariant_orients {α : Type*} (F : ℂ → α) (hF : ∀ ρ, F (reflect ρ) = F ρ)
    (dec : α → Prop) :
    ¬ (∀ ρ : ℂ, ρ.re ≠ 1 / 2 → (dec (F ρ) ↔ 1 / 2 < ρ.re)) := by
  intro h
  have h0 : ((0 : ℂ)).re ≠ 1 / 2 := by norm_num
  have h1 : (reflect (0 : ℂ)).re ≠ 1 / 2 := by simp
  have e0 := h 0 h0
  have e1 := h (reflect 0) h1
  rw [hF] at e1
  have hnot : ¬ dec (F 0) := by
    intro hd
    have := e0.mp hd
    simp at this
    linarith
  exact hnot (e1.mpr (by simp; norm_num))

/-! ### DETECT, and the scope limit -/

/-- **DETECT (the scope limit).**  There IS a reflection-invariant real functional whose
vanishing is exactly membership of the critical line.  Consequently reflection invariance
is provably NOT an obstruction to the Riemann Hypothesis: RH is a reflection-invariant
predicate (`onLine_reflect`), and invariant instruments can express invariant predicates.

The witness is the invariant pair coordinate `|Re rho - 1/2|`, the same quantity the wall
campaign's DETECT half reads off the pair weight `2 cosh((beta - 1/2) log x)`. -/
theorem invariant_detects :
    ∃ F : ℂ → ℝ, (∀ ρ, F (reflect ρ) = F ρ) ∧ (∀ ρ, F ρ = 0 ↔ OnLine ρ) := by
  refine ⟨fun ρ => |ρ.re - 1 / 2|, ?_, ?_⟩
  · intro ρ
    simp only [reflect_re]
    rw [show (1 : ℝ) - ρ.re - 1 / 2 = -(ρ.re - 1 / 2) by ring, abs_neg]
  · intro ρ
    simp [OnLine, abs_eq_zero, sub_eq_zero]

/-- Packaging: the symmetry barrier separates ORIENTATION from DETECTION.  Both halves
hold simultaneously, so "reflection-invariant instruments are blind to off-line-ness" is
FALSE as stated; only "blind to orientation" is true. -/
theorem forced_and_detect :
    (∀ {α : Type} (F : ℂ → α), (∀ ρ, F (reflect ρ) = F ρ) → ∀ dec : α → Prop,
        ¬ (∀ ρ : ℂ, ρ.re ≠ 1 / 2 → (dec (F ρ) ↔ 1 / 2 < ρ.re)))
      ∧ (∃ F : ℂ → ℝ, (∀ ρ, F (reflect ρ) = F ρ) ∧ (∀ ρ, F ρ = 0 ↔ OnLine ρ)) :=
  ⟨fun F hF dec => no_invariant_orients F hF dec, invariant_detects⟩

end WallBarrierAM

/-! ### Registry form

`reflect` and `OnLine` unfolded, so that the mission statement file for the proposed node
`RH_barrier_orientation_only` is literally contained in this artifact and the `grant` gate's
normalized-containment check passes without any new vocabulary in `RHDefs`. -/

theorem WallBarrierAM.RH_barrier_orientation_only :
    (∀ {α : Type} (F : ℂ → α), (∀ ρ : ℂ, F (1 - (starRingEnd ℂ) ρ) = F ρ) →
        ∀ dec : α → Prop,
          ¬ (∀ ρ : ℂ, ρ.re ≠ 1 / 2 → (dec (F ρ) ↔ 1 / 2 < ρ.re)))
      ∧ (∃ F : ℂ → ℝ, (∀ ρ : ℂ, F (1 - (starRingEnd ℂ) ρ) = F ρ)
          ∧ (∀ ρ : ℂ, F ρ = 0 ↔ ρ.re = 1 / 2)) := by
  exact WallBarrierAM.forced_and_detect


/-! ### Axiom guard (kernel evidence, printed by `lake env lean`) -/
#print axioms WallBarrierAM.no_invariant_orients
#print axioms WallBarrierAM.invariant_detects
#print axioms WallBarrierAM.forced_and_detect
#print axioms WallBarrierAM.onLine_reflect
#print axioms WallBarrierAM.RH_barrier_orientation_only
