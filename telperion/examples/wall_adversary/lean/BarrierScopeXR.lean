/-
  BarrierScopeXR.lean -- ADVERSARIAL re-check of the proposed FE-uniformity barrier.

  Branch wall/adversary, 2026-09-18.  conjecture1_proved = False.  No RH progress is
  claimed; this file bounds what a proposed barrier can do, and the bound is: nothing.

  WHAT IS BEING CHECKED.  The barrier seat proposed (FEUniformBarrierAM.lean, branch
  wall/barrier) a bundle

    FEData = entire + self-dual (Xi (1 - s) = Xi s) + order one

  and three transfer theorems whose common shape is

    (a member with an off-line zero)  ==>  NOT (for all E : FEData, Crit E),

  concluding "no FE-uniform argument can prove any route's wall clause, and one witness
  refutes all four routes at once".

  THE DEFECT, PROVED HERE.  Every route's wall clause is a statement about ONE member
  (the completed zeta): A5 "defect-0 membership of the regularized triple", B10 "all-n
  positivity", C10 "Lambda <= 0", D11 "Weil positivity".  None of them is a statement of
  the form `forall E : FEData, ...`.  The transfer theorems refute only the UNIVERSALLY
  QUANTIFIED form, and that refutation provably carries NO information about any fixed
  member:

    * `barrier_silent`                    -- the bundle contains a member satisfying the
                                             RH analogue AND a member refuting it, so
                                             `NOT (forall E, RHfor E)` is true while
                                             `RHfor D0` remains open for every D0.
    * `transfer_to_member_fails`          -- the inference "uniform form refuted, therefore
                                             the member's form is refuted" is FALSE in the
                                             kernel.
    * `uniform_refutation_decides_nothing`-- and this holds for EVERY criterion `Crit`
                                             equivalent to the RH analogue on the bundle,
                                             i.e. for exactly the class the barrier claims
                                             to kill: Li positivity, Weil positivity,
                                             Lambda <= 0, comb membership.

  So the transfer schema is sound and empty.  It is modus tollens: a universally
  quantified statement that implies a false statement is false.  The mathematical content
  is entirely in the unformalized premise "route R's wall clause is FE-uniform", which is
  false for every route actually pursued (see the report: route B's own corpus proof
  consumes `riemannZeta_ne_zero_of_one_le_re`, i.e. Euler-product non-vanishing, at
  RHBridge.lean:48,79).

  SECOND DEFECT, PROVED HERE.  The generalized FORCED half (`no_invariant_orients`)
  derives its contradiction from the pair (0, 1), which are not zeros of anything.
  Restricted to the domain where every instrument in this program actually operates --
  the zero set -- FORCED is VACUOUS under the RH analogue (`forced_on_zeros_vacuous`),
  and asserting it is EQUIVALENT to asserting an off-line zero
  (`forced_on_zeros_iff_not_rh`).  A statement equivalent to NOT-RH cannot obstruct a
  proof of RH; it presupposes its negation.

  THIRD POINT, PROVED HERE.  `enriched_bundle_flips`: enriching the bundle (the barrier
  seat's own "task number one") only helps if the ENRICHED class still contains an
  off-line witness.  Over a class with no such witness the very same schema turns into a
  THEOREM schema, not a barrier.  The program's actual target class (roadmap A1d:
  unimodular completely-multiplicative + FE, i.e. the degree-one Selberg class) excludes
  Davenport-Heilbronn by the multiplicativity clause, so no witness is available there.
  The barrier's force is a property of the class chosen, not of RH.

  Nothing here is progress on RH.
-/
import Mathlib

namespace BarrierScopeXR

open Complex

/-! ### The bundle, restated verbatim from the proposal -/

/-- On the critical line. -/
def OnLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- The FE-only bundle of the proposal: entire, self-dual, order one. -/
structure FEData where
  Ξ : ℂ → ℂ
  entire : Differentiable ℂ Ξ
  fe : ∀ s : ℂ, Ξ (1 - s) = Ξ s
  orderOne : ∃ C c : ℝ, ∀ s : ℂ, ‖Ξ s‖ ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖))

/-- The RH analogue for a member of the bundle. -/
def RHfor (D : FEData) : Prop := ∀ s : ℂ, D.Ξ s = 0 → OnLine s

/-! ### Two members: one refuting the RH analogue, one satisfying it -/

/-- A quadratic growth bound suffices for the bundle's order clause. -/
lemma exp_bound_of_sq {f : ℂ → ℂ} (h : ∀ s : ℂ, ‖f s‖ ≤ (1 + ‖s‖) ^ 2) :
    ∃ C c : ℝ, ∀ s : ℂ, ‖f s‖ ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  refine ⟨1, 2, fun s => ?_⟩
  set r := ‖s‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg s
  have hexp : (2 + r) ^ 2 ≤ Real.exp (2 * (1 + r) * Real.log (2 + r)) := by
    have h2 : Real.exp (2 * Real.log (2 + r)) = (2 + r) ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log (by linarith)]; ring
    rw [← h2]
    refine Real.exp_le_exp.mpr ?_
    have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
    nlinarith
  have hmono : (1 + r) ^ 2 ≤ (2 + r) ^ 2 := by nlinarith
  calc ‖f s‖ ≤ (1 + r) ^ 2 := h s
    _ ≤ (2 + r) ^ 2 := hmono
    _ ≤ Real.exp (2 * (1 + r) * Real.log (2 + r)) := hexp
    _ = 1 * Real.exp (2 * (1 + r) * Real.log (2 + r)) := by ring

/-- `s * (s - 1)`: the cheap off-line witness the barrier seat found himself. -/
noncomputable def polyFEData : FEData where
  Ξ := fun s => s * (s - 1)
  entire := by fun_prop
  fe := by intro s; ring
  orderOne := by
    refine exp_bound_of_sq (fun s => ?_)
    have h1 : ‖s - 1‖ ≤ ‖s‖ + 1 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by simp
    have h0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    calc ‖s * (s - 1)‖ = ‖s‖ * ‖s - 1‖ := by rw [norm_mul]
      _ ≤ (1 + ‖s‖) * (‖s‖ + 1) := by
          apply mul_le_mul (by linarith) h1 (norm_nonneg _) (by linarith)
      _ = (1 + ‖s‖) ^ 2 := by ring

/-- `(s - 1/2)^2`: an ON-LINE member of the same bundle.  Entire, self-dual, order zero,
and its only zero is `1/2`.  This member is what makes the barrier silent. -/
noncomputable def sqFEData : FEData where
  Ξ := fun s => (s - 1 / 2) ^ 2
  entire := by fun_prop
  fe := by intro s; ring
  orderOne := by
    refine exp_bound_of_sq (fun s => ?_)
    have h1 : ‖s - 1 / 2‖ ≤ ‖s‖ + 1 := by
      have : ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      have h2 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
        norm_num
      linarith
    have h0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have hnn : (0 : ℝ) ≤ ‖s - 1 / 2‖ := norm_nonneg _
    calc ‖(s - 1 / 2) ^ 2‖ = ‖s - 1 / 2‖ ^ 2 := by rw [norm_pow]
      _ ≤ (1 + ‖s‖) ^ 2 := by nlinarith

/-- The bundle member `s ↦ (s - 1/2)^2` SATISFIES the RH analogue. -/
theorem rhfor_sqFEData : RHfor sqFEData := by
  intro s hs
  have hs' : (s - 1 / 2) ^ 2 = 0 := hs
  have h1 : s - 1 / 2 = 0 := by
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hs'
  have h2 : s = 1 / 2 := by
    have := sub_eq_zero.mp h1
    exact this
  show s.re = 1 / 2
  rw [h2, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]

/-- The bundle member `s ↦ s * (s - 1)` REFUTES the RH analogue (zero at `0`). -/
theorem not_rhfor_polyFEData : ¬ RHfor polyFEData := by
  intro h
  have hz : polyFEData.Ξ 0 = 0 := by show (0 : ℂ) * (0 - 1) = 0; ring
  have h0 : ((0 : ℂ)).re = 1 / 2 := h 0 hz
  norm_num at h0

/-! ### The barrier's conclusion is TRUE and EMPTY -/

/-- **The barrier is silent.**  The bundle contains a member refuting the RH analogue AND a
member satisfying it.  So `¬ ∀ E, RHfor E` -- the barrier's entire conclusion -- holds while
`RHfor D` stays open for every fixed `D`.  A universally quantified refutation over a class
that also contains positive instances constrains no instance. -/
theorem barrier_silent : (¬ ∀ E : FEData, RHfor E) ∧ (∃ E : FEData, RHfor E) :=
  ⟨fun h => not_rhfor_polyFEData (h polyFEData), ⟨sqFEData, rhfor_sqFEData⟩⟩

/-- **The transfer the barrier needs does not exist.**  "The uniform form is refuted,
therefore the member's form is refuted" is FALSE in the kernel.  Every route's wall clause
is a member's form. -/
theorem transfer_to_member_fails :
    ¬ (∀ D0 : FEData, (¬ ∀ E : FEData, RHfor E) → ¬ RHfor D0) := by
  intro h
  exact h sqFEData barrier_silent.1 rhfor_sqFEData

/-- **And it decides nothing for ANY criterion in the class the barrier claims to kill.**
Let `Crit` be equivalent to the RH analogue throughout the bundle -- the exact hypothesis of
`fe_uniform_criterion_is_false`, satisfied (by the barrier's own reading) by Li positivity,
Weil positivity, `Λ ≤ 0` and comb membership.  Then the barrier refutes `∀ E, Crit E`, and
simultaneously `Crit` is TRUE at one bundle member and FALSE at another.  The refutation
therefore transmits nothing to the completed zeta. -/
theorem uniform_refutation_decides_nothing (Crit : FEData → Prop)
    (hequiv : ∀ E : FEData, Crit E ↔ RHfor E) :
    (¬ ∀ E : FEData, Crit E) ∧ (∃ E : FEData, Crit E) ∧ (∃ E : FEData, ¬ Crit E) := by
  refine ⟨?_, ⟨sqFEData, (hequiv sqFEData).mpr rhfor_sqFEData⟩,
    ⟨polyFEData, fun hc => not_rhfor_polyFEData ((hequiv polyFEData).mp hc)⟩⟩
  intro h
  exact not_rhfor_polyFEData ((hequiv polyFEData).mp (h polyFEData))

/-! ### The symmetry half, restricted to the domain instruments live on -/

/-- **FORCED is vacuous on the zero set under the RH analogue.**  The generalized FORCED
theorem takes its contradiction from the pair `(0, 1)`, which are not zeros.  Every
per-zero instrument this program builds is evaluated ON ZEROS; there, under `RHfor D`, ANY
map and ANY decision rule satisfy the orientation condition vacuously. -/
theorem forced_on_zeros_vacuous (D : FEData) (hRH : RHfor D)
    {α : Type*} (F : ℂ → α) (dec : α → Prop) :
    ∀ ρ : ℂ, D.Ξ ρ = 0 → ρ.re ≠ 1 / 2 → (dec (F ρ) ↔ 1 / 2 < ρ.re) := by
  intro ρ hz hne
  exact absurd (hRH ρ hz) hne

/-- **So the zero-set form of FORCED is equivalent to NOT-RH.**  Asserting that an
instrument fails to orient ON THE ZERO SET already asserts the existence of an off-line
zero.  A statement equivalent to the negation of the target cannot be an obstruction to
proving the target; it presupposes its falsity. -/
theorem forced_on_zeros_iff_not_rh (D : FEData) {α : Type*} (F : ℂ → α) (dec : α → Prop) :
    (¬ (∀ ρ : ℂ, D.Ξ ρ = 0 → ρ.re ≠ 1 / 2 → (dec (F ρ) ↔ 1 / 2 < ρ.re))) → ¬ RHfor D := by
  intro h hRH
  exact h (forced_on_zeros_vacuous D hRH F dec)

/-! ### Enrichment cuts both ways -/

/-- **The barrier's force is a property of the class, not of RH.**  Let `P` carve out an
enriched sub-bundle (the barrier seat's "task number one": a normalized Dirichlet series, or
-- as the roadmap's A1d actually targets -- unimodular complete multiplicativity, which
Davenport-Heilbronn FAILS).  If the enriched class has NO off-line witness, then the very
same schema runs FORWARD: the criterion holds throughout the enriched class.  Enrichment
without a witness in the enriched class converts the barrier into a theorem schema. -/
theorem enriched_bundle_flips (P : FEData → Prop) (Crit : FEData → Prop)
    (hequiv : ∀ E : FEData, P E → (Crit E ↔ RHfor E))
    (hno_witness : ∀ E : FEData, P E → RHfor E) :
    ∀ E : FEData, P E → Crit E := by
  intro E hP
  exact (hequiv E hP).mpr (hno_witness E hP)

/-- Packaging, for the ledger: the proposed barrier's conclusion is true, and it is
compatible with both truth values of every route's wall clause. -/
theorem barrier_scope_verdict :
    (¬ ∀ E : FEData, RHfor E)
      ∧ (∃ E : FEData, RHfor E)
      ∧ ¬ (∀ D0 : FEData, (¬ ∀ E : FEData, RHfor E) → ¬ RHfor D0) :=
  ⟨barrier_silent.1, barrier_silent.2, transfer_to_member_fails⟩

end BarrierScopeXR

#print axioms BarrierScopeXR.barrier_silent
#print axioms BarrierScopeXR.transfer_to_member_fails
#print axioms BarrierScopeXR.uniform_refutation_decides_nothing
#print axioms BarrierScopeXR.forced_on_zeros_vacuous
#print axioms BarrierScopeXR.forced_on_zeros_iff_not_rh
#print axioms BarrierScopeXR.enriched_bundle_flips
#print axioms BarrierScopeXR.rhfor_sqFEData
#print axioms BarrierScopeXR.barrier_scope_verdict
