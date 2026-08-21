/- HAND-AUTHORED (not telperion-generated): the hsq reduction and the d = 1
   discharge — closing the loop on the duality layer.

   Duality.lean's master theorem is conditional on hsq: nonnegativity of
   the pseudoexpectation on low-degree squares.  This file:

   * `pe_sq` / `hsq_of_subsetForm` — REDUCES hsq to the finite
     subset-indexed quadratic form  Σ_{S,T} x_S x_T f(|S ∪ T|) ≥ 0
     (|S|,|T| ≤ d), by expanding pe(s²) over the monomial support and
     grouping coefficients by exponent support (the multilinearization
     collapse).  This is exactly the object the Python layer validated
     (130×130 spectral reconstruction); the hypothesis of the conditional
     master is now FINITE-DIMENSIONAL (`SubsetFormPSD`), named as the
     remaining open layer (harmonic completeness);
   * `subsetForm_d1` — DISCHARGES d = 1 outright: the degree-1 form equals
     (x_∅ + X/2)² + (N·Q − X²)/(4(N−1))  with X = Σ x_{i}, Q = Σ x_{i}²,
     nonnegative by Cauchy–Schwarz.  The remainder coefficient identity is
     exact (the tie in disguise);
   * `knapsack_no_refutation_d1` — the payoff, UNCONDITIONAL: for every
     N > 2 there is NO SOS refutation of the knapsack system with squares
     of degree ≤ 1 and cofactors of degree ≤ 2.  The first fully
     kernel-checked end-to-end refutation-form statement of the pipeline
     (for odd N the system is genuinely infeasible: `knapsack_unsat`). -/
import Mathlib
import Duality

namespace KnapsackSOS
namespace Duality

open MvPolynomial

/-! ### Support algebra -/

/-- ℕ-valued Finsupp addition has no cancellation: supports unite. -/
theorem support_add_union {N : ℕ} (α β : Fin N →₀ ℕ) :
    (α + β).support = α.support ∪ β.support := by
  ext j
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_union]
  omega

theorem pe_monomial_mul (nq : ℚ) {N : ℕ} (α β : Fin N →₀ ℕ) (c e : ℚ) :
    pe nq (monomial α c * monomial β e)
      = c * e * f nq (α.support ∪ β.support).card := by
  rw [monomial_mul, pe_monomial, support_add_union]

/-! ### pe on squares, as the subset quadratic form -/

theorem pe_sq (nq : ℚ) {N : ℕ} (s : MvPolynomial (Fin N) ℚ) :
    pe nq (s ^ 2) = ∑ α ∈ s.support, ∑ β ∈ s.support,
      coeff α s * coeff β s * f nq (α.support ∪ β.support).card := by
  conv_lhs => rw [sq, as_sum s, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  exact pe_monomial_mul nq α β _ _

/-- The finite-dimensional remaining hypothesis: PSDness of the
subset-indexed moment form at level d (harmonic completeness). -/
def SubsetFormPSD (nq : ℚ) (N d : ℕ) : Prop :=
  ∀ x : Finset (Fin N) → ℚ, (∀ S, d < S.card → x S = 0) →
    0 ≤ ∑ S : Finset (Fin N), ∑ T : Finset (Fin N),
      x S * x T * f nq (S ∪ T).card

/-- The reduction: the subset form controls pe on squares.  Coefficients
are grouped by exponent support (multilinearization); the grouped vector
vanishes above level d because support card ≤ total degree. -/
theorem hsq_of_subsetForm (nq : ℚ) {N : ℕ} (d : ℕ)
    (H : SubsetFormPSD nq N d) :
    ∀ s : MvPolynomial (Fin N) ℚ, s.totalDegree ≤ d → 0 ≤ pe nq (s ^ 2) := by
  intro s hs
  classical
  set x : Finset (Fin N) → ℚ :=
    fun S => ∑ α ∈ s.support.filter (fun α => α.support = S), coeff α s with hxdef
  have hvanish : ∀ S : Finset (Fin N), d < S.card → x S = 0 := by
    intro S hS
    rw [hxdef]
    refine Finset.sum_eq_zero fun α hα => ?_
    exfalso
    have hmem := (Finset.mem_filter.mp hα).1
    have hsup := (Finset.mem_filter.mp hα).2
    have h1 : α.support.card ≤ α.sum fun _ e => e := card_support_le_degree α
    have h2 : (α.sum fun _ e => e) ≤ s.totalDegree := le_totalDegree hmem
    rw [hsup] at h1
    omega
  have key : ∑ S : Finset (Fin N), ∑ T : Finset (Fin N),
      x S * x T * f nq (S ∪ T).card = pe nq (s ^ 2) := by
    rw [pe_sq]
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun α : Fin N →₀ ℕ => α.support)
      (fun α (_ : α ∈ s.support) => Finset.mem_univ α.support)
      (fun α => ∑ β ∈ s.support,
        coeff α s * coeff β s * f nq (α.support ∪ β.support).card)]
    refine Finset.sum_congr rfl fun S _ => ?_
    -- inner: group β by support as well, for each α in the S-fiber
    have inner : ∀ α ∈ s.support.filter (fun α => α.support = S),
        ∑ β ∈ s.support,
          coeff α s * coeff β s * f nq (α.support ∪ β.support).card
        = coeff α s * ∑ T : Finset (Fin N), x T * f nq (S ∪ T).card := by
      intro α hα
      have hαS : α.support = S := (Finset.mem_filter.mp hα).2
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun β : Fin N →₀ ℕ => β.support)
        (fun β (_ : β ∈ s.support) => Finset.mem_univ β.support)
        (fun β => coeff α s * coeff β s * f nq (α.support ∪ β.support).card)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [hxdef, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β hβ => ?_
      have hβT : β.support = T := (Finset.mem_filter.mp hβ).2
      rw [hαS, hβT]
      ring
    rw [Finset.sum_congr rfl inner, ← Finset.sum_mul]
    have hxS : (∑ α ∈ s.support.filter (fun α => α.support = S), coeff α s)
        = x S := by rw [hxdef]
    rw [hxS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [← key]
  exact H x hvanish

/-! ### The d = 1 discharge -/

/-- f-values needed at level 1 (N ≥ 3 keeps denominators alive). -/
theorem f_one (N : ℕ) (hN : 0 < N) : f (N : ℚ) 1 = 1 / 2 := by
  have h0 : (N : ℚ) ≠ 0 := by
    have : (0 : ℚ) < N := by exact_mod_cast hN
    linarith
  simp only [f]
  push_cast
  field_simp
  ring

theorem f_two (N : ℕ) (hN : 1 < N) : f (N : ℚ) 2
    = ((N : ℚ) - 2) / (4 * ((N : ℚ) - 1)) := by
  have h0 : (N : ℚ) ≠ 0 := by
    have : (1 : ℚ) < N := by exact_mod_cast hN
    linarith
  have h1 : (N : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < N := by exact_mod_cast hN
    linarith
  simp only [f]
  push_cast
  field_simp
  ring

/-- The level-1 subset form is a completed square plus a Cauchy–Schwarz
remainder: (x_∅ + X/2)² + (N·Q − X²)/(4(N−1)). -/
theorem subsetForm_d1 (N : ℕ) (hN : 2 < N) : SubsetFormPSD (N : ℚ) N 1 := by
  intro x hx
  classical
  set P : Finset (Finset (Fin N)) :=
    insert ∅ (Finset.univ.image fun i : Fin N => {i}) with hP
  have hmemP : ∀ S : Finset (Fin N), S ∉ P → x S = 0 := by
    intro S hS
    refine hx S ?_
    by_contra hcard
    push_neg at hcard
    interval_cases h : S.card
    · exact hS (by simp [hP, Finset.card_eq_zero.mp h])
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
      exact hS (by simp [hP, hi])
  have hrestrict : ∑ S : Finset (Fin N), ∑ T : Finset (Fin N),
      x S * x T * f (N : ℚ) (S ∪ T).card
      = ∑ S ∈ P, ∑ T ∈ P, x S * x T * f (N : ℚ) (S ∪ T).card := by
    rw [← Finset.sum_subset (Finset.subset_univ P)]
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ P)]
      intro T _ hT
      rw [hmemP T hT, mul_zero, zero_mul]
    · intro S _ hS
      refine Finset.sum_eq_zero fun T _ => ?_
      rw [hmemP S hS, zero_mul, zero_mul]
  rw [hrestrict]
  have hnotmem : (∅ : Finset (Fin N)) ∉ Finset.univ.image
      (fun i : Fin N => ({i} : Finset (Fin N))) := by
    simp
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin N)), ∀ b ∈ Finset.univ,
      ({a} : Finset (Fin N)) = {b} → a = b :=
    fun a _ b _ h => Finset.singleton_injective h
  set A := x ∅ with hA
  set X := ∑ i : Fin N, x {i} with hX
  set Q := ∑ i : Fin N, x {i} ^ 2 with hQ
  set f1 := f (N : ℚ) 1 with hf1d
  set f2 := f (N : ℚ) 2 with hf2d
  have csum : ∀ c : ℚ, ∑ i : Fin N, c * x {i} = c * X := fun c => by
    rw [hX, Finset.mul_sum]
  -- row lemmas, fully explicit right-hand sides
  have hrow0 : ∑ T ∈ P, x ∅ * x T * f (N : ℚ) ((∅ : Finset (Fin N)) ∪ T).card
      = A * A + A * f1 * X := by
    rw [hP, Finset.sum_insert hnotmem, Finset.sum_image hinj]
    simp only [Finset.empty_union, Finset.union_empty, Finset.card_empty,
      Finset.card_singleton]
    have h1 : ∑ i : Fin N, x ∅ * x {i} * f (N : ℚ) 1
        = ∑ i : Fin N, (A * f1) * x {i} :=
      Finset.sum_congr rfl fun i _ => by rw [hA, hf1d]; ring
    rw [h1, csum (A * f1)]
    show A * A * f (N : ℚ) 0 + A * f1 * X = A * A + A * f1 * X
    rw [show f (N : ℚ) 0 = 1 from rfl]
    ring
  have hcup : ∀ i j : Fin N, (({i} : Finset (Fin N)) ∪ {j}).card
      = if j = i then 1 else 2 := by
    intro i j
    rcases eq_or_ne j i with rfl | hij
    · simp
    · rw [if_neg hij, Finset.singleton_union,
        Finset.card_insert_of_notMem (by simp [Ne.symm hij]),
        Finset.card_singleton]
  have hrow : ∀ i : Fin N,
      ∑ T ∈ P, x {i} * x T * f (N : ℚ) (({i} : Finset (Fin N)) ∪ T).card
      = (f1 * A) * x {i} + ((f2 * X) * x {i} + (f1 - f2) * x {i} ^ 2) := by
    intro i
    rw [hP, Finset.sum_insert hnotmem, Finset.sum_image hinj]
    simp only [Finset.union_empty, Finset.card_singleton]
    have hsplit : ∑ j : Fin N,
        x {i} * x {j} * f (N : ℚ) (({i} : Finset (Fin N)) ∪ {j}).card
        = ∑ j : Fin N, ((f2 * x {i}) * x {j}
            + if j = i then x {i} * x {j} * (f1 - f2) else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcup i j]
      rcases eq_or_ne j i with rfl | hij
      · rw [if_pos rfl, if_pos rfl, hf1d, hf2d]
        ring
      · rw [if_neg hij, if_neg hij, hf2d]
        ring
    rw [hsplit, Finset.sum_add_distrib, csum (f2 * x {i}),
      Finset.sum_ite_eq' Finset.univ i
        (fun j => x {i} * x {j} * (f1 - f2))]
    simp only [Finset.mem_univ, if_pos]
    rw [hf1d, hf2d]
    ring
  rw [hP, Finset.sum_insert hnotmem, Finset.sum_image hinj]
  rw [hrow0]
  have hRows : ∑ i : Fin N,
      ∑ T ∈ P, x {i} * x T * f (N : ℚ) (({i} : Finset (Fin N)) ∪ T).card
      = ∑ i : Fin N, ((f1 * A) * x {i}
          + ((f2 * X) * x {i} + (f1 - f2) * x {i} ^ 2)) :=
    Finset.sum_congr rfl fun i _ => hrow i
  rw [hRows, Finset.sum_add_distrib, csum (f1 * A), Finset.sum_add_distrib,
    csum (f2 * X)]
  have hQcollapse : ∑ i : Fin N, (f1 - f2) * x {i} ^ 2 = (f1 - f2) * Q := by
    rw [hQ, Finset.mul_sum]
  rw [hQcollapse]
  -- scalar endgame
  have hf1 : f1 = 1 / 2 := by rw [hf1d]; exact f_one N (by omega)
  have hf2 : f2 = ((N : ℚ) - 2) / (4 * ((N : ℚ) - 1)) := by
    rw [hf2d]; exact f_two N (by omega)
  have hCS : X ^ 2 ≤ (N : ℚ) * Q := by
    have := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin N))) (f := fun i => x {i})
    simpa [hX, hQ] using this
  have hN1 : (0 : ℚ) < (N : ℚ) - 1 := by
    have : (2 : ℚ) < N := by exact_mod_cast hN
    linarith
  have hkey : A * A + A * f1 * X + (f1 * A * X + (f2 * X * X + (f1 - f2) * Q))
      = (A + X / 2) ^ 2 + ((N : ℚ) * Q - X ^ 2) / (4 * ((N : ℚ) - 1)) := by
    rw [hf1, hf2]
    field_simp
    ring
  rw [hkey]
  have h1 : (0 : ℚ) ≤ (A + X / 2) ^ 2 := sq_nonneg _
  have h2 : (0 : ℚ) ≤ ((N : ℚ) * Q - X ^ 2) / (4 * ((N : ℚ) - 1)) :=
    div_nonneg (by linarith) (by linarith)
  linarith

/-- THE PAYOFF, UNCONDITIONAL: for every N > 2 no SOS refutation of the
knapsack system with squares of degree ≤ 1 and cofactors of degree ≤ 2
exists.  First fully kernel-checked end-to-end refutation-form statement
of the pipeline (for odd N the refuted system is genuinely infeasible:
`KnapsackSOS.knapsack_unsat`). -/
theorem knapsack_no_refutation_d1 (N : ℕ) (hN : 2 < N) :
    IsEmpty (SOSRefutation (knapsackSystem N) 1 2) :=
  knapsack_no_refutation N 1 (by omega)
    (hsq_of_subsetForm (N : ℚ) 1 (subsetForm_d1 N hN))

/-- The sharpened conditional master: the sole remaining hypothesis is the
finite-dimensional subset form (harmonic completeness), for general d. -/
theorem knapsack_no_refutation_of_subsetForm (N d : ℕ) (hd : 2 * d < N)
    (H : SubsetFormPSD (N : ℚ) N d) :
    IsEmpty (SOSRefutation (knapsackSystem N) d (2 * d)) :=
  knapsack_no_refutation N d hd (hsq_of_subsetForm (N : ℚ) d H)

end Duality
end KnapsackSOS

#print axioms KnapsackSOS.Duality.hsq_of_subsetForm
#print axioms KnapsackSOS.Duality.subsetForm_d1
#print axioms KnapsackSOS.Duality.knapsack_no_refutation_d1
#print axioms KnapsackSOS.Duality.knapsack_no_refutation_of_subsetForm
