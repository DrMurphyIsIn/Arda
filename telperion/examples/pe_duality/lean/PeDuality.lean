/- telperion 0.1.6 | family PeDuality | input-hash 5ee7a6b2632827d8
   11 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace PeDuality

open MvPolynomial
open scoped symmDiff

/-- A degree-bounded Positivstellensatz refutation of `{g i = 0}`:
`-1 = Σ s_j² + Σ p_i·g_i` with square degrees ≤ ds, cofactor degrees ≤ dc.
(Copied verbatim from the kernel-green KnapsackSOS.Duality.SOSRefutation.) -/
structure SOSRefutation {N : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → MvPolynomial (Fin N) ℚ) (ds : ℕ) (dc : ι → ℕ) where
  k : ℕ
  squares : Fin k → MvPolynomial (Fin N) ℚ
  sqDeg : ∀ j, (squares j).totalDegree ≤ ds
  cof : ι → MvPolynomial (Fin N) ℚ
  cofDeg : ∀ i, (cof i).totalDegree ≤ dc i
  identity : (-1 : MvPolynomial (Fin N) ℚ)
      = (∑ j, squares j ^ 2) + ∑ i, cof i * g i

/-- The abstract duality: a pseudoexpectation blocks all refutations.
(Copied verbatim from the kernel-green KnapsackSOS.Duality.no_refutation:
`map_add`/`map_sum`/`map_neg` + `Finset.sum_eq_zero` + `Finset.sum_nonneg`
+ `linarith`.) -/
theorem no_refutation {N : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → MvPolynomial (Fin N) ℚ) (ds : ℕ) (dc : ι → ℕ)
    (E : MvPolynomial (Fin N) ℚ →ₗ[ℚ] ℚ)
    (hE1 : E 1 = 1)
    (hsq : ∀ s : MvPolynomial (Fin N) ℚ, s.totalDegree ≤ ds → 0 ≤ E (s ^ 2))
    (hker : ∀ i, ∀ p : MvPolynomial (Fin N) ℚ,
      p.totalDegree ≤ dc i → E (p * g i) = 0) :
    IsEmpty (SOSRefutation g ds dc) := by
  constructor
  intro R
  have h := congrArg E R.identity
  rw [map_add, map_sum, map_sum, map_neg, hE1] at h
  have hz : ∑ i, E (R.cof i * g i) = 0 :=
    Finset.sum_eq_zero fun i _ => hker i (R.cof i) (R.cofDeg i)
  have hpos : (0 : ℚ) ≤ ∑ j, E (R.squares j ^ 2) :=
    Finset.sum_nonneg fun j _ => hsq _ (R.sqDeg j)
  rw [hz] at h
  linarith

/-- Support of a shifted exponent vector: adding `single i k` (k ≠ 0) inserts
`i`.  (Copied verbatim from KnapsackSOS.Duality.support_single_add.) -/
theorem support_single_add {N : ℕ} {k : ℕ} (hk : k ≠ 0) (i : Fin N)
    (α : Fin N →₀ ℕ) :
    (Finsupp.single i k + α).support = insert i α.support := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp [Finsupp.mem_support_iff, hk]
  · simp [Finsupp.mem_support_iff, hj]

/-- The odd-exponent variable set of a monomial exponent vector (±1 mode).
(Copied from Xor3Duality.oddSet, generalized in N.) -/
def oddSet {N : ℕ} (α : Fin N →₀ ℕ) : Finset (Fin N) :=
  α.support.filter (fun i => α i % 2 = 1)

theorem mem_oddSet {N : ℕ} {α : Fin N →₀ ℕ} {i : Fin N} :
    i ∈ oddSet α ↔ α i % 2 = 1 := by
  simp only [oddSet, Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

/-- Parity is a symmetric-difference homomorphism: the ±1 multilinearization
law.  (Copied from Xor3Duality.oddSet_add.) -/
theorem oddSet_add {N : ℕ} (α β : Fin N →₀ ℕ) :
    oddSet (α + β) = oddSet α ∆ oddSet β := by
  ext i
  rw [Finset.mem_symmDiff]
  simp only [mem_oddSet, Finsupp.add_apply]
  omega

/-- Adding 2 to any exponent preserves the parity set.
(Copied from Xor3Duality.oddSet_add_two.) -/
theorem oddSet_add_two {N : ℕ} (i : Fin N) (α : Fin N →₀ ℕ) :
    oddSet (Finsupp.single i 2 + α) = oddSet α := by
  ext j
  simp only [mem_oddSet, Finsupp.add_apply, Finsupp.single_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij]

/-! ### Instance `knap_n5_d1`: 5 vars, degree 1, 0/1 (bool) semantics.
Support-weighted pseudoexpectation (weight sees only WHICH variables occur);
the boolean ideal `X i ^ 2 - X i` is killed UNCONDITIONALLY. -/

/-- Support-cardinality weight (admissible: `fw 0 = 1`). -/
noncomputable def fw_knap_n5_d1 : ℕ → ℚ := fun k => (1 : ℚ) / (k.factorial : ℚ)

/-- The support-weighted pseudoexpectation as a linear functional. -/
noncomputable def pe_knap_n5_d1 : MvPolynomial (Fin 5) ℚ →ₗ[ℚ] ℚ := by
  exact (Finsupp.linearCombination ℚ
      (fun α : Fin 5 →₀ ℕ => fw_knap_n5_d1 α.support.card)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ)).toLinearMap

theorem pe_knap_n5_d1_monomial (α : Fin 5 →₀ ℕ) (c : ℚ) :
    pe_knap_n5_d1 (monomial α c) = c * fw_knap_n5_d1 α.support.card := by
  unfold pe_knap_n5_d1
  rw [← single_eq_monomial]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
    smul_eq_mul]

theorem pe_knap_n5_d1_one : pe_knap_n5_d1 (1 : MvPolynomial (Fin 5) ℚ) = 1 := by
  rw [one_def, pe_knap_n5_d1_monomial]
  simp [fw_knap_n5_d1]

/-- The boolean ideal `X i ^ 2 - X i` is killed UNCONDITIONALLY (the weight sees
only supports, and `support(α + 2eᵢ) = support(α + eᵢ)`). -/
theorem knap_n5_d1_bool_kill (i : Fin 5) (p : MvPolynomial (Fin 5) ℚ) :
    pe_knap_n5_d1 ((X i ^ 2 - X i) * p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have h2 : (X i : MvPolynomial (Fin 5) ℚ) ^ 2 * monomial α c
        = monomial (Finsupp.single i 2 + α) c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have h1 : (X i : MvPolynomial (Fin 5) ℚ) * monomial α c
        = monomial (Finsupp.single i 1 + α) c := by
      rw [X, monomial_mul, one_mul]
    rw [sub_mul, map_sub, h2, h1, pe_knap_n5_d1_monomial, pe_knap_n5_d1_monomial,
      support_single_add (by norm_num) i α,
      support_single_add (by norm_num) i α, sub_self]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, add_zero]

/-- The boolean constraint system: booleanity per variable. -/
noncomputable def knap_n5_d1System : Fin 5 → MvPolynomial (Fin 5) ℚ :=
  fun i => X i ^ 2 - X i

/-- CONDITIONAL MASTER: modulo the named square-nonnegativity hypothesis (the
moment-matrix PSD fact in functional form — the SDP leaf), NO degree-1 SoS
refutation of the boolean system exists (cofactors of degree ≤ 2).
Structurally identical to KnapsackSOS.Duality.knapsack_no_refutation. -/
theorem knap_n5_d1_no_refutation
    (hsq : ∀ s : MvPolynomial (Fin 5) ℚ, s.totalDegree ≤ 1 →
      0 ≤ pe_knap_n5_d1 (s ^ 2)) :
    IsEmpty (SOSRefutation knap_n5_d1System 1 (fun _ => 2)) := by
  refine no_refutation _ 1 (fun _ => 2) pe_knap_n5_d1 pe_knap_n5_d1_one hsq ?_
  intro i p _
  rw [show pe_knap_n5_d1 (p * knap_n5_d1System i) = pe_knap_n5_d1 ((X i ^ 2 - X i) * p) from by
    rw [mul_comm]; rfl]
  exact knap_n5_d1_bool_kill i p

#print axioms knap_n5_d1_no_refutation

/-! ### Instance `xor_n7_d2`: 7 vars, degree 2, ±1 (parity) semantics.
Parity-weighted pseudoexpectation (weight sees only the odd-exponent set);
the ±1 booleanity ideal `X i ^ 2 - 1` is killed UNCONDITIONALLY. -/

/-- Parity-mask weight: indicator of the empty parity set (admissible: the
constant monomial has weight 1). -/
noncomputable def wpar_xor_n7_d2 (α : Fin 7 →₀ ℕ) : ℚ :=
  if oddSet α = ∅ then 1 else 0

/-- The parity-weighted pseudoexpectation as a linear functional. -/
noncomputable def pe_xor_n7_d2 : MvPolynomial (Fin 7) ℚ →ₗ[ℚ] ℚ := by
  exact (Finsupp.linearCombination ℚ wpar_xor_n7_d2).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ)).toLinearMap

theorem pe_xor_n7_d2_monomial (α : Fin 7 →₀ ℕ) (c : ℚ) :
    pe_xor_n7_d2 (monomial α c) = c * wpar_xor_n7_d2 α := by
  unfold pe_xor_n7_d2
  rw [← single_eq_monomial]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
    smul_eq_mul]

theorem pe_xor_n7_d2_one : pe_xor_n7_d2 (1 : MvPolynomial (Fin 7) ℚ) = 1 := by
  rw [one_def, pe_xor_n7_d2_monomial]
  have h0 : oddSet (0 : Fin 7 →₀ ℕ) = ∅ := by
    ext i; simp [mem_oddSet]
  rw [wpar_xor_n7_d2, h0]
  norm_num

/-- The ±1 booleanity ideal `X i ^ 2 - 1` is killed UNCONDITIONALLY (adding 2 to
any exponent preserves the parity set).  Copied from Xor3Duality.pe3_bool_kill. -/
theorem xor_n7_d2_bool_kill (i : Fin 7) (p : MvPolynomial (Fin 7) ℚ) :
    pe_xor_n7_d2 ((X i ^ 2 - 1) * p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have h2 : (X i : MvPolynomial (Fin 7) ℚ) ^ 2 * monomial α c
        = monomial (Finsupp.single i 2 + α) c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [sub_mul, map_sub, h2, one_mul, pe_xor_n7_d2_monomial, pe_xor_n7_d2_monomial,
      wpar_xor_n7_d2, wpar_xor_n7_d2, oddSet_add_two, sub_self]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, add_zero]

/-- The ±1 booleanity constraint system. -/
noncomputable def xor_n7_d2System : Fin 7 → MvPolynomial (Fin 7) ℚ :=
  fun i => X i ^ 2 - 1

/-- CONDITIONAL MASTER: modulo the named square-nonnegativity hypothesis (the
moment-matrix PSD fact in functional form — the SDP leaf), NO degree-2 SoS
refutation of the ±1 booleanity system exists (cofactors of degree ≤ 4).
Structurally identical to Xor3Duality.petersen_no_refutation. -/
theorem xor_n7_d2_no_refutation
    (hsq : ∀ s : MvPolynomial (Fin 7) ℚ, s.totalDegree ≤ 2 →
      0 ≤ pe_xor_n7_d2 (s ^ 2)) :
    IsEmpty (SOSRefutation xor_n7_d2System 2 (fun _ => 4)) := by
  refine no_refutation _ 2 (fun _ => 4) pe_xor_n7_d2 pe_xor_n7_d2_one hsq ?_
  intro i p _
  rw [show pe_xor_n7_d2 (p * xor_n7_d2System i) = pe_xor_n7_d2 ((X i ^ 2 - 1) * p) from by
    rw [mul_comm]; rfl]
  exact xor_n7_d2_bool_kill i p

#print axioms xor_n7_d2_no_refutation

end PeDuality
