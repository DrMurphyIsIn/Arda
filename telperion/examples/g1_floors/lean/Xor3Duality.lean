/- HAND-AUTHORED (not telperion-generated): the 3XOR duality layer, stage B —
   the Petersen pseudoexpectation as a linear functional on MvPolynomial,
   with the parity (±1-booleanity) kill.

   Semantics: variables are ±1-valued, so x_i² = 1 and a monomial's value
   depends only on the PARITY of each exponent.  The pseudoexpectation
   weights a monomial by the Petersen closure sign of the bitmask of its
   odd-exponent variables:  w(α) = sgn(maskOf(oddSet α)), with sgn the
   kernel-checked width-4 closure table of PetersenCertificate and maskOf
   the Finset↔bitmask homomorphism of Xor3Mask.

   Proven here (stage B):
   * `pe3` — the functional (Finsupp.linearCombination ∘ coeffLinearEquiv,
     same construction as Duality.pe);
   * `oddSet_add` — parity is a Δ-homomorphism: oddSet(α+β) =
     oddSet α ∆ oddSet β (the multilinearization law for ±1 semantics);
   * `pe3_bool_kill` — the ±1-booleanity ideal (x_i² − 1) is killed
     UNCONDITIONALLY (adding 2 to an exponent never changes parity).

   Stage C (queued): the clause kill via PetersenCertificate's
   constraint_respect + degree guard, the PSD bridge (pe3 on squares →
   QuadForm grouping by oddMask → petersen_moment_psd via the
   ∅/{i}/{i,j} index decides), and the refutation-form master. -/
import Mathlib
import Xor3Mask
import PetersenCertificate

namespace Xor3Duality

open MvPolynomial Xor3Mask
open scoped symmDiff

/-- The odd-exponent variable set of a monomial exponent vector. -/
def oddSet (α : Fin 15 →₀ ℕ) : Finset (Fin 15) :=
  α.support.filter (fun i => α i % 2 = 1)

theorem mem_oddSet {α : Fin 15 →₀ ℕ} {i : Fin 15} :
    i ∈ oddSet α ↔ α i % 2 = 1 := by
  simp only [oddSet, Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by omega, h⟩

/-- Parity is a symmetric-difference homomorphism: the multilinearization
law of ±1 semantics. -/
theorem oddSet_add (α β : Fin 15 →₀ ℕ) :
    oddSet (α + β) = oddSet α ∆ oddSet β := by
  ext i
  rw [Finset.mem_symmDiff]
  simp only [mem_oddSet, Finsupp.add_apply]
  omega

/-- The Petersen pseudoexpectation weight: closure sign of the parity mask. -/
noncomputable def w3 (α : Fin 15 →₀ ℕ) : ℚ :=
  ((PetersenCertificate.sgn (maskOf (oddSet α)) : ℤ) : ℚ)

/-- The 3XOR pseudoexpectation as a linear functional. -/
noncomputable def pe3 : MvPolynomial (Fin 15) ℚ →ₗ[ℚ] ℚ := by
  exact (Finsupp.linearCombination ℚ w3).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ)).toLinearMap

theorem pe3_monomial (α : Fin 15 →₀ ℕ) (c : ℚ) :
    pe3 (monomial α c) = c * w3 α := by
  unfold pe3
  rw [← single_eq_monomial]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
    smul_eq_mul]

theorem pe3_one : pe3 (1 : MvPolynomial (Fin 15) ℚ) = 1 := by
  rw [one_def, pe3_monomial]
  have h0 : oddSet (0 : Fin 15 →₀ ℕ) = ∅ := by
    ext i; simp [mem_oddSet]
  rw [w3, h0, maskOf_empty, PetersenCertificate.sgn_zero]
  norm_num

/-- Adding 2 to any exponent preserves the parity set. -/
theorem oddSet_add_two (i : Fin 15) (α : Fin 15 →₀ ℕ) :
    oddSet (Finsupp.single i 2 + α) = oddSet α := by
  ext j
  simp only [mem_oddSet, Finsupp.add_apply, Finsupp.single_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij]

/-- The ±1-booleanity ideal (x_i² − 1) is killed UNCONDITIONALLY. -/
theorem pe3_bool_kill (i : Fin 15) (p : MvPolynomial (Fin 15) ℚ) :
    pe3 ((X i ^ 2 - 1) * p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have h2 : (X i : MvPolynomial (Fin 15) ℚ) ^ 2 * monomial α c
        = monomial (Finsupp.single i 2 + α) c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [sub_mul, map_sub, h2, one_mul, pe3_monomial, pe3_monomial,
      w3, w3, oddSet_add_two, sub_self]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, add_zero]

end Xor3Duality

#print axioms Xor3Duality.oddSet_add
#print axioms Xor3Duality.pe3_one
#print axioms Xor3Duality.pe3_bool_kill
