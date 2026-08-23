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
import Duality
import QuadForm

set_option maxRecDepth 100000

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


/-! ### Stage C: the clause system, clause kill, PSD bridge, and master -/

section StageC
open KnapsackSOS.Duality

/-- The ten Tseitin clauses of the Petersen instance: (edge set, charge).
Decoded from PetersenCertificate.clausePairs; the link is kernel-checked
in `clauseData_mask` below. -/
def clauseData : Fin 10 → (Finset (Fin 15) × ℤ) :=
  ![({0, 1, 2}, -1), ({0, 3, 4}, 1), ({3, 5, 6}, 1), ({5, 7, 8}, 1),
    ({1, 7, 9}, 1), ({2, 10, 11}, 1), ({4, 12, 13}, 1), ({6, 10, 14}, 1),
    ({8, 11, 12}, 1), ({9, 13, 14}, 1)]

theorem clauseData_mask : ∀ k : Fin 10,
    (maskOf (clauseData k).1, (clauseData k).2)
      ∈ PetersenCertificate.clausePairs := by decide

theorem clauseData_sign : ∀ k : Fin 10,
    (clauseData k).2 = 1 ∨ (clauseData k).2 = -1 := by decide

/-- Exponent vector of the multilinear monomial on a variable set. -/
noncomputable def expOf (A : Finset (Fin 15)) : Fin 15 →₀ ℕ :=
  A.sum fun i => Finsupp.single i 1

theorem expOf_apply (A : Finset (Fin 15)) (j : Fin 15) :
    expOf A j = if j ∈ A then 1 else 0 := by
  classical
  rw [expOf, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_ite_eq]

theorem oddSet_expOf (A : Finset (Fin 15)) : oddSet (expOf A) = A := by
  ext j
  rw [mem_oddSet, expOf_apply]
  by_cases h : j ∈ A <;> simp [h]

/-- The clause polynomial x_A − e (multilinear monomial minus the charge). -/
noncomputable def clausePoly (k : Fin 10) : MvPolynomial (Fin 15) ℚ :=
  monomial (expOf (clauseData k).1) 1 - C (((clauseData k).2 : ℤ) : ℚ)

/-- Honesty: the clause monomial IS the product of its variables. -/
theorem monomial_expOf_eq_prod (A : Finset (Fin 15)) :
    (monomial (expOf A) 1 : MvPolynomial (Fin 15) ℚ) = ∏ i ∈ A, X i := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [expOf]
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, ← ih, X, monomial_mul, one_mul,
      show expOf (insert i A) = Finsupp.single i 1 + expOf A from by
        rw [expOf, Finset.sum_insert hi]; rfl]

/-! Small decides: guards and index membership for the tiny mask shapes. -/

theorem pop_zero_le : PetersenCertificate.pop 16 0 ≤ 4 := by decide

theorem pop_single_le : ∀ i : Fin 15,
    PetersenCertificate.pop 16 (2 ^ (i : ℕ)) ≤ 4 := by decide

theorem guard_zero : ∀ k : Fin 10,
    PetersenCertificate.pop 16 ((0 : ℕ) ^^^ maskOf (clauseData k).1) ≤ 4 := by
  decide

theorem guard_single : ∀ k : Fin 10, ∀ i : Fin 15,
    PetersenCertificate.pop 16 (2 ^ (i : ℕ) ^^^ maskOf (clauseData k).1) ≤ 4 := by
  decide

theorem zero_mem_idx : (0 : ℕ) ∈ PetersenCertificate.idxList := by decide

theorem pow_mem_idx : ∀ i : Fin 15,
    2 ^ (i : ℕ) ∈ PetersenCertificate.idxList := by decide

theorem pair_mem_idx : ∀ i j : Fin 15, i ≠ j →
    2 ^ (i : ℕ) ||| 2 ^ (j : ℕ) ∈ PetersenCertificate.idxList := by decide

/-- Masks of degree-≤2 sets are indexed (the ∅/{i}/{i,j} split — no
popcount theory). -/
theorem mask_mem_idx (S : Finset (Fin 15)) (hc : S.card ≤ 2) :
    maskOf S ∈ PetersenCertificate.idxList := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero.mp h, maskOf_empty]
    exact zero_mem_idx
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    rw [maskOf_singleton]
    exact pow_mem_idx i
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h
    rw [maskOf_pair hij]
    exact pair_mem_idx i j hij

/-- The mask-level clause kill: the closure sign is multiplicative against
any in-width clause, on BOTH sides of the truncation boundary (off-closure
signs vanish coherently). -/
theorem sgn_clause (c : ℕ) (eZ : ℤ)
    (hc : (c, eZ) ∈ PetersenCertificate.clausePairs)
    (heZ : eZ = 1 ∨ eZ = -1) (mm : ℕ)
    (h1 : PetersenCertificate.pop 16 mm ≤ 4)
    (h2 : PetersenCertificate.pop 16 (mm ^^^ c) ≤ 4) :
    PetersenCertificate.sgn (mm ^^^ c)
      = eZ * PetersenCertificate.sgn mm := by
  classical
  by_cases hmem : mm ∈ PetersenCertificate.lam
  · exact PetersenCertificate.constraint_respect (c, eZ) hc mm hmem h2
  · have h0 : PetersenCertificate.sgn mm = 0 := by
      by_contra hne
      exact hmem (PetersenCertificate.sgn_ne_zero_mem hne)
    by_cases hmem2 : (mm ^^^ c) ∈ PetersenCertificate.lam
    · have hr := PetersenCertificate.constraint_respect (c, eZ) hc
        (mm ^^^ c) hmem2 (by
          rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          exact h1)
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, h0] at hr
      rcases heZ with rfl | rfl <;> omega
    · have h02 : PetersenCertificate.sgn (mm ^^^ c) = 0 := by
        by_contra hne
        exact hmem2 (PetersenCertificate.sgn_ne_zero_mem hne)
      rw [h0, h02, mul_zero]

/-- The clause ideal is killed against cofactors of degree ≤ 1 (parity
masks stay within the width-4 closure; the truncation is load-bearing
exactly as in the knapsack case). -/
theorem pe3_clause_kill (k : Fin 10) (p : MvPolynomial (Fin 15) ℚ)
    (hdeg : p.totalDegree ≤ 1) :
    pe3 (clausePoly k * p) = 0 := by
  classical
  have hdecomp : clausePoly k * p
      = ∑ α ∈ p.support, clausePoly k * monomial α (coeff α p) := by
    rw [← Finset.mul_sum, ← as_sum p]
  rw [hdecomp, map_sum]
  refine Finset.sum_eq_zero fun α hα => ?_
  -- the parity set of α has at most one element
  have hcard : (oddSet α).card ≤ 1 := by
    have h1 : (oddSet α).card ≤ α.support.card := Finset.card_filter_le _ _
    have h2 : α.support.card ≤ α.sum fun _ e => e :=
      KnapsackSOS.Duality.card_support_le_degree α
    have h3 : (α.sum fun _ e => e) ≤ p.totalDegree := le_totalDegree hα
    omega
  -- expand the clause action on the monomial
  rw [clausePoly, sub_mul, map_sub, monomial_mul, one_mul, C_mul_monomial,
    pe3_monomial, pe3_monomial, w3, w3, oddSet_add, oddSet_expOf,
    maskOf_symmDiff]
  -- the mask-level identity
  have key : PetersenCertificate.sgn
        (maskOf (clauseData k).1 ^^^ maskOf (oddSet α))
      = (clauseData k).2 * PetersenCertificate.sgn (maskOf (oddSet α)) := by
    rw [Nat.xor_comm]
    interval_cases h : (oddSet α).card
    · rw [Finset.card_eq_zero.mp h, maskOf_empty]
      exact sgn_clause _ _ (clauseData_mask k) (clauseData_sign k) 0
        pop_zero_le (guard_zero k)
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
      rw [hi, maskOf_singleton]
      exact sgn_clause _ _ (clauseData_mask k) (clauseData_sign k) _
        (pop_single_le i) (guard_single k i)
  push_cast [key]
  ring

/-! ### The PSD bridge -/

/-- Parity mask of an exponent vector. -/
def g3 (α : Fin 15 →₀ ℕ) : ℕ := maskOf (oddSet α)

/-- The moment kernel in mask coordinates. -/
def K3 (v v' : ℕ) : ℚ := ((PetersenCertificate.sgn (v ^^^ v') : ℤ) : ℚ)

theorem w3_add (α β : Fin 15 →₀ ℕ) : w3 (α + β) = K3 (g3 α) (g3 β) := by
  rw [w3, K3, g3, g3, oddSet_add, maskOf_symmDiff]

theorem pe3_sq (s : MvPolynomial (Fin 15) ℚ) :
    pe3 (s ^ 2) = ∑ α ∈ s.support, ∑ β ∈ s.support,
      coeff α s * coeff β s * K3 (g3 α) (g3 β) := by
  conv_lhs => rw [sq, as_sum s, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [monomial_mul, pe3_monomial, w3_add]

/-- Reindex a sum over the 121 certificate indices as a sum over the
distinct index masks. -/
theorem sum_m_eq_toFinset (h : ℕ → ℚ) :
    ∑ i : Fin 121, h (PetersenCertificate.m i)
      = ∑ v ∈ PetersenCertificate.idxList.toFinset, h v := by
  classical
  have hlen : PetersenCertificate.idxList.length = 121 := by decide
  have hnd : PetersenCertificate.idxList.Nodup := by decide
  have hm : ∀ i : Fin 121, PetersenCertificate.m i
      = PetersenCertificate.idxList[(i : ℕ)]'(by omega) := by
    intro i
    show PetersenCertificate.idxList.getD (i : ℕ) 0 = _
    rw [List.getD_eq_getElem]
  refine Finset.sum_bij (fun i _ => PetersenCertificate.m i) ?_ ?_ ?_ ?_
  · intro i _
    rw [hm]
    exact List.mem_toFinset.mpr (List.getElem_mem _)
  · intro i _ j _ hij
    rw [hm, hm] at hij
    have := (List.Nodup.getElem_inj_iff hnd).mp hij
    exact Fin.ext this
  · intro v hv
    obtain ⟨idx, hidx, rfl⟩ :=
      List.mem_iff_getElem.mp (List.mem_toFinset.mp hv)
    exact ⟨⟨idx, by omega⟩, Finset.mem_univ _, by rw [hm]⟩
  · intro a _
    rfl

/-- pe3 is nonnegative on squares of degree ≤ 2: the whole bridge. -/
theorem hsq3 : ∀ s : MvPolynomial (Fin 15) ℚ, s.totalDegree ≤ 2 →
    0 ≤ pe3 (s ^ 2) := by
  classical
  intro s hs
  rw [pe3_sq, QuadForm.sum_mul_sum_fiberwise s.support g3
    (fun α => coeff α s) K3]
  set C : ℕ → ℚ :=
    fun v => ∑ α ∈ s.support.filter (g3 · = v), coeff α s with hC
  have himg : s.support.image g3 ⊆ PetersenCertificate.idxList.toFinset := by
    intro v hv
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hv
    refine List.mem_toFinset.mpr (mask_mem_idx (oddSet α) ?_)
    have h1 : (oddSet α).card ≤ α.support.card := Finset.card_filter_le _ _
    have h2 : α.support.card ≤ α.sum fun _ e => e :=
      KnapsackSOS.Duality.card_support_le_degree α
    have h3 : (α.sum fun _ e => e) ≤ s.totalDegree := le_totalDegree hα
    omega
  have hCzero : ∀ v ∈ PetersenCertificate.idxList.toFinset,
      v ∉ s.support.image g3 → C v = 0 := by
    intro v _ hv
    refine Finset.sum_eq_zero fun α hα => ?_
    exfalso
    exact hv ((Finset.mem_filter.mp hα).2 ▸
      Finset.mem_image_of_mem g3 (Finset.mem_filter.mp hα).1)
  rw [QuadForm.grouped_extend (s.support.image g3)
    PetersenCertificate.idxList.toFinset himg C K3 hCzero]
  rw [← sum_m_eq_toFinset (fun v =>
    ∑ v' ∈ PetersenCertificate.idxList.toFinset, C v * C v' * K3 v v')]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    (sum_m_eq_toFinset (fun v' =>
      C (PetersenCertificate.m i) * C v' * K3 (PetersenCertificate.m i) v')).symm]
  have hfinal : ∑ i : Fin 121, ∑ j : Fin 121,
      C (PetersenCertificate.m i) * C (PetersenCertificate.m j)
        * K3 (PetersenCertificate.m i) (PetersenCertificate.m j)
      = ∑ i : Fin 121, ∑ j : Fin 121,
        (fun t => C (PetersenCertificate.m t)) i * PetersenCertificate.D i j
          * (fun t => C (PetersenCertificate.m t)) j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = C (PetersenCertificate.m i) * PetersenCertificate.D i j
      * C (PetersenCertificate.m j)
    rw [show PetersenCertificate.D i j
        = K3 (PetersenCertificate.m i) (PetersenCertificate.m j) from rfl]
    ring
  rw [hfinal]
  exact PetersenCertificate.petersen_moment_psd _

/-! ### The refutation-form master -/

/-- The Petersen Tseitin constraint system: ten clauses + fifteen ±1
booleanity constraints. -/
noncomputable def petersenSystem :
    Fin 10 ⊕ Fin 15 → MvPolynomial (Fin 15) ℚ :=
  Sum.elim clausePoly (fun i => X i ^ 2 - 1)

/-- UNCONDITIONAL: no SOS refutation of the Petersen Tseitin system with
squares of degree ≤ 2, clause cofactors of degree ≤ 1, and boolean
cofactors of degree ≤ 4 exists. The refuted system is genuinely
contradictory (PetersenCertificate.refutation_certificate): the second
fully kernel-checked end-to-end refutation-form lower bound of the
pipeline, this time for 3XOR. -/
theorem petersen_no_refutation :
    IsEmpty (SOSRefutation petersenSystem 2
      (Sum.elim (fun _ => 1) (fun _ => 4))) := by
  refine no_refutation _ 2 _ pe3 pe3_one hsq3 ?_
  rintro (k | i) p hp
  · rw [show pe3 (p * petersenSystem (.inl k))
        = pe3 (clausePoly k * p) from by rw [mul_comm]; rfl]
    exact pe3_clause_kill k p hp
  · rw [show pe3 (p * petersenSystem (.inr i))
        = pe3 ((X i ^ 2 - 1) * p) from by rw [mul_comm]; rfl]
    exact pe3_bool_kill i p

end StageC

end Xor3Duality

#print axioms Xor3Duality.oddSet_add
#print axioms Xor3Duality.pe3_one
#print axioms Xor3Duality.pe3_bool_kill
#print axioms Xor3Duality.pe3_clause_kill
#print axioms Xor3Duality.hsq3
#print axioms Xor3Duality.petersen_no_refutation
