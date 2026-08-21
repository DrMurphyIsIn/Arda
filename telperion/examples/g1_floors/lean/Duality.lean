/- HAND-AUTHORED (not telperion-generated): the moment/SOS duality layer.

   Turns the PSD certificates of KnapsackSOS into REFUTATION-FORM lower
   bounds: a pseudoexpectation (linear functional, E 1 = 1, nonnegative on
   low-degree squares, killing the constraint ideal at admissible degrees)
   makes low-degree SOS refutations IMPOSSIBLE, by applying E to the
   would-be identity  -1 = Σ s_j² + Σ p_i·g_i.

   Contents:
   * `SOSRefutation` — degree-bounded Positivstellensatz refutations of a
     finite constraint system (squares of degree ≤ d, cofactors of degree
     ≤ dc — note dc ≤ 2d is MORE generous than the textbook bound on the
     products, so the nonexistence statement is stronger);
   * `no_refutation` — the abstract duality: any functional with the three
     pseudoexpectation properties blocks all refutations (four-line proof:
     linearity + sign);
   * `pe` — the knapsack fractional-hypergeometric pseudoexpectation as an
     honest LINEAR FUNCTIONAL on MvPolynomial (Fin N) ℚ, weighting each
     monomial by f(|support|) — the multilinearization is BUILT IN (the
     weight sees only the support), so the boolean ideal is killed
     UNCONDITIONALLY (`pe_bool_kill`, no degree guard);
   * `pe_lin_kill` — the linear constraint is killed at cofactor degree
     ≤ 2d < N.  THE TRUNCATION IS LOAD-BEARING: at a full-support monomial
     (|S| = N) the telescoping identity genuinely fails
     (N·f(N) ≠ (N/2)·f(N)), which is exactly why the bound is a LOWER
     bound and not a proof of consistency;
   * `knapsack_no_refutation` — the conditional master: modulo the named
     square-nonnegativity hypothesis (the moment-matrix PSD fact in
     functional form, whose block decomposition is kernel-checked in
     KnapsackSOS/BridgeD4 and whose harmonic-completeness assembly is the
     one Python-pinned layer), NO degree-d SOS refutation of the knapsack
     system exists, for every N > 2d.  Nonvacuity: for odd N the system
     really is infeasible (`KnapsackSOS.knapsack_unsat`). -/
import Mathlib
import KnapsackSOS

namespace KnapsackSOS
namespace Duality

open MvPolynomial

/-! ### Degree-bounded SOS refutations and the abstract obstruction -/

/-- A degree-bounded Positivstellensatz refutation of `{g i = 0}`:
`-1 = Σ s_j² + Σ p_i·g_i` with square degrees ≤ ds, cofactor degrees ≤ dc. -/
structure SOSRefutation {N : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → MvPolynomial (Fin N) ℚ) (ds : ℕ) (dc : ι → ℕ) where
  k : ℕ
  squares : Fin k → MvPolynomial (Fin N) ℚ
  sqDeg : ∀ j, (squares j).totalDegree ≤ ds
  cof : ι → MvPolynomial (Fin N) ℚ
  cofDeg : ∀ i, (cof i).totalDegree ≤ dc i
  identity : (-1 : MvPolynomial (Fin N) ℚ)
      = (∑ j, squares j ^ 2) + ∑ i, cof i * g i

/-- The abstract duality: a pseudoexpectation blocks all refutations. -/
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

/-! ### The knapsack pseudoexpectation as a linear functional -/

/-- Support of a shifted exponent vector: adding `single i k` (k ≠ 0)
inserts `i`. -/
theorem support_single_add {N : ℕ} {k : ℕ} (hk : k ≠ 0) (i : Fin N)
    (α : Fin N →₀ ℕ) :
    (Finsupp.single i k + α).support = insert i α.support := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp [Finsupp.mem_support_iff, Finsupp.single_apply, hk]
  · simp [Finsupp.mem_support_iff, Finsupp.single_apply, hj, Ne.symm hj]

/-- The fractional-hypergeometric pseudoexpectation, as a linear functional:
each monomial is weighted by f(rn, |exponent support|).  Multilinearization
is built in: the weight sees only WHICH variables occur, not their powers. -/
noncomputable def pe (rn : ℚ) {N : ℕ} : MvPolynomial (Fin N) ℚ →ₗ[ℚ] ℚ := by
  exact (Finsupp.linearCombination ℚ
      (fun α : Fin N →₀ ℕ => f rn α.support.card)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℚ)).toLinearMap

theorem pe_monomial (rn : ℚ) {N : ℕ} (α : Fin N →₀ ℕ) (c : ℚ) :
    pe rn (monomial α c) = c * f rn α.support.card := by
  unfold pe
  rw [← single_eq_monomial]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
    smul_eq_mul]

theorem pe_one (rn : ℚ) {N : ℕ} : pe rn (1 : MvPolynomial (Fin N) ℚ) = 1 := by
  rw [one_def, pe_monomial]
  simp [f]

/-- The boolean ideal is killed UNCONDITIONALLY: `x_i² − x_i` annihilates
against every polynomial, no degree guard (the weight only sees supports,
and `support(α + 2eᵢ) = support(α + eᵢ)`). -/
theorem pe_bool_kill (rn : ℚ) {N : ℕ} (i : Fin N)
    (p : MvPolynomial (Fin N) ℚ) :
    pe rn ((X i ^ 2 - X i) * p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have h2 : (X i : MvPolynomial (Fin N) ℚ) ^ 2 * monomial α c
        = monomial (Finsupp.single i 2 + α) c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have h1 : (X i : MvPolynomial (Fin N) ℚ) * monomial α c
        = monomial (Finsupp.single i 1 + α) c := by
      rw [X, monomial_mul, one_mul]
    rw [sub_mul, map_sub, h2, h1, pe_monomial, pe_monomial,
      support_single_add (by norm_num) i α,
      support_single_add (by norm_num) i α, sub_self]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, add_zero]

/-- Per-monomial linear-constraint kill, BELOW full support.  This is where
the truncation earns its keep: the hypothesis `α.support.card < N` is
genuinely necessary (at full support the telescoping identity fails). -/
theorem pe_lin_monomial (nq : ℚ) {N : ℕ} (α : Fin N →₀ ℕ) (c : ℚ)
    (hcard : α.support.card < N) (hnq : nq = (N : ℚ)) :
    pe nq (((∑ i, X i) - C (nq / 2)) * monomial α c) = 0 := by
  have hX : ∀ i : Fin N, (X i : MvPolynomial (Fin N) ℚ) * monomial α c
      = monomial (Finsupp.single i 1 + α) c := fun i => by
    rw [X, monomial_mul, one_mul]
  have hsupp : ∀ i : Fin N,
      (Finsupp.single i 1 + α).support = insert i α.support := fun i =>
    support_single_add one_ne_zero i α
  rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
  clear hsupp
  have hCm : (C (nq / 2) : MvPolynomial (Fin N) ℚ) * monomial α c
      = monomial α (nq / 2 * c) := by
    rw [C_mul_monomial]
  rw [hCm, pe_monomial]
  have hterm : ∀ i : Fin N, pe nq ((X i : MvPolynomial (Fin N) ℚ)
      * monomial α c) = c * f nq (insert i α.support).card := fun i => by
    rw [hX i, pe_monomial, support_single_add one_ne_zero i α]
  simp only [hterm]
  set k := α.support.card with hk
  have hsplit : ∑ i : Fin N, c * f nq (insert i α.support).card
      = k * (c * f nq k) + ((N : ℚ) - k) * (c * f nq (k + 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ α.support)]
    have hin : ∀ i ∈ Finset.univ.filter (· ∈ α.support),
        c * f nq (insert i α.support).card = c * f nq k := by
      intro i hi
      have : i ∈ α.support := (Finset.mem_filter.mp hi).2
      rw [Finset.insert_eq_self.mpr this]
    have hout : ∀ i ∈ Finset.univ.filter (¬ · ∈ α.support),
        c * f nq (insert i α.support).card = c * f nq (k + 1) := by
      intro i hi
      have hni : i ∉ α.support := (Finset.mem_filter.mp hi).2
      rw [Finset.card_insert_of_notMem hni]
    rw [Finset.sum_congr rfl hin, Finset.sum_congr rfl hout,
      Finset.sum_const, Finset.sum_const]
    have hcount_in : (Finset.univ.filter (· ∈ α.support)).card = k := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hcount_out : (Finset.univ.filter (¬ · ∈ α.support)).card = N - k := by
      have := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin N))) (p := (· ∈ α.support))
      have hN : (Finset.univ : Finset (Fin N)).card = N := by simp
      omega
    rw [hcount_in, hcount_out, nsmul_eq_mul, nsmul_eq_mul]
    push_cast [Nat.cast_sub (le_of_lt hcard)]
    ring
  rw [hsplit]
  have hkne : (k : ℚ) ≠ (N : ℚ) := by
    have : (k : ℚ) < N := by exact_mod_cast hcard
    linarith
  have hid := pseudoexpectation_ideal (N : ℚ) k hkne
  rw [hnq]
  linear_combination c * hid

/-- Exponent-sum dominates support cardinality. -/
theorem card_support_le_degree {N : ℕ} (α : Fin N →₀ ℕ) :
    α.support.card ≤ α.sum fun _ e => e := by
  rw [Finset.card_eq_sum_ones, Finsupp.sum]
  exact Finset.sum_le_sum fun i hi =>
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- The linear constraint is killed against every cofactor of degree < N. -/
theorem pe_lin_kill (nq : ℚ) {N : ℕ} (p : MvPolynomial (Fin N) ℚ)
    (hdeg : p.totalDegree < N) (hnq : nq = (N : ℚ)) :
    pe nq (((∑ i, X i) - C (nq / 2)) * p) = 0 := by
  -- decompose over the ACTUAL support (structural induction would be wrong:
  -- summands of a low-degree polynomial can individually have high degree)
  have hdecomp : ((∑ i, X i) - C (nq / 2)) * p
      = ∑ α ∈ p.support, ((∑ i, X i) - C (nq / 2)) * monomial α (coeff α p) := by
    rw [← Finset.mul_sum, ← as_sum p]
  rw [hdecomp, map_sum]
  refine Finset.sum_eq_zero fun α hα => ?_
  exact pe_lin_monomial nq α _
    (lt_of_le_of_lt (le_trans (card_support_le_degree α) (le_totalDegree hα))
      hdeg) hnq

/-! ### The knapsack system and the conditional master theorem -/

/-- The knapsack constraint system: booleanity per variable + the linear
constraint `Σ x_i = N/2`. -/
noncomputable def knapsackSystem (N : ℕ) : Fin N ⊕ Unit → MvPolynomial (Fin N) ℚ
  | .inl i => X i ^ 2 - X i
  | .inr _ => (∑ i, X i) - C ((N : ℚ) / 2)

/-- CONDITIONAL MASTER: modulo the named square-nonnegativity hypothesis
(the moment-matrix PSD fact in functional form; its block decomposition is
kernel-checked, its harmonic-completeness assembly is the one Python-pinned
layer), NO SOS refutation of the knapsack system with squares of degree ≤ d
and cofactors of degree ≤ 2d exists, for any N > 2d.  For odd N the system
is genuinely infeasible (`KnapsackSOS.knapsack_unsat`): the refuted
statement is true, and low-degree SOS cannot prove it. -/
theorem knapsack_no_refutation (N d : ℕ) (hd : 2 * d < N)
    (hsq : ∀ s : MvPolynomial (Fin N) ℚ, s.totalDegree ≤ d →
      0 ≤ pe (N : ℚ) (s ^ 2)) :
    IsEmpty (SOSRefutation (knapsackSystem N) d (fun _ => 2 * d)) := by
  refine no_refutation _ d (fun _ => 2 * d) (pe (N : ℚ)) (pe_one _) hsq ?_
  rintro (i | _) p hp
  · rw [show pe (N:ℚ) (p * knapsackSystem N (.inl i))
        = pe (N:ℚ) ((X i ^ 2 - X i) * p) from by
      rw [mul_comm]; rfl]
    exact pe_bool_kill _ i p
  · rw [show pe (N:ℚ) (p * knapsackSystem N (.inr ()))
        = pe (N:ℚ) (((∑ i, X i) - C ((N:ℚ) / 2)) * p) from by
      rw [mul_comm]; rfl]
    exact pe_lin_kill _ p (lt_of_le_of_lt hp hd) rfl

end Duality
end KnapsackSOS

#print axioms KnapsackSOS.Duality.no_refutation
#print axioms KnapsackSOS.Duality.pe_bool_kill
#print axioms KnapsackSOS.Duality.pe_lin_kill
#print axioms KnapsackSOS.Duality.knapsack_no_refutation
