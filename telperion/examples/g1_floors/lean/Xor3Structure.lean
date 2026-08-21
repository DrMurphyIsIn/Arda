/- HAND-AUTHORED (not telperion-generated): the 3XOR structure theorem.

   Schoenebeck/Grigoriev 3XOR pseudoexpectations have moment matrices
   M[S,T] = E[x_{S xor T}] that are block-diagonal over GF(2) derivability
   classes with +-1 rank-one blocks; PSDness is COMBINATORIAL CONSISTENCY,
   not eigenvalue analysis.  Validated exactly per instance by
   telperion/examples/knapsack_sos/xor3_pseudoexpectation.py (Tseitin on the
   Petersen graph: UNSAT, refutation width exactly 6, 121x121 moment matrix
   = exact block-rank-one over 61 classes).

   This file proves the generic theorems that turn a per-instance closure
   certificate into PSDness, kernel-checked:

   * `block_quadform_nonneg` -- a matrix of the exact block form
     M[S,T] = [cls S = cls T] * sigma_S * sigma_T has nonnegative quadratic
     form (sum over classes of squares);
   * `consistent_kernel_quadform_nonneg` -- the ABSTRACT structure theorem:
     any reflexive (D S S = 1), symmetric, PARTIALLY MULTIPLICATIVE kernel
     (D S U = D S T * D T U whenever both factors are nonzero) has
     nonnegative quadratic form.  The class function is constructed as the
     neighborhood predicate cls S = (D S . != 0), the sign as the value
     against an epsilon-chosen class representative; +-1-ness of values is
     DERIVED (D S T^2 = 1 on nonzeros), not assumed;
   * `xor3_moment_quadform_nonneg` -- the 3XOR instantiation: the moment
     matrix built from a sign map on a closure support Λ over symmetric
     differences is PSD, under hypotheses that are exactly what the
     per-instance verifier checks (empty set in Λ with sign 1, and the
     closure/multiplicativity condition on the index range -- nonvanishing
     of sgn on the support turned out to be unnecessary).

   The layer that ESTABLISHES those hypotheses for a concrete instance
   (BFS closure conflict-freeness; expansion => width for the asymptotic
   statement) is the emitter's job / honest-conditional assembly -- future
   work, tracked in the README. -/
import Mathlib

namespace Xor3Structure

open Finset
open scoped symmDiff

/-! ### Generic block rank-one PSD -/

/-- A matrix with exact block form `[cls S = cls T] * sigma S * sigma T` has
nonnegative quadratic form: it is the direct sum over classes of rank-one
squares. -/
theorem block_quadform_nonneg {ι β : Type*} [Fintype ι] [DecidableEq β]
    (cls : ι → β) (σ : ι → ℚ) (M : ι → ι → ℚ)
    (hM : ∀ S T, M S T = if cls S = cls T then σ S * σ T else 0)
    (x : ι → ℚ) : 0 ≤ ∑ S, ∑ T, x S * M S T * x T := by
  classical
  set y : ι → ℚ := fun S => σ S * x S with hy
  have key : ∑ S, ∑ T, x S * M S T * x T
      = ∑ c ∈ Finset.univ.image cls,
          (∑ S ∈ Finset.univ.filter (fun S => cls S = c), y S) ^ 2 := by
    calc ∑ S, ∑ T, x S * M S T * x T
        = ∑ S, y S * ∑ T ∈ Finset.univ.filter (fun T => cls T = cls S), y T := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [hM]
          by_cases h : cls S = cls T
          · rw [if_pos h, if_pos h.symm, hy]; ring
          · rw [if_neg h, if_neg fun hh => h hh.symm]; ring
      _ = ∑ c ∈ Finset.univ.image cls,
            ∑ S ∈ Finset.univ.filter (fun S => cls S = c),
              y S * ∑ T ∈ Finset.univ.filter (fun T => cls T = cls S), y T := by
          rw [Finset.sum_fiberwise_of_maps_to
            (fun S _ => Finset.mem_image_of_mem cls (Finset.mem_univ S))]
      _ = ∑ c ∈ Finset.univ.image cls,
            (∑ S ∈ Finset.univ.filter (fun S => cls S = c), y S) ^ 2 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun S hS => ?_
          rw [(Finset.mem_filter.mp hS).2]
  rw [key]
  exact Finset.sum_nonneg fun c _ => sq_nonneg _

/-! ### The abstract structure theorem -/

/-- Partially multiplicative +-kernels are PSD.  Hypotheses: reflexivity
`D S S = 1`, symmetry, and multiplicativity on nonzeros.  Note +-1-ness of
the nonzero values is a consequence (`D S T * D T S = D S S = 1`), and the
block structure is constructed, not assumed. -/
theorem consistent_kernel_quadform_nonneg {ι : Type*} [Fintype ι]
    (D : ι → ι → ℚ)
    (h1 : ∀ S, D S S = 1)
    (h2 : ∀ S T, D S T = D T S)
    (h3 : ∀ S T U, D S T ≠ 0 → D T U ≠ 0 → D S U = D S T * D T U)
    (x : ι → ℚ) : 0 ≤ ∑ S, ∑ T, x S * D S T * x T := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · simp
  -- class predicate: the nonzero-neighborhood of S
  set cls : ι → (ι → Prop) := fun S U => D S U ≠ 0 with hcls
  have hrel₁ : ∀ S T, cls S = cls T → D S T ≠ 0 := by
    intro S T h
    have hTT : cls T T := by simp only [hcls]; rw [h1]; exact one_ne_zero
    have hST : cls S T := h ▸ hTT
    simpa only [hcls] using hST
  have hrel₂ : ∀ S T, D S T ≠ 0 → cls S = cls T := by
    intro S T h
    funext U
    simp only [hcls]
    apply propext
    constructor
    · intro hSU
      have hTS : D T S ≠ 0 := fun hz => h (by rw [h2]; exact hz)
      rw [h3 T S U hTS hSU]
      exact mul_ne_zero hTS hSU
    · intro hTU
      rw [h3 S T U h hTU]
      exact mul_ne_zero h hTU
  -- representative of each class via epsilon, sign against the representative
  set rep : (ι → Prop) → ι := fun c => Classical.epsilon (fun T => cls T = c)
    with hrep_def
  have hrep : ∀ S, cls (rep (cls S)) = cls S := fun S =>
    Classical.epsilon_spec (⟨S, rfl⟩ : ∃ T, cls T = cls S)
  set σ : ι → ℚ := fun S => D S (rep (cls S)) with hσ
  have hM : ∀ S T, D S T = if cls S = cls T then σ S * σ T else 0 := by
    intro S T
    by_cases h : cls S = cls T
    · rw [if_pos h]
      have hSR : D S (rep (cls S)) ≠ 0 := hrel₁ S _ (hrep S).symm
      have hTR : D T (rep (cls T)) ≠ 0 := hrel₁ T _ (hrep T).symm
      have hRT : D (rep (cls S)) T ≠ 0 := by
        rw [h, h2]; exact hTR
      have hexp := h3 S (rep (cls S)) T hSR hRT
      rw [hexp]
      simp only [hσ]
      rw [h, h2 (rep (cls T)) T]
    · rw [if_neg h]
      by_contra hz
      exact h (hrel₂ S T hz)
  exact block_quadform_nonneg cls σ D hM x

/-! ### The 3XOR instantiation -/

/-- The degree-d 3XOR moment matrix from a closure certificate (Λ, sgn):
M[S,T] = sgn(S xor T) if S xor T is in the closure support, else 0. -/
def xorMoment {n : ℕ} (Λ : Finset (Finset (Fin n)))
    (sgn : Finset (Fin n) → ℚ) (S T : Finset (Fin n)) : ℚ :=
  if S ∆ T ∈ Λ then sgn (S ∆ T) else 0

/-- THE 3XOR STRUCTURE THEOREM: conflict-free closure data yields a PSD
moment matrix.  The hypotheses are exactly the finite conditions the
per-instance verifier (xor3_pseudoexpectation.py) checks on the index range:
the empty set is in the support with sign 1, and the closure is
sum-closed with multiplicative signs across index differences.  No
nonvanishing or +-1 assumption on sgn is needed at all: zero signs on the
support are handled by the abstract kernel theorem's class construction. -/
theorem xor3_moment_quadform_nonneg {n d : ℕ}
    (Λ : Finset (Finset (Fin n))) (sgn : Finset (Fin n) → ℚ)
    (hempty : ∅ ∈ Λ) (hone : sgn ∅ = 1)
    (hmul : ∀ S T U : Finset (Fin n), S.card ≤ d → T.card ≤ d → U.card ≤ d →
      S ∆ T ∈ Λ → T ∆ U ∈ Λ →
      S ∆ U ∈ Λ ∧ sgn (S ∆ U) = sgn (S ∆ T) * sgn (T ∆ U))
    (x : {S : Finset (Fin n) // S.card ≤ d} → ℚ) :
    0 ≤ ∑ S, ∑ T, x S * xorMoment Λ sgn S.val T.val * x T := by
  classical
  refine consistent_kernel_quadform_nonneg
    (fun S T : {S : Finset (Fin n) // S.card ≤ d} => xorMoment Λ sgn S.val T.val)
    ?_ ?_ ?_ x
  · intro S
    simp [xorMoment, symmDiff_self, bot_eq_empty, hempty, hone]
  · intro S T
    simp [xorMoment, symmDiff_comm]
  · intro S T U hST hTU
    have hSTmem : S.val ∆ T.val ∈ Λ := by
      by_contra hmem
      exact hST (by simp [xorMoment, hmem])
    have hTUmem : T.val ∆ U.val ∈ Λ := by
      by_contra hmem
      exact hTU (by simp [xorMoment, hmem])
    obtain ⟨hSUmem, hsgn⟩ :=
      hmul S.val T.val U.val S.property T.property U.property hSTmem hTUmem
    simp [xorMoment, hSTmem, hTUmem, hSUmem, hsgn]

end Xor3Structure

#print axioms Xor3Structure.block_quadform_nonneg
#print axioms Xor3Structure.consistent_kernel_quadform_nonneg
#print axioms Xor3Structure.xor3_moment_quadform_nonneg
