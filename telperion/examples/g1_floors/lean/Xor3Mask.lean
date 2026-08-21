/- HAND-AUTHORED (not telperion-generated): the Finset ↔ Nat-bitmask bridge
   for the 3XOR duality layer.

   `maskOf` encodes a Finset (Fin n) as a Nat bitmask via a lor-fold, so
   symmetric difference becomes kernel-accelerated XOR:
   `maskOf (S ∆ T) = maskOf S ^^^ maskOf T` (proved bitwise via testBit).
   This connects the MvPolynomial parity semantics of the 3XOR
   pseudoexpectation to the mask-level Petersen certificate data
   (PetersenCertificate.sgn, idxList) without any popcount theory: the
   index-membership facts needed downstream are obtained by small decides
   over the ∅ / {i} / {i,j} case split, not by a fueled-popcount
   correspondence. -/
import Mathlib

namespace Xor3Mask

open scoped symmDiff

variable {n : ℕ}

/-- Bitmask of a finite set of variable indices (lor-fold of powers of 2). -/
def maskOf (S : Finset (Fin n)) : ℕ :=
  S.fold (· ||| ·) 0 (fun i : Fin n => (2 : ℕ) ^ (i : ℕ))

theorem maskOf_empty : maskOf (∅ : Finset (Fin n)) = 0 := rfl

theorem maskOf_insert {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S) :
    maskOf (insert i S) = 2 ^ (i : ℕ) ||| maskOf S :=
  Finset.fold_insert hi

/-- Bit `j` of the mask is set iff some element of `S` has value `j`. -/
theorem testBit_maskOf (S : Finset (Fin n)) (j : ℕ) :
    (maskOf S).testBit j = true ↔ ∃ i ∈ S, (i : ℕ) = j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [maskOf_empty]
  | insert i S hi ih =>
    rw [maskOf_insert hi, Nat.testBit_or]
    simp only [Bool.or_eq_true, ih, Nat.testBit_two_pow]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact ⟨i, Finset.mem_insert_self i S, by simpa [eq_comm] using h⟩
      · exact ⟨a, Finset.mem_insert_of_mem ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · left; simp
      · right; exact ⟨a, ha', rfl⟩

/-- In-range bits are decidable membership of the corresponding element. -/
theorem testBit_maskOf_lt (S : Finset (Fin n)) {j : ℕ} (hj : j < n) :
    (maskOf S).testBit j = decide ((⟨j, hj⟩ : Fin n) ∈ S) := by
  rw [Bool.eq_iff_iff, testBit_maskOf, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (Fin.eta i hj).symm ▸ hi
  · intro h
    exact ⟨⟨j, hj⟩, h, rfl⟩

/-- Out-of-range bits are clear. -/
theorem testBit_maskOf_ge (S : Finset (Fin n)) {j : ℕ} (hj : ¬ j < n) :
    (maskOf S).testBit j = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨i, _, rfl⟩ := (testBit_maskOf S _).mp h
  exact hj i.isLt

/-- THE HOMOMORPHISM: symmetric difference of sets is XOR of masks. -/
theorem maskOf_symmDiff (S T : Finset (Fin n)) :
    maskOf (S ∆ T) = maskOf S ^^^ maskOf T := by
  classical
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  by_cases hj : j < n
  · rw [testBit_maskOf_lt (S ∆ T) hj, testBit_maskOf_lt S hj,
      testBit_maskOf_lt T hj]
    by_cases hS : (⟨j, hj⟩ : Fin n) ∈ S <;>
      by_cases hT : (⟨j, hj⟩ : Fin n) ∈ T <;>
        simp [Finset.mem_symmDiff, hS, hT]
  · rw [testBit_maskOf_ge (S ∆ T) hj, testBit_maskOf_ge S hj,
      testBit_maskOf_ge T hj]
    rfl

/-- Masks determine sets (needed to transport Nodup/index facts). -/
theorem maskOf_injective : Function.Injective (maskOf (n := n)) := by
  classical
  intro S T h
  ext i
  have hb : (maskOf S).testBit (i : ℕ) = (maskOf T).testBit (i : ℕ) := by
    rw [h]
  rw [testBit_maskOf_lt S i.isLt, testBit_maskOf_lt T i.isLt] at hb
  simpa [Fin.eta] using decide_eq_decide.mp hb

theorem maskOf_singleton (i : Fin n) :
    maskOf ({i} : Finset (Fin n)) = 2 ^ (i : ℕ) := by
  rw [show ({i} : Finset (Fin n)) = insert i ∅ from rfl,
    maskOf_insert (Finset.notMem_empty i), maskOf_empty]
  simp

theorem maskOf_pair {i j : Fin n} (hij : i ≠ j) :
    maskOf ({i, j} : Finset (Fin n)) = 2 ^ (i : ℕ) ||| 2 ^ (j : ℕ) := by
  rw [show ({i, j} : Finset (Fin n)) = insert i {j} from rfl,
    maskOf_insert (by simp [hij]), maskOf_singleton]

end Xor3Mask

#print axioms Xor3Mask.maskOf_symmDiff
#print axioms Xor3Mask.maskOf_injective
