/-  SignChain.lean -- A2 Theorem 7: the alternating-sign-chain → hLine lemma.

    Generalizes the per-instance IVT pattern of `XiLineZeros` (lambda_zero_*, lambda_two_zeros_*,
    lambda_five_zeros_*) into ONE lemma parameterized by an arbitrary grid of `n+1` points:

        alternating_signs_chain

    Given `n+1` strictly increasing grid points `p₀ < p₁ < … < pₙ` in `[T0, T1]` at which the
    real critical-line function `gLine` takes strictly sign-alternating values (encoded as the
    single per-interval condition `gLine pᵢ · gLine pᵢ₊₁ < 0`), it produces the VERBATIM T5
    `hLine` shape (see `TuringBand.BandStatement`):

        ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧
          (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
          (∀ t ∈ xs, completedRiemannZeta (1/2 + t·I) = 0)

    Each of the `n` consecutive sign-change subintervals yields, by the intermediate value
    theorem on the continuous `gLine`, one interior zero; strict monotonicity of the grid
    orders the zeros into a `<`-chain.  A reflected sign-sweep (kernel-checked rational bounds
    on `gLine` at the grid points, of alternating sign) discharges `hLine` through this lemma.

    conjecture1_proved = False.
-/
import XiLineZeros
import TuringBand

open Complex ZetaZeroLocalization XiLineZeros

namespace ZetaReflection

/-- **One interior zero per sign-change interval.**  If `gLine a` and `gLine b` have opposite
    signs on `a < b`, the IVT gives a zero of `gLine` (hence of `completedRiemannZeta` on the
    line) STRICTLY inside `(a, b)`. -/
theorem exists_zero_of_sign_change {a b : ℝ} (hab : a < b)
    (hsign : gLine a * gLine b < 0) :
    ∃ r : ℝ, a < r ∧ r < b ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
  have hcont : ContinuousOn gLine (Set.Icc a b) := gLine_continuous.continuousOn
  -- opposite signs: either  gLine a < 0 < gLine b  or  gLine b < 0 < gLine a
  rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
  · -- gLine a > 0, gLine b < 0  → use intermediate_value_Icc'
    have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc' (le_of_lt hab) hcont ⟨le_of_lt hnb, le_of_lt hpa⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpa)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hnb)
    refine ⟨r, hlo, hhi, ?_⟩
    rw [lambda_eq_gLine, hz]; simp
  · -- gLine a < 0, gLine b > 0  → use intermediate_value_Icc
    have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc (le_of_lt hab) hcont ⟨le_of_lt hna, le_of_lt hpb⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hna)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpb)
    refine ⟨r, hlo, hhi, ?_⟩
    rw [lambda_eq_gLine, hz]; simp

/-- **A2 Theorem 7 — the alternating-sign chain.**  From `n+1` strictly increasing grid points
    `p : Fin (n+1) → ℝ` inside `[T0, T1]` with a sign change of `gLine` across each consecutive
    pair, produce the verbatim T5 `hLine` chain of `n` on-line zeros. -/
theorem alternating_signs_chain
    (T0 T1 : ℝ) (n : ℕ) (p : Fin (n + 1) → ℝ)
    (hmono : StrictMono p)
    (hlo : T0 ≤ p 0) (hhi : p (Fin.last n) ≤ T1)
    (hsign : ∀ i : Fin n, gLine (p i.castSucc) * gLine (p i.succ) < 0) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  -- for each interval pick a strictly-interior zero
  have hroot : ∀ i : Fin n, ∃ r : ℝ, p i.castSucc < r ∧ r < p i.succ ∧
      completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
    intro i
    exact exists_zero_of_sign_change (hmono (Fin.castSucc_lt_succ (i := i))) (hsign i)
  choose root hroot_lo hroot_hi hroot_zero using hroot
  refine ⟨List.ofFn root, ?_, ?_, ?_, ?_⟩
  · -- length
    rw [List.length_ofFn]
  · -- strictly increasing chain
    rw [List.isChain_ofFn]
    intro i hi
    -- root ⟨i⟩ < p ⟨i⟩.succ = p ⟨i+1⟩.castSucc < root ⟨i+1⟩
    have h1 : root ⟨i, Nat.lt_of_succ_lt hi⟩ < p (Fin.succ ⟨i, Nat.lt_of_succ_lt hi⟩) :=
      hroot_hi _
    have h2 : p (Fin.castSucc ⟨i + 1, hi⟩) < root ⟨i + 1, hi⟩ := hroot_lo _
    have hcast : (Fin.succ ⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (n + 1))
        = Fin.castSucc ⟨i + 1, hi⟩ := by
      apply Fin.ext; simp
    rw [hcast] at h1
    exact lt_trans h1 h2
  · -- bounds T0 ≤ t ≤ T1
    intro t ht
    rw [List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    constructor
    · -- T0 ≤ p 0 ≤ p i.castSucc < root i
      have hmono0 : p 0 ≤ p i.castSucc := by
        rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
        · have : (i.castSucc : Fin (n+1)) = 0 := by apply Fin.ext; simp [h0]
          rw [this]
        · exact le_of_lt (hmono (by
            rw [Fin.lt_def]; simpa using hpos))
      linarith [hlo, hmono0, hroot_lo i]
    · -- root i < p i.succ ≤ p (last) ≤ T1
      have hmonoL : p i.succ ≤ p (Fin.last n) := by
        rcases eq_or_lt_of_le (Fin.le_last i.succ) with h | h
        · rw [h]
        · exact le_of_lt (hmono h)
      linarith [hhi, hmonoL, hroot_hi i]
  · -- zeros
    intro t ht
    rw [List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    exact hroot_zero i

end ZetaReflection
