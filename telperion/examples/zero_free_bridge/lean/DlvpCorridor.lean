/-  CORRIDOR BRICKS (log²T corridor, Summit 1): C2 — the zero-gap pigeonhole — and the ψ-shift
    corollary of the unconditional Binet bound.

    C2 (`exists_gap_point`): among any `≤ N` zero-ordinates in a unit interval there is a height
    at distance `≥ 1/(2(N+1))` from ALL of them — the `N+1` midpoints of the equal subdivision
    are pairwise too far apart for one ordinate to block two, so pigeonhole frees one.  With the
    Jensen count `N = O(log T)` this yields the corridor height whose distance to every zero is
    `≳ 1/log T`; combined with the partial-fraction bound (C1, corpus Blaschke machinery) each
    near-zero term is `O(log T)` and the sum is `O(log² T)` (C3).

    ψ-shift (`norm_digamma_sub_log_add_three_le`): the unconditional Binet bound transported to
    `Re ≥ −1` at any height `|Im| ≥ 1` via the 3-step digamma recursion (pole-free off the real
    axis) — the effective Archimedean input for the corridor's Γ-terms and the Guinand–Weil
    edges.  conjecture1_proved = False. -/
import Mathlib
import DlvpTheta

open Complex

namespace ZeroFreeBridge

/-! ## C2: the zero-gap pigeonhole. -/

/-- **The gap point** (C2): if `Z` holds at most `N` reals, some `t ∈ [T, T+1]` has
    `|t − γ| ≥ 1/(2(N+1))` for every `γ ∈ Z`. -/
theorem exists_gap_point (T : ℝ) (Z : Finset ℝ) (N : ℕ) (hcard : Z.card ≤ N) :
    ∃ t : ℝ, T ≤ t ∧ t ≤ T + 1 ∧ ∀ γ ∈ Z, 1 / (2 * ((N : ℝ) + 1)) ≤ |t - γ| := by
  by_contra hcon
  push_neg at hcon
  set ε : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hεdef
  set mid : ℕ → ℝ := fun i => T + (2 * (i : ℝ) + 1) / (2 * ((N : ℝ) + 1)) with hmiddef
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmlo : ∀ i : ℕ, T ≤ mid i := by
    intro i
    have : (0 : ℝ) ≤ (2 * (i : ℝ) + 1) / (2 * ((N : ℝ) + 1)) := by positivity
    simp only [hmiddef]
    linarith
  have hmhi : ∀ i ∈ Finset.range (N + 1), mid i ≤ T + 1 := by
    intro i hi
    have hiN : (i : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : (2 * (i : ℝ) + 1) / (2 * ((N : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    simp only [hmiddef]
    linarith
  have key : ∀ i ∈ Finset.range (N + 1), ∃ γ ∈ Z, |mid i - γ| < ε := by
    intro i hi
    obtain ⟨γ, hγZ, hγlt⟩ := hcon (mid i) (hmlo i) (hmhi i hi)
    exact ⟨γ, hγZ, hγlt⟩
  choose! f hfZ hflt using key
  have hc : Z.card < (Finset.range (N + 1)).card := by
    rw [Finset.card_range]
    omega
  have hmaps : Set.MapsTo f (Finset.range (N + 1)) Z := by
    intro i hi
    exact hfZ i (by simpa using hi)
  obtain ⟨i, hi, j, hj, hij, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps
  -- distinct midpoints are ≥ 1/(N+1) apart, but both are < ε from the SAME γ.
  have hmdiff : mid i - mid j = ((i : ℝ) - (j : ℝ)) / ((N : ℝ) + 1) := by
    simp only [hmiddef]
    field_simp
    ring
  have habs1 : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have h1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have h1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hgap : 1 / ((N : ℝ) + 1) ≤ |mid i - mid j| := by
    rw [hmdiff, abs_div, abs_of_pos hNpos, div_le_div_iff₀ hNpos hNpos]
    nlinarith [habs1, hNpos]
  have htri : |mid i - mid j| < 2 * ε := by
    have h1 := hflt i hi
    have h2 := hflt j hj
    rw [hfeq] at h1
    calc |mid i - mid j| = |(mid i - f j) + (f j - mid j)| := by ring_nf
      _ ≤ |mid i - f j| + |f j - mid j| := abs_add_le _ _
      _ = |mid i - f j| + |mid j - f j| := by rw [abs_sub_comm (f j)]
      _ < ε + ε := add_lt_add h1 h2
      _ = 2 * ε := by ring
  have hε2 : 2 * ε = 1 / ((N : ℝ) + 1) := by
    rw [hεdef]
    field_simp
  rw [hε2] at htri
  linarith

/-! ## The ψ-shift corollary: effective digamma off the real axis, `Re ≥ −1`. -/

/-- The digamma recursion, pole-avoidance from `Im ≠ 0` (works at ANY real part). -/
theorem digamma_shift_of_im_ne {s : ℂ} (him : s.im ≠ 0) (N : ℕ) :
    Complex.digamma (s + N) = Complex.digamma s + ∑ k ∈ Finset.range N, (s + k)⁻¹ := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hpole : ∀ m : ℕ, s + (n : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      apply him
      have := congrArg Complex.im hm
      simpa using this
    have hcast : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
    rw [hcast, Complex.digamma_apply_add_one _ hpole, ih, Finset.sum_range_succ, add_assoc]

/-- **Effective digamma at any height ≥ 1** (ψ-shift): for `Re s ≥ −1`, `|Im s| ≥ 1`,
    `‖ψ(s) − log(s+3)‖ ≤ 1/(Re s + 2) + 3/|Im s|`.  The Binet bound transported down the
    recursion — the Archimedean input for the corridor Γ-terms and the GW edges. -/
theorem norm_digamma_sub_log_add_three_le {s : ℂ} (hre : -1 ≤ s.re) (him : 1 ≤ |s.im|) :
    ‖Complex.digamma s - Complex.log (s + 3)‖ ≤ 1 / (s.re + 2) + 3 / |s.im| := by
  have him0 : s.im ≠ 0 := by
    intro h; rw [h] at him; simp at him; linarith
  have hshift := digamma_shift_of_im_ne him0 3
  have hre3 : (2 : ℝ) ≤ (s + (3 : ℕ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    push_cast
    linarith
  have hB := norm_digamma_sub_log_le (s := s + (3 : ℕ)) hre3
  have hterm : ∀ k ∈ Finset.range 3, ‖(s + (k : ℂ))⁻¹‖ ≤ 1 / |s.im| := by
    intro k _
    have himk : |(s + (k : ℂ)).im| = |s.im| := by
      simp
    have hnorm : |s.im| ≤ ‖s + (k : ℂ)‖ := by
      rw [← himk]
      exact Complex.abs_im_le_norm _
    rw [norm_inv, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) hnorm
  have hsum : ‖∑ k ∈ Finset.range 3, (s + (k : ℂ))⁻¹‖ ≤ 3 / |s.im| := by
    calc ‖∑ k ∈ Finset.range 3, (s + (k : ℂ))⁻¹‖
        ≤ ∑ k ∈ Finset.range 3, ‖(s + (k : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range 3, 1 / |s.im| := Finset.sum_le_sum hterm
      _ = 3 * (1 / |s.im|) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      _ = 3 / |s.im| := by ring
  have hkey : Complex.digamma s - Complex.log (s + 3)
      = (Complex.digamma (s + (3:ℕ)) - Complex.log (s + (3:ℕ)))
        - ∑ k ∈ Finset.range 3, (s + (k : ℂ))⁻¹ := by
    have hc : ((3:ℕ) : ℂ) = (3 : ℂ) := by norm_num
    rw [hc] at hshift ⊢
    linear_combination -hshift
  rw [hkey]
  have hden : (s + (3:ℕ)).re - 1 = s.re + 2 := by
    simp only [Complex.add_re, Complex.natCast_re]
    push_cast
    ring
  calc ‖(Complex.digamma (s + (3:ℕ)) - Complex.log (s + (3:ℕ)))
        - ∑ k ∈ Finset.range 3, (s + (k : ℂ))⁻¹‖
      ≤ ‖Complex.digamma (s + (3:ℕ)) - Complex.log (s + (3:ℕ))‖
        + ‖∑ k ∈ Finset.range 3, (s + (k : ℂ))⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 / ((s + (3:ℕ)).re - 1) + 3 / |s.im| := add_le_add hB hsum
    _ = 1 / (s.re + 2) + 3 / |s.im| := by rw [hden]

end ZeroFreeBridge
