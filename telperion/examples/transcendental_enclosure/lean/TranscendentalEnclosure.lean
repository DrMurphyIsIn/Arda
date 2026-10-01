/- telperion 0.1.6 | family TranscendentalEnclosure | input-hash f321128a01ba2f03
   17 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace TranscendentalEnclosure

-- Provenance: kin to the Montgomery-Taylor transcendental-constant
-- enclosure of AxiomMath/ZetaZeros (arXiv:2609.02882); this ships the
-- rational log face only (the trig/C0 face is deferred). Independently
-- re-implemented; see NOTICE.md for full attribution.

-- ===== log face: rational enclosure of Real.log (1 + x) on [1/4, 1/2] =====
-- Serves BG compact-core cells (e_v = log(1 + S/d) − F*): enclosing
-- log(1+x) between rationals turns a per-cell inequality into a pure
-- rational nlinarith goal.

-- (1) tangent UPPER bound, all x ≥ 0: log(1+x) ≤ x (Real.log_le_sub_one_of_pos at y = 1+x).
theorem log1p_encl_qtr_half_upper (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have hy : (0 : ℝ) < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos hy
  linarith

-- (2) rational LOWER bound on the box [1/4, 1/2]: 1/5 ≤ log(1+x).
-- log monotone ⇒ log(1+x) ≥ log(1+1/4); and 1/5 ≤ log(1+1/4) via
-- Real.le_log_iff_exp_le reduced to the certified exp(1/5) ≤ 1+1/4.
theorem log1p_encl_qtr_half_lower_box (x : ℝ) (hx : x ∈ Set.Icc (1/4 : ℝ) (1/2 : ℝ)) :
    (1/5 : ℝ) ≤ Real.log (1 + x) := by
  obtain ⟨hlo, _hhi⟩ := hx
  have hx0pos : (0 : ℝ) < 1 + (1/4 : ℝ) := by norm_num
  have hxpos : (0 : ℝ) < 1 + x := by linarith
  -- rational floor: 1/5 ≤ log(1 + 1/4).
  have hfloor : (1/5 : ℝ) ≤ Real.log (1 + (1/4 : ℝ)) := by
    rw [Real.le_log_iff_exp_le hx0pos]
    -- exp(1/5) ≤ 1 + 1/4 via the degree-3 Taylor upper bound on exp.
    have hexp := Real.exp_bound' (x := (1/5 : ℝ)) (by norm_num) (by norm_num)
      (n := 3) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 3, (1/5 : ℝ) ^ m / m.factorial)
        + (1/5 : ℝ) ^ 3 * (3 + 1) / ((3 : ℕ).factorial * 3) ≤ 1 + (1/4 : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  -- monotone step: log(1+1/4) ≤ log(1+x).
  have hmono : Real.log (1 + (1/4 : ℝ)) ≤ Real.log (1 + x) :=
    Real.log_le_log hx0pos (by linarith)
  linarith

-- (3) packaged rational enclosure 1/5 ≤ log(1+x) ≤ 1/2 on [1/4, 1/2].
theorem log1p_encl_qtr_half_enclosure (x : ℝ) (hx : x ∈ Set.Icc (1/4 : ℝ) (1/2 : ℝ)) :
    (1/5 : ℝ) ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ (1/2 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hx
  refine ⟨log1p_encl_qtr_half_lower_box x ⟨hlo, hhi⟩, ?_⟩
  have hup := log1p_encl_qtr_half_upper x (by linarith)
  linarith

-- ===== log face: rational enclosure of Real.log (1 + x) on [0, 1/2] =====
-- Serves BG compact-core cells (e_v = log(1 + S/d) − F*): enclosing
-- log(1+x) between rationals turns a per-cell inequality into a pure
-- rational nlinarith goal.

-- (1) tangent UPPER bound, all x ≥ 0: log(1+x) ≤ x (Real.log_le_sub_one_of_pos at y = 1+x).
theorem log1p_encl_zero_half_upper (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have hy : (0 : ℝ) < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos hy
  linarith

-- (2) rational LOWER bound on the box [0, 1/2]: 0 ≤ log(1+x).
-- log monotone ⇒ log(1+x) ≥ log(1+0); and 0 ≤ log(1+0) via
-- Real.le_log_iff_exp_le reduced to the certified exp(0) ≤ 1+0.
theorem log1p_encl_zero_half_lower_box (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1/2 : ℝ)) :
    (0 : ℝ) ≤ Real.log (1 + x) := by
  obtain ⟨hlo, _hhi⟩ := hx
  have hx0pos : (0 : ℝ) < 1 + (0 : ℝ) := by norm_num
  have hxpos : (0 : ℝ) < 1 + x := by linarith
  -- rational floor: 0 ≤ log(1 + 0).
  have hfloor : (0 : ℝ) ≤ Real.log (1 + (0 : ℝ)) := by
    rw [Real.le_log_iff_exp_le hx0pos]
    -- exp(0) ≤ 1 + 0 via the degree-3 Taylor upper bound on exp.
    have hexp := Real.exp_bound' (x := (0 : ℝ)) (by norm_num) (by norm_num)
      (n := 3) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 3, (0 : ℝ) ^ m / m.factorial)
        + (0 : ℝ) ^ 3 * (3 + 1) / ((3 : ℕ).factorial * 3) ≤ 1 + (0 : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  -- monotone step: log(1+0) ≤ log(1+x).
  have hmono : Real.log (1 + (0 : ℝ)) ≤ Real.log (1 + x) :=
    Real.log_le_log hx0pos (by linarith)
  linarith

-- (3) packaged rational enclosure 0 ≤ log(1+x) ≤ 1/2 on [0, 1/2].
theorem log1p_encl_zero_half_enclosure (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1/2 : ℝ)) :
    (0 : ℝ) ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ (1/2 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hx
  refine ⟨log1p_encl_zero_half_lower_box x ⟨hlo, hhi⟩, ?_⟩
  have hup := log1p_encl_zero_half_upper x (by linarith)
  linarith

/-! ## `log (1 + u)` Taylor bounds for all `u >= 0`, with signed remainder

`T n u = sum_{j < n} (-1)^j u^(j+1) / (j+1)`.  For every `u >= 0`: `log (1 + u) <= T n u`
when `n` is odd, `T n u <= log (1 + u)` when `n` is even.  Generic proof: `T n - log (1 + .)`
vanishes at `0` and has derivative `-(-t)^n / (1 + t)` (geometric sum), then the mean value
theorem.  Emitted by `transcendental_enclosure` (face `log_taylor`). -/

namespace log1p_taylor_logTaylor

noncomputable def T (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * u ^ (j + 1) / ((j : ℝ) + 1)

theorem hasDerivAt_T (n : ℕ) (t : ℝ) :
    HasDerivAt (T n) (∑ j ∈ Finset.range n, (-t) ^ j) t := by
  have h : ∀ j ∈ Finset.range n, HasDerivAt
      (fun u : ℝ => (-1 : ℝ) ^ j * u ^ (j + 1) / ((j : ℝ) + 1)) ((-t) ^ j) t := by
    intro j _
    have h1 := ((hasDerivAt_pow (j + 1) t).const_mul ((-1 : ℝ) ^ j)).div_const ((j : ℝ) + 1)
    refine h1.congr_deriv ?_
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, neg_pow t j]
    push_cast
    field_simp
  exact HasDerivAt.fun_sum h

theorem nonneg_of_deriv_nonneg {g g' : ℝ → ℝ} (h0 : g 0 = 0)
    (hd : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t) (hp : ∀ t, 0 ≤ t → 0 ≤ g' t) :
    ∀ u, 0 ≤ u → 0 ≤ g u := by
  intro u hu
  rcases hu.eq_or_lt with h | h
  · rw [← h, h0]
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' h
      (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
      (fun x hx => hd x hx.1.le)
    have := hp c hc.1.le
    rw [hcs, h0, sub_zero, sub_zero] at this
    exact (div_nonneg_iff.mp this).elim (fun h' => h'.1) (fun h' => by linarith [h'.2])

/-- The remainder's derivative: `(T n)' - 1/(1+t) = -(-t)^n / (1 + t)`. -/
theorem deriv_gap (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range n, (-t) ^ j) - 1 / (1 + t) = -(-t) ^ n / (1 + t) := by
  have h1 : (1 + t) ≠ 0 := by positivity
  have hg := geom_sum_mul_neg (-t) n
  rw [sub_neg_eq_add, add_comm] at hg
  field_simp
  linarith [hg]

theorem hasDerivAt_log1 (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 t := (hasDerivAt_id t).const_add 1
  have := h1.log (by positivity)
  simpa using this

/-- Odd order: the Taylor polynomial is an UPPER bound for every `u >= 0`. -/
theorem log_le_T (n : ℕ) (hn : Odd n) (u : ℝ) (hu : 0 ≤ u) : Real.log (1 + u) ≤ T n u := by
  have key := nonneg_of_deriv_nonneg (g := fun v => T n v - Real.log (1 + v))
    (g' := fun t => (∑ j ∈ Finset.range n, (-t) ^ j) - 1 / (1 + t))
    (by simp [T])
    (fun t ht => (hasDerivAt_T n t).sub (hasDerivAt_log1 t ht))
    (fun t ht => by
      rw [deriv_gap n t ht, hn.neg_pow]
      have : 0 ≤ t ^ n := pow_nonneg ht n
      have : 0 < 1 + t := by linarith
      rw [neg_neg]; positivity)
    u hu
  have key' : 0 ≤ T n u - Real.log (1 + u) := key
  linarith

/-- Even order: the Taylor polynomial is a LOWER bound for every `u >= 0`. -/
theorem T_le_log (n : ℕ) (hn : Even n) (u : ℝ) (hu : 0 ≤ u) : T n u ≤ Real.log (1 + u) := by
  have key := nonneg_of_deriv_nonneg (g := fun v => Real.log (1 + v) - T n v)
    (g' := fun t => 1 / (1 + t) - (∑ j ∈ Finset.range n, (-t) ^ j))
    (by simp [T])
    (fun t ht => (hasDerivAt_log1 t ht).sub (hasDerivAt_T n t))
    (fun t ht => by
      have e : 1 / (1 + t) - (∑ j ∈ Finset.range n, (-t) ^ j) = (-t) ^ n / (1 + t) := by
        have := deriv_gap n t ht; rw [neg_div] at this; linarith
      rw [e, hn.neg_pow]
      have : 0 ≤ t ^ n := pow_nonneg ht n
      positivity)
    u hu
  have key' : 0 ≤ Real.log (1 + u) - T n u := key
  linarith

theorem upper_1 (u : ℝ) (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u := by
  have h := log_le_T 1 (by decide) u hu
  simp only [T, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

theorem lower_2 (u : ℝ) (hu : 0 ≤ u) :
    u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  have h := T_le_log 2 (by decide) u hu
  simp only [T, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

theorem upper_3 (u : ℝ) (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  have h := log_le_T 3 (by decide) u hu
  simp only [T, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

theorem lower_4 (u : ℝ) (hu : 0 ≤ u) :
    u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 ≤ Real.log (1 + u) := by
  have h := T_le_log 4 (by decide) u hu
  simp only [T, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

theorem upper_5 (u : ℝ) (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 := by
  have h := log_le_T 5 (by decide) u hu
  simp only [T, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

end log1p_taylor_logTaylor

end TranscendentalEnclosure
