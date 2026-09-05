/- telperion 0.1.6 | family TranscendentalEnclosure | input-hash dc9e59259b41d2af
   6 theorems, 2 generation-time self-checks passed.
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

end TranscendentalEnclosure
