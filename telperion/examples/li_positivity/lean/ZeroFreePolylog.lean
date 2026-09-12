/- POLYLOG-IMPROVED UNCONDITIONAL ZERO-FREE REGION -- wiring the sharp near-line bound into the
   elementary cascade.

   The elementary region `riemannZeta_zero_free_poly` (`Re s > 1 - c/|t|⁵`, ZeroFreeElementary.lean)
   spends its `γ⁵` as `γ⁴` (the Cauchy factor `ζ(σ+it)⁴`) × `γ¹` (the 2t factor `ζ(σ+2it)`), both
   from the CRUDE growth bound `|ζ| ≤ C|t|`.

   The 2t factor `ζ((2-β)+2iγ)` sits at `Re = 2-β ∈ [1,2]`, `|2γ| ≥ 4` -- EXACTLY the domain of the
   sharp bound `zeta_log_bound` (`|ζ| ≤ 6(1+log|t|)`, ZetaLogBound.lean).  Swapping it in replaces
   that `γ¹` by `1 + log(2γ)`, upgrading the region to

       Re s > 1 - c/(γ⁴·(1 + log(2γ))),   strictly stronger than `1 - c/γ⁵`.

   HONEST SCOPE OF THE WIRING: only the 2t factor improves cleanly.  The dominant `γ⁴` Cauchy factor
   is NOT reachable this way -- `zeta_hcauchy`/`zeta_sphere_bound` bound `ζ'` on a radius-½ disk about
   `u+iγ` (`u ≥ 3/4`) that dips to `Re z = 1/4 < 1`, where the log bound is FALSE
   (`Σ n^{-σ} ~ N^{1-σ}` is polynomial for `σ < 1`).  Pushing `γ⁴ → (log γ)⁴` needs a one-sided
   (`Re ≥ 1`) log-derivative bound = Borel–Carathéodory (absent from Mathlib v4.32.0) -- the classical
   dVP route.  So this is a partial, honest improvement, NOT the dVP `1 - c/log|t|` region, and NOT a
   proof of RH.  conjecture1_proved = False.
-/
import ZeroFreeElementary
import ZetaLogBound

open Filter Topology

namespace ZeroFreeBridge

/-- POLYLOG ASSEMBLY.  Identical to `zeta_zero_free_poly_of` except the 2t magnitude is bounded by a
    general positive `S` (to be `1 + log(2γ)`) instead of `c₂·γ`: the product inequality then pushes
    the zero left by `1/(16 c₁³ c₂ c₄⁴ γ⁴ S) ≤ 1 - β`. -/
theorem zeta_zero_free_polylog_of {β γ c₁ c₂ c₄ S Zσ Zσt Zσ2t : ℝ}
    (hβ1 : β < 1) (hγ : 1 ≤ γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₄ : 0 < c₄) (hS : 0 < S)
    (hZσ : 0 ≤ Zσ) (hZσt : 0 ≤ Zσt) (hZσ2t : 0 ≤ Zσ2t)
    (hprod : 1 ≤ Zσ ^ 3 * Zσt ^ 4 * Zσ2t)
    (hpole : Zσ ≤ c₁ / (1 - β))
    (hstrip : Zσ2t ≤ c₂ * S)
    (hcauchy : Zσt ≤ 2 * (1 - β) * c₄ * γ) :
    1 / (16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * γ ^ 4 * S) ≤ 1 - β := by
  have hη : 0 < 1 - β := by linarith
  have hγ0 : 0 < γ := by linarith
  have hub : Zσ ^ 3 * Zσt ^ 4 * Zσ2t
      ≤ (c₁ / (1 - β)) ^ 3 * (2 * (1 - β) * c₄ * γ) ^ 4 * (c₂ * S) := by
    gcongr
  have hsimp : (c₁ / (1 - β)) ^ 3 * (2 * (1 - β) * c₄ * γ) ^ 4 * (c₂ * S)
      = 16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * (1 - β) * γ ^ 4 * S := by
    field_simp
    ring
  rw [hsimp] at hub
  have h1 : (1 : ℝ) ≤ 16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * (1 - β) * γ ^ 4 * S := le_trans hprod hub
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1]

/-- The 2t magnitude via the SHARP bound: `‖ζ((2-β)+2iγ)‖ ≤ 6·(1 + log(2γ))` for `0 ≤ β ≤ 1`,
    `2 ≤ γ`.  `Re = 2-β ∈ [1,2]` and `|2γ| ≥ 4 ≥ 2`, so `zeta_log_bound` applies directly. -/
theorem zeta_strip_2t_log_bound {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hγ : 2 ≤ γ) :
    ‖riemannZeta (((2 - β : ℝ) : ℂ) + 2 * γ * Complex.I)‖ ≤ 6 * (1 + Real.log (2 * γ)) := by
  have habs : |2 * γ| = 2 * γ := abs_of_nonneg (by linarith)
  have hpt : ((2 - β : ℝ) : ℂ) + 2 * γ * Complex.I
      = ((2 - β : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hpt]
  have h := zeta_log_bound (σ := 2 - β) (t := 2 * γ)
    (by linarith : (1 : ℝ) ≤ 2 - β) (by linarith : 2 - β ≤ 2)
    (by rw [habs]; linarith : (2 : ℝ) ≤ |2 * γ|)
  rw [habs] at h
  exact h

/-- POLYLOG-IMPROVED UNCONDITIONAL ZERO-FREE REGION.  There is `c > 0` such that every strip zero
    `β+iγ` of `riemannZeta` with `2 ≤ γ` satisfies `β ≤ 1 - c/(γ⁴·(1+log(2γ)))` -- strictly stronger
    than the elementary `1 - c/γ⁵`.  Assembled from the reused elementary bounds
    (`zeta_norm_product_ge_one`, `zeta_pole_bound`, `zeta_hcauchy`) with the 2t factor upgraded via
    `zeta_strip_2t_log_bound` (the sharp `zeta_log_bound`).  Still Hadamard-free and UNCONDITIONAL;
    the residual `γ⁴` factor is Borel–Carathéodory-gated.  conjecture1_proved = False. -/
theorem riemannZeta_zero_free_polylog :
    ∃ c > (0 : ℝ), ∀ β γ : ℝ,
      riemannZeta ((β : ℂ) + γ * Complex.I) = 0 → 2 ≤ γ →
      β ≤ 1 - c / (γ ^ 4 * (1 + Real.log (2 * γ))) := by
  obtain ⟨δ₀, hδ₀, hpoleδ⟩ := zeta_pole_bound
  set δ₁ : ℝ := min δ₀ (1 / 4) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ (by norm_num)
  refine ⟨min (16 * δ₁) (1 / 254803968), by positivity, ?_⟩
  set c := min (16 * δ₁) (1 / 254803968) with hc
  have hc_le1 : c ≤ 16 * δ₁ := min_le_left _ _
  have hc_le2 : c ≤ 1 / 254803968 := min_le_right _ _
  intro β γ hzero hγ
  -- positivity facts for the polylog denominator `g(γ) = γ⁴·(1+log(2γ))`.
  have hγpos : (0 : ℝ) < γ := by linarith
  have hγ4pos : (0 : ℝ) < γ ^ 4 := by positivity
  have hlog2γ : (0 : ℝ) ≤ Real.log (2 * γ) := Real.log_nonneg (by linarith)
  have hSpos : (0 : ℝ) < 1 + Real.log (2 * γ) := by linarith
  have hg_pos : (0 : ℝ) < γ ^ 4 * (1 + Real.log (2 * γ)) := mul_pos hγ4pos hSpos
  have hg16 : (16 : ℝ) ≤ γ ^ 4 * (1 + Real.log (2 * γ)) := by
    have h1 : (16 : ℝ) ≤ γ ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ γ ^ 4 := by gcongr <;> linarith
    have h2 : (1 : ℝ) ≤ 1 + Real.log (2 * γ) := by linarith
    calc (16 : ℝ) = 16 * 1 := by ring
      _ ≤ γ ^ 4 * (1 + Real.log (2 * γ)) :=
          mul_le_mul h1 h2 (by norm_num) (by positivity)
  -- `β < 1`: else `ζ(β+iγ) ≠ 0` (Re ≥ 1).
  have hβ1 : β < 1 := by
    by_contra h; push_neg at h
    have hre : (1 : ℝ) ≤ ((β : ℂ) + γ * Complex.I).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_mul]; linarith
    exact riemannZeta_ne_zero_of_one_le_re hre hzero
  by_cases hcase : β ≤ 1 - δ₁
  · -- far case: `1 - β ≥ δ₁ ≥ c/g(γ)`.
    have hgap : c / (γ ^ 4 * (1 + Real.log (2 * γ))) ≤ δ₁ := by
      rw [div_le_iff₀ hg_pos]
      have h := mul_le_mul_of_nonneg_left hg16 hδ₁0.le
      nlinarith [hc_le1, h]
    linarith
  · -- near case: run the machinery at `σ = 2 - β`, 2t factor via the sharp bound.
    push_neg at hcase
    have hβ34 : (3 : ℝ) / 4 ≤ β := by have : δ₁ ≤ 1 / 4 := min_le_right _ _; linarith
    have hσδ₀ : 2 - β < 1 + δ₀ := by have : δ₁ ≤ δ₀ := min_le_left _ _; linarith
    have hprod := zeta_norm_product_ge_one (show (0 : ℝ) < 1 - β by linarith) γ
    have he0 : (1 : ℂ) + ((1 - β : ℝ) : ℂ) = ((2 - β : ℝ) : ℂ) := by push_cast; ring
    rw [he0] at hprod
    have hpole : ‖riemannZeta ((2 - β : ℝ) : ℂ)‖ ≤ 2 / (1 - β) := by
      have h := hpoleδ (2 - β) (by linarith) hσδ₀
      rw [show (2 - β) - 1 = 1 - β by ring] at h
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - β)]
      nlinarith [h]
    have hstrip : ‖riemannZeta (((2 - β : ℝ) : ℂ) + 2 * Complex.I * γ)‖
        ≤ 6 * (1 + Real.log (2 * γ)) := by
      have h := zeta_strip_2t_log_bound (β := β) (by linarith) (by linarith) hγ
      rw [show ((2 - β : ℝ) : ℂ) + 2 * γ * Complex.I
          = ((2 - β : ℝ) : ℂ) + 2 * Complex.I * γ by ring] at h
      exact h
    have hcauchy : ‖riemannZeta (((2 - β : ℝ) : ℂ) + Complex.I * γ)‖ ≤ 2 * (1 - β) * 24 * γ := by
      have h := zeta_hcauchy hβ34 (by linarith : 2 - β ≤ 2) (by linarith : β ≤ 2 - β) hγ hzero
      rw [show 24 * γ * ((2 - β) - β) = 2 * (1 - β) * 24 * γ by ring,
          show ((2 - β : ℝ) : ℂ) + γ * Complex.I
          = ((2 - β : ℝ) : ℂ) + Complex.I * γ by ring] at h
      exact h
    have hgap := zeta_zero_free_polylog_of hβ1 (by linarith : (1 : ℝ) ≤ γ)
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 6) (by norm_num : (0 : ℝ) < 24)
      hSpos (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hprod hpole hstrip hcauchy
    rw [show (16 : ℝ) * 2 ^ 3 * 6 * 24 ^ 4 * γ ^ 4 * (1 + Real.log (2 * γ))
        = 254803968 * γ ^ 4 * (1 + Real.log (2 * γ)) by ring] at hgap
    have hbig_pos : (0 : ℝ) < 254803968 * γ ^ 4 * (1 + Real.log (2 * γ)) :=
      mul_pos (mul_pos (by norm_num) hγ4pos) hSpos
    have hle : c / (γ ^ 4 * (1 + Real.log (2 * γ))) ≤ 1 - β := by
      rw [div_le_iff₀ hbig_pos] at hgap
      rw [div_le_iff₀ hg_pos]
      nlinarith [hgap, hc_le2, hg_pos]
    linarith

end ZeroFreeBridge
