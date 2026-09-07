/- PHASE 4 (dVP frontier, the NUMERIC CLOSING): discharge the two remaining hypothesis families of
   `dlvp_zeta_region_concrete_wired` — the numeric coupling (`hnum`) and the pole bound (`hpole`) —
   by CHOOSING `A, L` and requiring `|γ|` large.  This closes the dVP zero-free region for a concrete
   ζ-zero end-to-end.

   The σ↔L circularity is broken by keeping the count `C` and the entire-part CAPS σ-independent:
     * `C₁, C₂` are the actual divisor finsums over the two disks — fixed, σ-independent, so the
       wiring lemma's `hC` are `le_refl` (`.ge`); no Jensen bound needed for the ∃-form.
     * `Bg₁cap = 4·log(...)·(R+1)/(R-1)²` bounds the σ-dependent `Bg₁` from `hg_bound_gamma`
       (`‖z₀‖ = 2-σ ∈ (0,1)` ⟹ `(R+‖z₀‖)/(R-‖z₀‖)² ≤ (R+1)/(R-1)²`), σ-independent.
     * `L := 1 + 1/(Aε) + (|C₁|/(R-1)+Bg₁cap)/A + (|C₂|/(R-1)+Bg₂cap)/A` — σ-independent.
     * `σ := 1 + 1/(2(3A+5AL))` is then an OUTPUT; `den = R-(2-σ) > R-1 > 0` gives both `hnum`.
   `A := max A₀ 1` (`A₀` the pole constant from `hpole_bounded`); the `1/(Aε)` term forces `σ-1 < ε`
   (`ε` the pole neighborhood radius), so `hpole_pf` holds at the real `σ`.  `R := 7/4 - β/2 ∈ (5/4,3/2)`.

   conjecture1_proved = False (NOT a proof of RH — this is a REDUCTION; the constant is non-effective).
-/
import DlvpZetaConcreteWired
import DlvpZetaHgBoundGamma
import DlvpZetaHpole

open Complex MeromorphicOn Metric Filter Topology

namespace ZeroFreeBridge

set_option maxHeartbeats 1200000 in
/-- **The de la Vallée Poussin region for a concrete ζ-zero.**  For a zero `ρ₀ = β+iγ` with
    `1/2 < β < 1` and `|γ| ≥ 7/2` (multiplicity `k` in the disk of radius `7/4 - β/2`), there are
    explicit `A, L` (constructed from the pole constant and the entire-part/count bounds) with
    `β ≤ 1 - 1/(112·A·L)`.  Closes the numeric coupling (`hnum`) and the pole bound (`hpole`) on top
    of `dlvp_zeta_region_concrete_wired`.  conjecture1_proved = False (NOT a proof of RH). -/
theorem dlvp_zeta_region_concrete (β γ : ℝ) (k : ℤ)
    (hβ2 : 1/2 < β) (hβ1 : β < 1) (hγ : 7/2 ≤ |γ|) (hk : 1 ≤ k)
    (hmρ₀ : divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) (7/4 - β/2)) ((β : ℂ) + (γ : ℂ) * I)
              = k) :
    ∃ A L : ℝ, 0 < A ∧ 1 ≤ L ∧ β ≤ 1 - 1 / (112 * (A * L)) := by
  -- ===== pole: extract the constant A₀ and a neighborhood radius ε =====
  obtain ⟨A₀, hev⟩ := hpole_bounded
  obtain ⟨t, ht_mem, ht⟩ := eventually_iff_exists_mem.mp hev
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp ht_mem
  -- ===== A =====
  set A : ℝ := max A₀ 1 with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact le_max_right A₀ 1
  have hA0le : A₀ ≤ A := by rw [hAdef]; exact le_max_left A₀ 1
  clear_value A
  have hA : 0 < A := by linarith
  -- ===== R (fixed radius) =====
  set R : ℝ := 7/4 - β/2 with hRdef
  have hR32 : R < 3/2 := by rw [hRdef]; linarith
  have hR1 : 1 < R := by rw [hRdef]; linarith
  clear_value R
  have hR : 0 < R := by linarith
  have hβR : 2 - β < R := by rw [hRdef]; linarith
  have himc0 : R + 2 ≤ |γ| := by linarith
  have h2γ : |γ| ≤ |2 * γ| := by
    rw [abs_mul]; have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]; linarith [abs_nonneg γ]
  have hγ2 : R + 2 ≤ |2 * γ| := le_trans himc0 h2γ
  -- ===== C₁, C₂ (the actual σ-independent divisor counts) =====
  set C₁ : ℝ := ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) ρ : ℤ) : ℝ)
    with hC₁def
  set C₂ : ℝ :=
    ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ : ℤ) : ℝ)
    with hC₂def
  clear_value C₁ C₂
  -- ===== log oscillation nonneg =====
  have hpipos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hAz1 : (0 : ℝ) ≤ Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
    apply Real.log_nonneg
    rw [one_le_div hpipos]
    have : (0 : ℝ) ≤ Real.pi ^ 2 / 6 := by positivity
    linarith [abs_nonneg γ]
  have hAz2 : (0 : ℝ) ≤ Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
    apply Real.log_nonneg
    rw [one_le_div hpipos]
    have : (0 : ℝ) ≤ Real.pi ^ 2 / 6 := by positivity
    linarith [abs_nonneg (2 * γ)]
  -- ===== Bg caps (σ-independent) =====
  set Bg₁cap : ℝ := 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) * (R + 1) / (R - 1) ^ 2
    with hBg₁capdef
  set Bg₂cap : ℝ :=
    4 * Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) * (R + 1) / (R - 1) ^ 2
    with hBg₂capdef
  clear_value Bg₁cap Bg₂cap
  have hR1' : (0 : ℝ) < R - 1 := by linarith
  have hBg1cap_nn : 0 ≤ Bg₁cap := by
    rw [hBg₁capdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hAz1) (by linarith)) (sq_nonneg _)
  have hBg2cap_nn : 0 ≤ Bg₂cap := by
    rw [hBg₂capdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hAz2) (by linarith)) (sq_nonneg _)
  -- ===== L (σ-independent) =====
  set L : ℝ := 1 + 1 / (A * ε) + (|C₁| / (R - 1) + Bg₁cap) / A + (|C₂| / (R - 1) + Bg₂cap) / A
    with hLdef
  clear_value L
  have ht1 : (0 : ℝ) ≤ 1 / (A * ε) := le_of_lt (div_pos one_pos (mul_pos hA hε))
  have ht2 : (0 : ℝ) ≤ (|C₁| / (R - 1) + Bg₁cap) / A :=
    div_nonneg (add_nonneg (div_nonneg (abs_nonneg _) (le_of_lt hR1')) hBg1cap_nn) (le_of_lt hA)
  have ht3 : (0 : ℝ) ≤ (|C₂| / (R - 1) + Bg₂cap) / A :=
    div_nonneg (add_nonneg (div_nonneg (abs_nonneg _) (le_of_lt hR1')) hBg2cap_nn) (le_of_lt hA)
  have hL : 1 ≤ L := by rw [hLdef]; linarith
  have hLpole : 1 / (A * ε) ≤ L := by rw [hLdef]; linarith
  have hLnum1 : (|C₁| / (R - 1) + Bg₁cap) / A ≤ L := by rw [hLdef]; linarith
  have hLnum2 : (|C₂| / (R - 1) + Bg₂cap) / A ≤ L := by rw [hLdef]; linarith
  -- ===== σ (determined by A, L) =====
  have hAL1 : (1 : ℝ) ≤ A * L := by nlinarith [hA1, hL]
  have hden : (0 : ℝ) < 2 * (3 * A + 5 * (A * L)) := by nlinarith [hA1, hL, hAL1]
  set σ : ℝ := 1 + 1 / (2 * (3 * A + 5 * (A * L))) with hσdef
  clear_value σ
  have hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L))) := by rw [hσdef]; ring
  have hσ1 : 1 < σ := by rw [hσdef]; have := div_pos one_pos hden; linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have h16 : (1 : ℝ) ≤ 2 * (3 * A + 5 * (A * L)) := by nlinarith [hA1, hL, hAL1]
    have : 1 / (2 * (3 * A + 5 * (A * L))) ≤ 1 := by rw [div_le_one hden]; linarith
    linarith
  -- σ - 1 < ε
  have hALlb : 1 / ε ≤ A * L := by
    have h := mul_le_mul_of_nonneg_left hLpole hA.le
    rwa [show A * (1 / (A * ε)) = 1 / ε by field_simp] at h
  have hALε : (1 : ℝ) ≤ A * L * ε := by
    have h := mul_le_mul_of_nonneg_right hALlb hε.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hε)] at h
  have hσdelt : σ - 1 < ε := by
    rw [hσ_opt, div_lt_iff₀ hden]; nlinarith [hALε, mul_pos hA hε]
  -- ===== eval-point norms =====
  have hzn : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ = 2 - σ := by
    have he : (σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]; ring
  have hzn0 : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖ = 2 - σ := by
    rw [sub_zero]; exact hzn
  have hzn1 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖ = 2 - σ := by
    have he : (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
        = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]; ring
  have hzn10 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖
      = 2 - σ := by rw [sub_zero]; exact hzn1
  have hz₀mem : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ < R := by rw [hzn]; linarith
  have hz₀mem2 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖ < R := by
    rw [hzn1]; linarith
  -- ===== Bg (σ-dependent), from hg_bound_gamma =====
  set Bg₁ : ℝ := 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6))
      * (R + ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖)
      / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖) ^ 2 with hBg₁def
  set Bg₂ : ℝ := 4 * Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6))
      * (R + ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖)
      / (R - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖) ^ 2
    with hBg₂def
  clear_value Bg₁ Bg₂
  have hd1 : (0 : ℝ) < R - (2 - σ) := by linarith
  -- Bg₁ ≤ Bg₁cap
  have hBg1_le : Bg₁ ≤ Bg₁cap := by
    rw [hBg₁def, hBg₁capdef, hzn0, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hAz1)
    gcongr
    · linarith
    · linarith
  have hBg2_le : Bg₂ ≤ Bg₂cap := by
    rw [hBg₂def, hBg₂capdef, hzn10, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hAz2)
    gcongr
    · linarith
    · linarith
  -- ===== the 4 wiring-lemma hypothesis families =====
  have hgb₁ : ∀ g : ℂ → ℂ,
      CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R →
      ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg₁ := by
    intro g D; rw [hBg₁def]; exact hg_bound_gamma hR hR32 himc0 D hz₀mem
  have hgb₂ : ∀ g : ℂ → ℂ,
      CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) g R →
      ‖logDeriv g ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))‖ ≤ Bg₂ := by
    intro g D; rw [hBg₂def]; exact hg_bound_gamma hR hR32 hγ2 D hz₀mem2
  have hC₁ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) ρ : ℤ) : ℝ) ≤ C₁ :=
    hC₁def.ge
  have hC₂ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ : ℤ) : ℝ)
      ≤ C₂ := hC₂def.ge
  -- hnum₁
  have hRHS1 : |C₁| / (R - 1) + Bg₁cap ≤ A * L := by
    rw [mul_comm]; exact (div_le_iff₀ hA).mp hLnum1
  have hRHS2 : |C₂| / (R - 1) + Bg₂cap ≤ A * L := by
    rw [mul_comm]; exact (div_le_iff₀ hA).mp hLnum2
  have hC1step : C₁ / (R - (2 - σ)) ≤ |C₁| / (R - 1) :=
    calc C₁ / (R - (2 - σ)) ≤ |C₁| / (R - (2 - σ)) := by gcongr; exact le_abs_self C₁
      _ ≤ |C₁| / (R - 1) := by gcongr; linarith
  have hC2step : C₂ / (R - (2 - σ)) ≤ |C₂| / (R - 1) :=
    calc C₂ / (R - (2 - σ)) ≤ |C₂| / (R - (2 - σ)) := by gcongr; exact le_abs_self C₂
      _ ≤ |C₂| / (R - 1) := by gcongr; linarith
  have hnum₁ : C₁ / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg₁ ≤ A * L := by
    rw [hzn]; exact le_trans (add_le_add hC1step hBg1_le) hRHS1
  have hnum₂ : C₂ / (R - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖) + Bg₂
      ≤ A * L := by rw [hzn1]; exact le_trans (add_le_add hC2step hBg2_le) hRHS2
  -- hpole_pf
  have hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      ≤ (1 / ((σ : ℂ) - 1)).re + A := by
    have hmemball : (σ : ℂ) ∈ Metric.ball (1 : ℂ) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have he : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - 1)]
      exact hσdelt
    have hmemcompl : (σ : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hPσ := ht (σ : ℂ) (hsub ⟨hmemball, hmemcompl⟩)
    exact hPσ.trans (by linarith [hA0le])
  -- ===== assemble =====
  refine ⟨A, L, hA, hL, ?_⟩
  exact dlvp_zeta_region_concrete_wired σ A L β γ k R Bg₁ C₁ Bg₂ C₂ hA hL hk hσ_opt hβ1 hσ2 hR hβR
    himc0 hmρ₀ hpole_pf hgb₁ hC₁ hnum₁ hgb₂ hC₂ hnum₂

end ZeroFreeBridge

