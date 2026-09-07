/- PHASE 4 (dVP frontier, the RATE-EXPOSED region): lift the ∃-form `dlvp_zeta_region_concrete` to a
   theorem carrying the classical de la Vallée Poussin RATE `β ≤ 1 - c/log|γ|` in its TYPE.

   FIXED radii `R = 11/8`, `R' = 23/16` (valid for `β ≥ 3/4`; near `β = 1/2` the zero-enclosing
   window `(2-β, 3/2)` collapses, so `β` is kept off the critical line — zeros with `β < 3/4` satisfy
   any `1 - c/log|γ|` bound trivially for large `|γ|`). Fixed radii ⟹ ABSOLUTE geometric constants ⟹
   count `= O(log|γ|)` (`zeta_zero_count_strip` + `U_le_of_c0_2_gamma` + `zeta_norm_ge_two_sub`),
   entire-part cap `= O(log|γ|)`, hence `L ≤ K·log|γ|` (UNIFORM `K`) and
   `β ≤ 1 - 1/(112·A·L) ≤ 1 - c/log|γ|`, `c := 1/(112·A·K)`.

   `c` is `∃`-quantified (`A` from Mathlib's pole constant), so NON-EFFECTIVE — as classical dVP is.
   conjecture1_proved = False (NOT a proof of RH; a kernel-verified reduction for a concrete zero).
-/
import DlvpZetaConcreteWired
import DlvpZetaHgBoundGamma
import DlvpZetaHpole
import DlvpZetaCountStrip
import DlvpZetaAzeta

open Complex MeromorphicOn Metric Filter Topology

namespace ZeroFreeBridge

set_option maxHeartbeats 3200000 in
/-- **The de la Vallée Poussin region at the classical rate.**  There is `c > 0` such that every
    ζ-zero `ρ₀ = β+iγ` with `3/4 ≤ β < 1`, `|γ| ≥ 55/16`, multiplicity `k` in the fixed disk of
    radius `11/8`, satisfies `β ≤ 1 - c/log|γ|`.  Rate exposed in the type; `c` non-effective. -/
theorem dlvp_zeta_region_rate :
    ∃ c : ℝ, 0 < c ∧ ∀ (β γ : ℝ) (k : ℤ),
      3/4 ≤ β → β < 1 → 55/16 ≤ |γ| → 1 ≤ k →
      divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ((β : ℂ) + (γ : ℂ) * I) = k →
      β ≤ 1 - c / Real.log |γ| := by
  obtain ⟨A₀, hev⟩ := hpole_bounded
  obtain ⟨t, ht_mem, ht⟩ := eventually_iff_exists_mem.mp hev
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp ht_mem
  set A : ℝ := max A₀ 1 with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact le_max_right A₀ 1
  have hA0le : A₀ ≤ A := by rw [hAdef]; exact le_max_left A₀ 1
  clear_value A
  have hA : 0 < A := by linarith
  have hAne : A ≠ 0 := ne_of_gt hA
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  set Lr : ℝ := Real.log ((23/16) / (11/8)) with hLrdef
  have hLrpos : 0 < Lr := by rw [hLrdef]; exact Real.log_pos (by norm_num)
  have hLrne : Lr ≠ 0 := ne_of_gt hLrpos
  clear_value Lr
  set M : ℝ := (8 / (3 * Lr) + 608/9) / A with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  clear_value M
  have hlog15 : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hpi]; nlinarith [hpi])
  set K : ℝ := 1 + 1 / (A * ε) + 2 * M * (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine ⟨1 / (112 * A * K), by positivity, ?_⟩
  clear_value K
  intro β γ k h34 hβ1 hΓ hk hmρ₀
  have hγ1 : (1 : ℝ) ≤ |γ| := by linarith
  have hlogγpos : 0 < Real.log |γ| := Real.log_pos (by linarith)
  have hlogγ1 : 1 ≤ Real.log |γ| := by
    have hle : Real.exp 1 ≤ |γ| := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log |γ| := Real.log_le_log (by positivity) hle
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : ((2 : ℂ) + (γ : ℂ) * I).im = γ := by simp
  have hc1re : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re = 2 := by simp
  have hc1im : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).im = 2 * γ := by simp
  have h2γ : |γ| ≤ |2 * γ| := by
    rw [abs_mul]; have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]; linarith [abs_nonneg γ]
  have h1c0 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + (γ : ℂ) * I) (11/8) :=
    one_notMem_closedBall_of_himc (by rw [hc0im]; linarith)
  have h1c1 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) (11/8) :=
    one_notMem_closedBall_of_himc (by rw [hc1im]; nlinarith [h2γ, hΓ])
  have hc0lt : (1 : ℝ) < ((2 : ℂ) + (γ : ℂ) * I).re := by rw [hc0re]; norm_num
  have hc1lt : (1 : ℝ) < ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re := by rw [hc1re]; norm_num
  -- === the two O(log|γ|) count bounds ===
  set C₁ : ℝ := Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) / Lr with hC₁def
  set C₂ : ℝ := Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) / Lr with hC₂def
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁def]; apply div_nonneg _ (le_of_lt hLrpos)
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg γ, hpi]
  have hC₂nn : 0 ≤ C₂ := by
    rw [hC₂def]; apply div_nonneg _ (le_of_lt hLrpos)
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg (2 * γ), hpi]
  have hC₁ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ρ : ℤ) : ℝ)
      ≤ C₁ := by
    have hcnt := zeta_zero_count_strip ((2 : ℂ) + (γ : ℂ) * I) (11/8) (23/16)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8)]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16)]; norm_num)
      hc0lt
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc0re]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc0im]; linarith)
    rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16),
      ← hLrdef] at hcnt
    refine le_trans hcnt ?_
    rw [hC₁def]
    have hUle := U_le_of_c0_2_gamma γ (23/16) (by norm_num) (by norm_num) (by linarith)
    have hζ0 := zeta_norm_ge_two_sub (s := (2 : ℂ) + (γ : ℂ) * I) (by rw [hc0re])
    set U : ℝ := (‖(2:ℂ)+(γ:ℂ)*I‖ + 23/16) / (|((2:ℂ)+(γ:ℂ)*I).im| - 23/16)
        + (‖(2:ℂ)+(γ:ℂ)*I‖ + 23/16) / (((2:ℂ)+(γ:ℂ)*I).re - 23/16) with hUdef
    have hfrac : U / ‖riemannZeta ((2:ℂ)+(γ:ℂ)*I)‖ ≤ (2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6) := by
      gcongr
    have hlogle : Real.log (U / ‖riemannZeta ((2:ℂ)+(γ:ℂ)*I)‖)
        ≤ Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
      apply Real.log_le_log _ hfrac
      have h1 : (0:ℝ) < |((2:ℂ)+(γ:ℂ)*I).im| - 23/16 := by rw [hc0im]; linarith [abs_nonneg γ]
      have h2 : (0:ℝ) < ((2:ℂ)+(γ:ℂ)*I).re - 23/16 := by rw [hc0re]; norm_num
      have hznz : (0:ℝ) < ‖riemannZeta ((2:ℂ)+(γ:ℂ)*I)‖ := by linarith [hζ0, hpi]
      rw [hUdef]; positivity
    gcongr
  have hC₂ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) (11/8)) ρ : ℤ) : ℝ)
      ≤ C₂ := by
    have hcnt := zeta_zero_count_strip ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) (11/8) (23/16)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8)]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16)]; norm_num)
      hc1lt
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc1re]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc1im]; nlinarith [h2γ, hΓ])
    rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16),
      ← hLrdef] at hcnt
    refine le_trans hcnt ?_
    rw [hC₂def]
    have hUle := U_le_of_c0_2_gamma (2 * γ) (23/16) (by norm_num) (by norm_num) (by nlinarith [h2γ, hΓ])
    have hζ1 := zeta_norm_ge_two_sub (s := (2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) (by rw [hc1re])
    set U : ℝ := (‖(2:ℂ)+((2*γ:ℝ):ℂ)*I‖ + 23/16) / (|((2:ℂ)+((2*γ:ℝ):ℂ)*I).im| - 23/16)
        + (‖(2:ℂ)+((2*γ:ℝ):ℂ)*I‖ + 23/16) / (((2:ℂ)+((2*γ:ℝ):ℂ)*I).re - 23/16) with hUdef
    have hfrac : U / ‖riemannZeta ((2:ℂ)+((2*γ:ℝ):ℂ)*I)‖
        ≤ (2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6) := by gcongr
    have hlogle : Real.log (U / ‖riemannZeta ((2:ℂ)+((2*γ:ℝ):ℂ)*I)‖)
        ≤ Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
      apply Real.log_le_log _ hfrac
      have h1 : (0:ℝ) < |((2:ℂ)+((2*γ:ℝ):ℂ)*I).im| - 23/16 := by
        rw [hc1im]; nlinarith [h2γ, hΓ, abs_nonneg (2*γ)]
      have h2 : (0:ℝ) < ((2:ℂ)+((2*γ:ℝ):ℂ)*I).re - 23/16 := by rw [hc1re]; norm_num
      have hznz : (0:ℝ) < ‖riemannZeta ((2:ℂ)+((2*γ:ℝ):ℂ)*I)‖ := by linarith [hζ1, hpi]
      rw [hUdef]; positivity
    gcongr
  clear_value C₁ C₂
  -- === Bg caps, L, σ ===
  have hAz1 : (0:ℝ) ≤ Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg γ, hpi]
  have hAz2 : (0:ℝ) ≤ Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg (2 * γ), hpi]
  set Bg₁cap : ℝ := 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) * (11/8 + 1) / (11/8 - 1) ^ 2
    with hBg₁capdef
  set Bg₂cap : ℝ :=
    4 * Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) * (11/8 + 1) / (11/8 - 1) ^ 2
    with hBg₂capdef
  have hBg1cap_nn : 0 ≤ Bg₁cap := by
    rw [hBg₁capdef]; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hAz1) (by norm_num)) (by positivity)
  have hBg2cap_nn : 0 ≤ Bg₂cap := by
    rw [hBg₂capdef]; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hAz2) (by norm_num)) (by positivity)
  clear_value Bg₁cap Bg₂cap
  set L : ℝ := 1 + 1 / (A * ε) + (C₁ / (11/8 - 1) + Bg₁cap) / A + (C₂ / (11/8 - 1) + Bg₂cap) / A
    with hLdef
  have ht1 : (0 : ℝ) ≤ 1 / (A * ε) := le_of_lt (div_pos one_pos (mul_pos hA hε))
  have ht2 : (0 : ℝ) ≤ (C₁ / (11/8 - 1) + Bg₁cap) / A :=
    div_nonneg (add_nonneg (div_nonneg hC₁nn (by norm_num)) hBg1cap_nn) (le_of_lt hA)
  have ht3 : (0 : ℝ) ≤ (C₂ / (11/8 - 1) + Bg₂cap) / A :=
    div_nonneg (add_nonneg (div_nonneg hC₂nn (by norm_num)) hBg2cap_nn) (le_of_lt hA)
  have hL : 1 ≤ L := by rw [hLdef]; linarith
  have hLpole : 1 / (A * ε) ≤ L := by rw [hLdef]; linarith
  have hLnum1 : (C₁ / (11/8 - 1) + Bg₁cap) / A ≤ L := by rw [hLdef]; linarith
  have hLnum2 : (C₂ / (11/8 - 1) + Bg₂cap) / A ≤ L := by rw [hLdef]; linarith
  clear_value L
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
  have hR32 : (11/8 : ℝ) < 3/2 := by norm_num
  have hβR : 2 - β < (11/8 : ℝ) := by linarith
  have himc0 : (11/8 : ℝ) + 2 ≤ |γ| := by linarith
  have hβσ : β < σ := by linarith
  have hALlb : 1 / ε ≤ A * L := by
    have h := mul_le_mul_of_nonneg_left hLpole hA.le
    rwa [show A * (1 / (A * ε)) = 1 / ε by field_simp] at h
  have hALε : (1 : ℝ) ≤ A * L * ε := by
    have h := mul_le_mul_of_nonneg_right hALlb hε.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hε)] at h
  have hσdelt : σ - 1 < ε := by
    rw [hσ_opt, div_lt_iff₀ hden]; nlinarith [hALε, mul_pos hA hε]
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
    exact (ht (σ : ℂ) (hsub ⟨hmemball, hmemcompl⟩)).trans (by linarith [hA0le])
  -- eval-point norms + Bg (σ-dependent)
  have hzn : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ = 2 - σ := by
    have he : (σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]; ring
  have hzn0 : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖ = 2 - σ := by rw [sub_zero]; exact hzn
  have hzn1 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖ = 2 - σ := by
    have he : (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]; ring
  have hzn10 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖ = 2 - σ := by
    rw [sub_zero]; exact hzn1
  have hz₀mem : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ < (11/8 : ℝ) := by rw [hzn]; linarith
  have hz₀mem2 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖ < (11/8 : ℝ) := by
    rw [hzn1]; linarith
  set Bg₁ : ℝ := 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6))
      * ((11/8 : ℝ) + ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖)
      / ((11/8 : ℝ) - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖) ^ 2 with hBg₁def
  set Bg₂ : ℝ := 4 * Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6))
      * ((11/8 : ℝ) + ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖)
      / ((11/8 : ℝ) - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖) ^ 2
    with hBg₂def
  clear_value Bg₁ Bg₂
  have hd1 : (0 : ℝ) < (11/8 : ℝ) - (2 - σ) := by linarith
  have hBg1_le : Bg₁ ≤ Bg₁cap := by
    rw [hBg₁def, hBg₁capdef, hzn0, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hAz1)
    gcongr <;> linarith
  have hBg2_le : Bg₂ ≤ Bg₂cap := by
    rw [hBg₂def, hBg₂capdef, hzn10, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hAz2)
    gcongr <;> linarith
  -- === wiring-lemma hypotheses ===
  have hgb₁ : ∀ g : ℂ → ℂ,
      CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g (11/8) →
      ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg₁ := by
    intro g D; rw [hBg₁def]; exact hg_bound_gamma (by norm_num) hR32 himc0 D hz₀mem
  have hgb₂ : ∀ g : ℂ → ℂ,
      CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) g (11/8) →
      ‖logDeriv g ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))‖ ≤ Bg₂ := by
    intro g D; rw [hBg₂def]
    exact hg_bound_gamma (by norm_num) hR32 (by nlinarith [h2γ, hΓ]) D hz₀mem2
  have hnum₁ : C₁ / ((11/8 : ℝ) - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg₁ ≤ A * L := by
    rw [hzn]
    have hRHS1 : C₁ / (11/8 - 1) + Bg₁cap ≤ A * L := by
      rw [mul_comm]; exact (div_le_iff₀ hA).mp hLnum1
    have hC1step : C₁ / ((11/8 : ℝ) - (2 - σ)) ≤ C₁ / (11/8 - 1) := by gcongr <;> linarith
    linarith [add_le_add hC1step hBg1_le]
  have hnum₂ : C₂ / ((11/8 : ℝ) - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖)
      + Bg₂ ≤ A * L := by
    rw [hzn1]
    have hRHS2 : C₂ / (11/8 - 1) + Bg₂cap ≤ A * L := by
      rw [mul_comm]; exact (div_le_iff₀ hA).mp hLnum2
    have hC2step : C₂ / ((11/8 : ℝ) - (2 - σ)) ≤ C₂ / (11/8 - 1) := by gcongr <;> linarith
    linarith [add_le_add hC2step hBg2_le]
  have hdiff₁ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hdiff₂ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; simp at this; linarith
  -- === run the wiring lemma ===
  have hreg : β ≤ 1 - 1 / (112 * (A * L)) :=
    dlvp_zeta_region_concrete_wired σ A L β γ k (11/8) Bg₁ C₁ Bg₂ C₂ hA hL hk hσ_opt hβ1 hσ2
      (by norm_num) hβR himc0 hmρ₀ hpole_pf hgb₁ hC₁ hnum₁ hgb₂ hC₂ hnum₂
  -- === L ≤ K·log|γ| ===
  have hLK : L ≤ K * Real.log |γ| := by
    set Lg1 : ℝ := Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) with hLg1
    set Lg2 : ℝ := Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) with hLg2
    have hg12 : Lg1 ≤ Lg2 := by
      rw [hLg1, hLg2]; apply Real.log_le_log (by positivity); gcongr
    have hLγ2 : Lg2 ≤ (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) * Real.log |γ| := by
      rw [hLg2]
      have hstep : (2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6) ≤ (15 / (2 - Real.pi ^ 2 / 6)) * |γ| := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]
        have h4 : 2 * |2 * γ| + 11 ≤ 15 * |γ| := by
          rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]; nlinarith [hγ1]
        nlinarith [h4]
      calc Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6))
          ≤ Real.log ((15 / (2 - Real.pi ^ 2 / 6)) * |γ|) := Real.log_le_log (by positivity) hstep
        _ = Real.log (15 / (2 - Real.pi ^ 2 / 6)) + Real.log |γ| :=
            Real.log_mul (by positivity) (by positivity)
        _ ≤ (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) * Real.log |γ| := by nlinarith [hlog15, hlogγ1]
    have heq1 : (C₁ / (11/8 - 1) + Bg₁cap) / A = M * Lg1 := by
      rw [hC₁def, hBg₁capdef, hMdef]; field_simp; ring
    have heq2 : (C₂ / (11/8 - 1) + Bg₂cap) / A = M * Lg2 := by
      rw [hC₂def, hBg₂capdef, hMdef]; field_simp; ring
    have hL2 : L = 1 + 1 / (A * ε) + M * Lg1 + M * Lg2 := by rw [hLdef, heq1, heq2]
    have hp1 : 0 ≤ M * (Lg2 - Lg1) := mul_nonneg hMpos.le (by linarith)
    have hp2 : 0 ≤ M * ((Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) * Real.log |γ| - Lg2) :=
      mul_nonneg hMpos.le (by linarith)
    have hp3 : 0 ≤ (1 + 1 / (A * ε)) * (Real.log |γ| - 1) := mul_nonneg (by positivity) (by linarith)
    rw [hL2, hKdef]; nlinarith [hp1, hp2, hp3]
  -- === conclude the rate ===
  have hden112 : (0:ℝ) < 112 * (A * L) := by positivity
  have hchain : 112 * (A * L) ≤ 112 * A * K * Real.log |γ| := by
    nlinarith [mul_le_mul_of_nonneg_left hLK (le_of_lt hA), hlogγpos, hKpos, hA]
  have hrecip : 1 / (112 * A * K * Real.log |γ|) ≤ 1 / (112 * (A * L)) :=
    one_div_le_one_div_of_le hden112 hchain
  have hce : (1 / (112 * A * K)) / Real.log |γ| = 1 / (112 * A * K * Real.log |γ|) := by rw [div_div]
  calc β ≤ 1 - 1 / (112 * (A * L)) := hreg
    _ ≤ 1 - (1 / (112 * A * K)) / Real.log |γ| := by rw [hce]; linarith [hrecip]

end ZeroFreeBridge

