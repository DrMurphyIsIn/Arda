/- PHASE 4 (dVP frontier, the CAPSTONE WIRING): the concrete instantiation of
   `dlvp_zeta_region_of_bc_sums` for an actual ζ-zero `ρ₀ = β+iγ` (`β < 1`).

   This discharges — internally, for the two disks `c₀ = 2+iγ` (height γ) and `c₁ = 2+2iγ`
   (height 2γ) — every hypothesis of the lower-layer region theorem EXCEPT the pole bound and the
   two O(L) numeric constraints:
     * both `CanonicalDecomp`s (`zeta_recentered_canonical_decomp`), analyticity bundles
       (`zeta_recenter_ana_closedBall`/`.mono`), and `MeromorphicOn`s;
     * `hbc₁` (height γ) via `hbc1_from_bounds` fed by the abstract `Bg₁`/`C₁` bounds
       (`hgb₁`, `hC₁` via `sum_divisor_recenter_le_finsum`);
     * `hbc₂` (height 2γ) via the PARALLEL `c₁`-disk `hbc1_from_bounds`, dropped to `A·L` with
       `htwo_shape_of_bc_sum` and recentred to the `c₀` form (`neg_logDeriv_zeta_recenter_re`),
       with `s₂ = ∅`;
     * the divisor/geometry data for the concrete zero (`divisor_comp_const_add_apply`,
       `zeta_zero_re_lt`, `zeta_divisor_nonneg`).

   The remaining inputs — the pole bound `hpole_pf` (via `hpole_bounded`, needs `σ` near 1) and the
   two numeric couplings `hnum₁`/`hnum₂` (`C/(R-‖z₀‖) + Bg ≤ A·L`, with `Bg = O(L)` from
   `hg_bound_gamma` and `C = O(L)` from `sum_divisor_recenter_le_jensen`) — are taken as clean
   hypotheses here: they are the numeric-coupling crux, isolated for a dedicated closing lemma.
   `Bg₁`/`C₁`/`Bg₂`/`C₂` are abstracted so the caller supplies the explicit O(L) values.

   conjecture1_proved = False (NOT a proof of RH — this is a REDUCTION).
-/
import DlvpZetaBcBridge
import DlvpZetaHbc1
import DlvpZetaCountReconcile
import DlvpZetaRecenterDecomp
import DlvpZetaAnaFoundation
import DlvpZetaZeroLoc
import DlvpBlaschkeAnalytic
import DlvpZetaRecenterEq

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **dVP region concrete WIRING.**  Instantiates `dlvp_zeta_region_of_bc_sums` for a concrete
    ζ-zero `ρ₀ = β+iγ` (`β < 1`), on the two disks `c₀ = 2+iγ` (height γ) and `c₁ = 2+2iγ`
    (height 2γ).  Discharges `hbc₁`, `hbc₂`, and all divisor/geometry data internally; takes the
    pole bound and the two O(L) numeric constraints (`Bg`/`C` abstracted) as hypotheses. -/
theorem dlvp_zeta_region_concrete_wired
    (σ A L β γ : ℝ) (k : ℤ) (R : ℝ) (Bg₁ C₁ Bg₂ C₂ : ℝ)
    (hA : 0 < A) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L))))
    (hβ1 : β < 1) (hσ2 : σ ≤ 2)
    (hR : 0 < R) (hβR : 2 - β < R) (himc0 : R + 2 ≤ |γ|)
    (hmρ₀ : divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) ((β : ℂ) + (γ : ℂ) * I) = k)
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    (hgb₁ : ∀ g : ℂ → ℂ,
        CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R →
        ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg₁)
    (hC₁ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) ρ : ℤ) : ℝ) ≤ C₁)
    (hnum₁ : C₁ / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg₁ ≤ A * L)
    (hgb₂ : ∀ g : ℂ → ℂ,
        CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) g R →
        ‖logDeriv g ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))‖ ≤ Bg₂)
    (hC₂ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ : ℤ) : ℝ)
             ≤ C₂)
    (hnum₂ : C₂ / (R - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖) + Bg₂
             ≤ A * L) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  -- basic derived scalar facts
  have hden : (0 : ℝ) < 2 * (3 * A + 5 * (A * L)) := by
    have : (0 : ℝ) < A * L := mul_pos hA (by linarith)
    nlinarith [hA]
  have hσ1 : 1 < σ := by
    have : 0 < σ - 1 := by rw [hσ_opt]; exact div_pos one_pos hden
    linarith
  have hR1 : 1 < R := by linarith
  have hσR : 2 - σ < R := by linarith
  have hβσ : β < σ := by linarith
  -- centre real/imag parts
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : ((2 : ℂ) + (γ : ℂ) * I).im = γ := by simp
  have hc1re : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re = 2 := by simp
  have hc1im : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).im = 2 * γ := by simp
  -- 1 ∉ the two closed balls
  have h1c0 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + (γ : ℂ) * I) R :=
    one_notMem_closedBall_of_himc (by rw [hc0im]; exact himc0)
  have h1c1 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R := by
    refine one_notMem_closedBall_of_himc ?_
    rw [hc1im]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    have : |γ| ≤ |2 * γ| := by rw [abs_mul, h2]; nlinarith [abs_nonneg γ]
    linarith
  have hc0lt : (1 : ℝ) < ((2 : ℂ) + (γ : ℂ) * I).re := by rw [hc0re]; norm_num
  have hc1lt : (1 : ℝ) < ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re := by rw [hc1re]; norm_num
  -- ζ ≠ 1 differentiability points
  have hev0_re : ((σ : ℂ) + (γ : ℂ) * I).re = σ := by simp
  have hev1_re : ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re = σ := by simp
  have hdiff₁ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; rw [hev0_re] at this; simp at this; linarith
  have hdiff₂ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; rw [hev1_re] at this; simp at this; linarith
  -- ============ c₀ disk bundle (height γ) ============
  obtain ⟨g₀, D₀⟩ := zeta_recentered_canonical_decomp ((2 : ℂ) + (γ : ℂ) * I) R hR h1c0 hc0lt
  have hana0 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w))
      (closedBall 0 R) := zeta_recenter_ana_closedBall _ R h1c0
  have hf_ana0 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) :=
    hana0.mono ball_subset_closedBall
  have hζ_ana_cl0 : AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) :=
    zeta_analyticOnNhd_disk _ R h1c0
  have hf_mero0 : MeromorphicOn riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) :=
    MeromorphicOn.mono_set (hζ_ana_cl0.meromorphicOn) ball_subset_closedBall
  have hf'_mero0 : MeromorphicOn (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) :=
    hf_ana0.meromorphicOn
  have hg_ana0 := canonicalDecomp_analyticOnNhd D₀
  have hg_ne0 := canonicalDecomp_ne_zero D₀
  have hfin0 : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D₀.meromorphicOn.divisor_ball_support_finite
  have heval_ne0 : riemannZeta (((2 : ℂ) + (γ : ℂ) * I)
      + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))) ≠ 0 := by
    rw [concrete_hcz]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hev0_re]; linarith)
  -- count bound for c₀
  have hcount₁ : (∑ u ∈ hfin0.toFinset,
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ)) ≤ C₁ := by
    have hZ := sum_divisor_recenter_le_finsum hf_mero0 hf'_mero0 hζ_ana_cl0 hfin0
    calc (∑ u ∈ hfin0.toFinset,
          (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        = ((∑ u ∈ hfin0.toFinset,
            divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℤ) : ℝ) := by
          push_cast; ring
      _ ≤ ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) R) ρ : ℤ) : ℝ) := by
          exact_mod_cast hZ
      _ ≤ C₁ := hC₁
  -- height-γ hbc₁
  have hbc₁ := hbc1_from_bounds σ γ hR hσ1 hσ2 hσR g₀ D₀ hf_ana0 hg_ana0 hg_ne0 hfin0 heval_ne0
    (hgb₁ g₀ D₀) hcount₁ hnum₁
  -- domain facts for s₁
  have hs₁_dom : ∀ u ∈ hfin0.toFinset,
      u ∈ ball (0 : ℂ) R ∧ ((2 : ℂ) + (γ : ℂ) * I) + u ∈ ball ((2 : ℂ) + (γ : ℂ) * I) R := by
    intro u hu
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    refine ⟨huball, ?_⟩
    rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
  have hm₁ : ∀ ρ ∈ hfin0.toFinset.image (fun u => ((2 : ℂ) + (γ : ℂ) * I) + u),
      0 ≤ divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) ρ :=
    fun ρ _ => zeta_divisor_nonneg h1c0 ρ
  -- ρ₀ membership + zero-location
  have hρ₀mem : (β : ℂ) + (γ : ℂ) * I
      ∈ hfin0.toFinset.image (fun u => ((2 : ℂ) + (γ : ℂ) * I) + u) := by
    have heq : (β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((β - 2 : ℝ) : ℂ) := by
      push_cast; ring
    have hu0ball : (β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : β - 2 ≤ 0)]
      linarith
    have hρ₀ball : (β : ℂ) + (γ : ℂ) * I ∈ ball ((2 : ℂ) + (γ : ℂ) * I) R := by
      rw [mem_ball_iff_norm, heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : β - 2 ≤ 0)]
      linarith
    have hcadd : ((2 : ℂ) + (γ : ℂ) * I) + ((β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
        = (β : ℂ) + (γ : ℂ) * I := by ring
    have hdivne : divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R)
        ((β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) ≠ 0 := by
      rw [divisor_comp_const_add_apply _ hf_mero0 hf'_mero0 hu0ball (by rw [hcadd]; exact hρ₀ball),
        hcadd, hmρ₀]
      omega
    refine Finset.mem_image.mpr ⟨(β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I), ?_, by ring⟩
    rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero]; exact hdivne
  have hother₁ : ∀ ρ ∈ hfin0.toFinset.image (fun u => ((2 : ℂ) + (γ : ℂ) * I) + u),
      ρ ≠ (β : ℂ) + (γ : ℂ) * I → ρ.re < σ := by
    intro ρ hρ _
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R)).supportWithinDomain
        (Function.mem_support.mpr hune)
    have hcuball : ((2 : ℂ) + (γ : ℂ) * I) + u ∈ ball ((2 : ℂ) + (γ : ℂ) * I) R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    have hdivρ : divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) R) (((2 : ℂ) + (γ : ℂ) * I) + u) ≠ 0 := by
      rw [← divisor_comp_const_add_apply _ hf_mero0 hf'_mero0 huball hcuball]; exact hune
    exact zeta_zero_re_lt hσ1 h1c0 hcuball hdivρ
  -- ============ c₁ disk bundle (height 2γ) ============
  obtain ⟨g₁, D₁⟩ := zeta_recentered_canonical_decomp ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R hR h1c1 hc1lt
  have hana1 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
      (closedBall 0 R) := zeta_recenter_ana_closedBall _ R h1c1
  have hf_ana1 : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
      (ball 0 R) := hana1.mono ball_subset_closedBall
  have hζ_ana_cl1 : AnalyticOnNhd ℂ riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) :=
    zeta_analyticOnNhd_disk _ R h1c1
  have hf_mero1 : MeromorphicOn riemannZeta (ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) :=
    MeromorphicOn.mono_set (hζ_ana_cl1.meromorphicOn) ball_subset_closedBall
  have hf'_mero1 : MeromorphicOn (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
      (ball 0 R) := hf_ana1.meromorphicOn
  have hg_ana1 := canonicalDecomp_analyticOnNhd D₁
  have hg_ne1 := canonicalDecomp_ne_zero D₁
  have hfin1 : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
        (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D₁.meromorphicOn.divisor_ball_support_finite
  have heval_ne1 : riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
      + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))) ≠ 0 := by
    rw [concrete_hcz]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hev1_re]; linarith)
  have hcount₂ : (∑ u ∈ hfin1.toFinset,
      (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        ≤ C₂ := by
    have hZ := sum_divisor_recenter_le_finsum hf_mero1 hf'_mero1 hζ_ana_cl1 hfin1
    calc (∑ u ∈ hfin1.toFinset,
          (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        = ((∑ u ∈ hfin1.toFinset,
            divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u
              : ℤ) : ℝ) := by push_cast; ring
      _ ≤ ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ : ℤ) : ℝ) := by
          exact_mod_cast hZ
      _ ≤ C₂ := hC₂
  -- c₁ BC-SUM
  have hbc_c1 := hbc1_from_bounds σ (2 * γ) hR hσ1 hσ2 hσR g₁ D₁ hf_ana1 hg_ana1 hg_ne1 hfin1
    heval_ne1 (hgb₂ g₁ D₁) hcount₂ hnum₂
  have hs₂_dom : ∀ u ∈ hfin1.toFinset,
      u ∈ ball (0 : ℂ) R ∧ ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u
        ∈ ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R := by
    intro u hu
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u
        ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
        (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hune)
    refine ⟨huball, ?_⟩
    rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
  have hm_c1 : ∀ ρ ∈ hfin1.toFinset.image (fun u => ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u),
      0 ≤ divisor riemannZeta (ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R) ρ :=
    fun ρ _ => zeta_divisor_nonneg h1c1 ρ
  have hlt_c1 : ∀ ρ ∈ hfin1.toFinset.image (fun u => ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u),
      ρ.re < σ := by
    intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨u, hu, rfl⟩ := hρ
    have hune : divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) (ball 0 R) u
        ≠ 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, neg_ne_zero] at hu; exact hu
    have huball : u ∈ ball (0 : ℂ) R :=
      (divisor (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w))
        (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hune)
    have hcuball : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u
        ∈ ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left]; rwa [mem_ball_zero_iff] at huball
    have hdivρ : divisor riemannZeta (ball ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R)
        (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + u) ≠ 0 := by
      rw [← divisor_comp_const_add_apply _ hf_mero1 hf'_mero1 huball hcuball]; exact hune
    exact zeta_zero_re_lt hσ1 h1c1 hcuball hdivρ
  -- c₁ height-2γ shape: Re(-ζ'/ζ(σ+2iγ)) ≤ A*L
  have hcz_c1 : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
      + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
      = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I := by ring
  have htwo := htwo_shape_of_bc_sum ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) σ γ (A * L) R
    hf_mero1 hf'_mero1 hfin1.toFinset hs₂_dom hcz_c1 hdiff₂ hbc_c1 hm_c1 hlt_c1
  -- convert htwo to the c₀-recentred hbc₂ form (s₂ = ∅)
  have hbc₂ : (-(logDeriv (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w))
        ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)))).re
      ≤ A * L - (∑ u ∈ (∅ : Finset ℂ),
          (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℂ)
            / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) - u)).re := by
    rw [Finset.sum_empty, Complex.zero_re, sub_zero]
    have hdc0 : DifferentiableAt ℂ riemannZeta
        (((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))) := by
      rw [show ((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
          = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I from by ring]
      exact hdiff₂
    rw [neg_logDeriv_zeta_recenter_re ((2 : ℂ) + (γ : ℂ) * I)
      ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) hdc0,
      show ((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
          = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I from by ring]
    exact htwo
  -- ============ final assembly ============
  have hcz₂ : ((2 : ℂ) + (γ : ℂ) * I)
      + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
      = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I := by ring
  exact dlvp_zeta_region_of_bc_sums ((2 : ℂ) + (γ : ℂ) * I) σ A L β γ k R hA hL hk hσ_opt hβσ
    hf_mero0 hf'_mero0 hpole_pf
    hfin0.toFinset hs₁_dom (concrete_hcz σ γ) hdiff₁ hbc₁ hm₁ ((β : ℂ) + (γ : ℂ) * I) hρ₀mem rfl
    hmρ₀ hother₁
    (∅ : Finset ℂ) (by intro u hu; exact absurd hu (Finset.notMem_empty u)) hcz₂ hdiff₂ hbc₂
    (by intro ρ hρ; rw [Finset.image_empty] at hρ; exact absurd hρ (Finset.notMem_empty ρ))
    (by intro ρ hρ; rw [Finset.image_empty] at hρ; exact absurd hρ (Finset.notMem_empty ρ))

end ZeroFreeBridge
