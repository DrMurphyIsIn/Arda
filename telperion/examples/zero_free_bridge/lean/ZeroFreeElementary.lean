/- ELEMENTARY UNCONDITIONAL ZERO-FREE REGION (polynomial rate) -- the Hadamard-free route.

   The classical de la Vallee Poussin region needs `|ζ| ≪ log|t|` (the sharp near-line bound),
   which requires the Hadamard factorization of ξ (Jensen's formula, canonical products, the ζ'/ζ
   partial fraction -- ALL absent from Mathlib v4.32.0).  But a GENUINE UNCONDITIONAL region with a
   POLYNOMIAL rate is reachable from elementary tools ALONE:

     - the product inequality `|ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1`  (Mathlib nonvanishing machinery,
       `norm_LFunction_product_ge_one`, specialized to ζ),
     - the CRUDE strip growth bound `|ζ(σ+it)| ≤ C·|t|`             (Phase 2, `zeta_strip_bound`),
     - the pole `|ζ(σ)| ≤ C/(σ-1)` near `s = 1`                     (Mathlib residue),
     - Cauchy's derivative estimate `|ζ'| ≤ C·|t|` on a disk        (Mathlib) => near a zero `β+iγ`,
       `|ζ(σ+iγ)| = |ζ(σ+iγ) - ζ(β+iγ)| ≤ (σ-β)·sup|ζ'|`.

   Choosing `σ = 2 - β` (so `σ-1 = 1-β` and `σ-β = 2(1-β)`) makes the estimate PURELY INTEGER-POWER:
   the product bound reads `1 ≤ 16 c₁³ c₂ c₄⁴ (1-β) γ⁵`, giving

       β ≤ 1 - 1/(16 c₁³ c₂ c₄⁴ |γ|⁵),   i.e. a zero-free region  Re s > 1 - c/|t|⁵.

   Weaker than de la Vallee Poussin's `1 - c/log|t|` (the crude `|t|` growth, not `log|t|`, is what
   costs the rate), but a REAL, UNCONDITIONAL zero-free region -- and every input is elementary,
   sidestepping the Hadamard wall entirely.  This file is the ASSEMBLY (four bounds -> region);
   discharging the four bounds (all reachable) is the follow-on.  conjecture1_proved = False.
-/
import StripBound

open Filter Topology

namespace ZeroFreeBridge

/-- ELEMENTARY ZERO-FREE REGION ASSEMBLY.  At `σ = 2 - β` and height `γ ≥ 1`, given the four
    elementary bounds on the zeta magnitudes `Zσ = |ζ(2-β)|`, `Zσt = |ζ((2-β)+iγ)|`,
    `Zσ2t = |ζ((2-β)+2iγ)|` -- the product inequality, the pole bound, the crude strip growth
    bound, and the Cauchy-derivative bound at the zero -- the zero at `β+iγ` is pushed left of the
    1-line by an explicit polynomial gap `1/(16 c₁³ c₂ c₄⁴ γ⁵) ≤ 1 - β`. -/
theorem zeta_zero_free_poly_of {β γ c₁ c₂ c₄ Zσ Zσt Zσ2t : ℝ}
    (hβ1 : β < 1) (hγ : 1 ≤ γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₄ : 0 < c₄)
    (hZσ : 0 ≤ Zσ) (hZσt : 0 ≤ Zσt) (hZσ2t : 0 ≤ Zσ2t)
    (hprod : 1 ≤ Zσ ^ 3 * Zσt ^ 4 * Zσ2t)
    (hpole : Zσ ≤ c₁ / (1 - β))
    (hstrip : Zσ2t ≤ c₂ * γ)
    (hcauchy : Zσt ≤ 2 * (1 - β) * c₄ * γ) :
    1 / (16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * γ ^ 5) ≤ 1 - β := by
  have hη : 0 < 1 - β := by linarith
  have hγ0 : 0 < γ := by linarith
  -- Bound the product of magnitudes by the product of the four elementary bounds (all ≥ 0).
  have hub : Zσ ^ 3 * Zσt ^ 4 * Zσ2t
      ≤ (c₁ / (1 - β)) ^ 3 * (2 * (1 - β) * c₄ * γ) ^ 4 * (c₂ * γ) := by
    gcongr
  -- The `(1-β)³` in the pole cube cancels three of the four `(1-β)` powers from the Cauchy 4th power.
  have hsimp : (c₁ / (1 - β)) ^ 3 * (2 * (1 - β) * c₄ * γ) ^ 4 * (c₂ * γ)
      = 16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * (1 - β) * γ ^ 5 := by
    field_simp
    ring
  rw [hsimp] at hub
  have h1 : (1 : ℝ) ≤ 16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * (1 - β) * γ ^ 5 := le_trans hprod hub
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1]

/-- DISCHARGE of `hprod` for `riemannZeta`: the 3-4-1 product inequality
    `|ζ(1+x)|³ |ζ(1+x+iy)|⁴ |ζ(1+x+2iy)| ≥ 1` for `x > 0`, specialized from Mathlib's Dirichlet
    nonvanishing machinery (`DirichletCharacter.norm_LFunction_product_ge_one` at modulus `1`, where
    `LFunction_modOne_eq` sends every mod-1 character's L-function to `riemannZeta`). -/
theorem zeta_norm_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + Complex.I * y)‖ ^ 4
        * ‖riemannZeta (1 + x + 2 * Complex.I * y)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one
    (χ := (1 : DirichletCharacter ℂ 1)) hx y
  rw [ge_iff_le] at h
  -- `LFunctionTrivChar 1 = riemannZeta` (the mod-1 trivial character) and every mod-1
  -- character's L-function is `riemannZeta` (`LFunction_modOne_eq`, a `@[simp]` lemma).
  have htriv : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  rw [htriv] at h
  simp only [DirichletCharacter.LFunction_modOne_eq, norm_mul, norm_pow] at h
  exact h

/-- DISCHARGE of `hpole`: near `σ = 1`, `(σ-1)·|ζ(σ)| ≤ 2`, i.e. `|ζ(σ)| ≤ 2/(σ-1)`.  From the
    simple pole of `riemannZeta` at `s = 1` with residue `1` (`riemannZeta_residue_one`:
    `(s-1)·ζ(s) → 1`), composed along the real ray `σ ↓ 1`. -/
theorem zeta_pole_bound :
    ∃ δ₀ > (0 : ℝ), ∀ σ : ℝ, 1 < σ → σ < 1 + δ₀ → (σ - 1) * ‖riemannZeta (σ : ℂ)‖ ≤ 2 := by
  -- Pull the ℂ residue limit back to the real ray `𝓝[>] 1`.
  have hcast : Filter.Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Filter.Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 ((1 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : (1 : ℝ) < σ := hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [Complex.ofReal_eq_one] at h
      linarith
  have hcomp : Filter.Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta σ) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hcast
  -- Eventually on the ray, the residue-normalised modulus is `≤ 2`.
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] 1, (σ - 1) * ‖riemannZeta (σ : ℂ)‖ ≤ 2 := by
    have h1 := Metric.tendsto_nhds.mp hcomp 1 one_pos
    filter_upwards [h1, self_mem_nhdsWithin] with σ hσ1 hσpos
    have hσ : (1 : ℝ) < σ := hσpos
    have hre : ‖((σ : ℂ) - 1) * riemannZeta σ‖ = (σ - 1) * ‖riemannZeta (σ : ℂ)‖ := by
      rw [norm_mul]; congr 1
      rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    rw [dist_eq_norm] at hσ1
    have hsub := norm_sub_norm_le (((σ : ℂ) - 1) * riemannZeta σ) 1
    rw [norm_one] at hsub
    rw [← hre]; linarith [hsub, hσ1]
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨δ₀, hδ₀, hsub⟩ := hev
  refine ⟨δ₀, hδ₀, fun σ h1 h2 => ?_⟩
  apply hsub
  refine ⟨?_, h1⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < σ - 1)]
  linarith

/-- Geometric input for the Cauchy estimate: on the closed disk of radius `1/2` about `w = u+iγ`
    (with `3/4 ≤ u ≤ 2`, `2 ≤ γ`), every point `z` has `Re z ≥ 1/4 > 0`, `‖z-1‖ ≥ γ-1/2 > 0`,
    and `‖z‖ ≤ γ + 3`, so `z ∈ stripDomain` and `zeta_strip_bound` gives `‖ζ(z)‖ ≤ 12·γ`. -/
theorem zeta_sphere_bound {u γ : ℝ} (hu : 3 / 4 ≤ u) (hu2 : u ≤ 2) (hγ : 2 ≤ γ)
    {z : ℂ} (hz : z ∈ Metric.closedBall ((u : ℂ) + γ * Complex.I) (1 / 2)) :
    ‖riemannZeta z‖ ≤ 12 * γ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  set w : ℂ := (u : ℂ) + γ * Complex.I with hw
  have hwre : w.re = u := by simp [hw]
  have hwim : w.im = γ := by simp [hw]
  -- `Re z = Re w + Re (z - w)`, and `|Re (z-w)| ≤ ‖z-w‖ ≤ 1/2`.
  have hzre_lb : (1 : ℝ) / 4 ≤ z.re := by
    have h1 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
    have h2 : (z - w).re = z.re - u := by rw [Complex.sub_re, hwre]
    rw [h2] at h1
    have := abs_le.mp (le_trans h1 hz)
    linarith [this.1]
  have hzim_lb : γ - 1 / 2 ≤ |z.im| := by
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    have h2 : (z - w).im = z.im - γ := by rw [Complex.sub_im, hwim]
    rw [h2] at h1
    have := abs_le.mp (le_trans h1 hz)
    have : γ - 1 / 2 ≤ z.im := by linarith [this.1]
    exact le_trans this (le_abs_self _)
  have hzrepos : (0 : ℝ) < z.re := by linarith
  have hzne1 : z ≠ 1 := by
    intro h; rw [h] at hzim_lb; simp at hzim_lb; linarith
  have hmem : z ∈ stripDomain := ⟨hzrepos, by simpa using hzne1⟩
  -- Upper bound on `‖z‖` and lower bounds on `‖z-1‖`, `Re z`, then feed `zeta_strip_bound`.
  have hznorm : ‖z‖ ≤ γ + 3 := by
    have hw_norm : ‖w‖ ≤ u + γ := by
      have h := norm_add_le (u : ℂ) (γ * Complex.I)
      simp only [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one,
        Real.norm_eq_abs] at h
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u), abs_of_nonneg (by linarith : (0 : ℝ) ≤ γ)]
        at h
      rw [hw]; exact h
    calc ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by simpa using norm_le_norm_add_norm_sub' z w
      _ ≤ (u + γ) + 1 / 2 := by linarith
      _ ≤ γ + 3 := by linarith
  have hz1_lb : γ - 1 / 2 ≤ ‖z - 1‖ := by
    calc γ - 1 / 2 ≤ |z.im| := hzim_lb
      _ = |(z - 1).im| := by rw [Complex.sub_im]; simp
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have hsb := zeta_strip_bound hmem
  -- `‖ζ(z)‖ ≤ ‖z‖/‖z-1‖ + ‖z‖/Re z ≤ 4 + (4γ+12) ≤ 12γ` (each division bounded via `div_le_iff₀`).
  have hd1 : (0 : ℝ) < ‖z - 1‖ := by linarith
  have hb_zterm : ‖z‖ / ‖z - 1‖ ≤ 4 := by
    rw [div_le_iff₀ hd1]; nlinarith [hznorm, hz1_lb, hγ]
  have hb_reterm : ‖z‖ / z.re ≤ 4 * γ + 12 := by
    rw [div_le_iff₀ hzrepos]; nlinarith [hznorm, hzre_lb, hγ]
  calc ‖riemannZeta z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re := hsb
    _ ≤ 4 + (4 * γ + 12) := by linarith [hb_zterm, hb_reterm]
    _ ≤ 12 * γ := by linarith

/-- hcauchy step 2 -- Cauchy derivative estimate: `‖ζ'(u+iγ)‖ ≤ 24·γ`.  `ζ` is `DiffContOnCl` on the
    radius-`1/2` disk about `w = u+iγ` (holomorphic away from `s=1`, which the disk avoids), its
    modulus on the boundary sphere is `≤ 12·γ` (`zeta_sphere_bound`), so Cauchy's estimate
    (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) gives `‖ζ'(w)‖ ≤ 12γ/(1/2) = 24γ`. -/
theorem zeta_deriv_bound {u γ : ℝ} (hu : 3 / 4 ≤ u) (hu2 : u ≤ 2) (hγ : 2 ≤ γ) :
    ‖deriv riemannZeta ((u : ℂ) + γ * Complex.I)‖ ≤ 24 * γ := by
  set w : ℂ := (u : ℂ) + γ * Complex.I with hw
  have hwim : w.im = γ := by simp [hw]
  have hne : ∀ z ∈ Metric.closedBall w (1 / 2), z ≠ 1 := by
    intro z hz h1
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    subst h1
    have hle : |((1 : ℂ) - w).im| ≤ ‖(1 : ℂ) - w‖ := Complex.abs_im_le_norm _
    have him : ((1 : ℂ) - w).im = -γ := by rw [Complex.sub_im, hwim]; simp
    rw [him, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ γ)] at hle
    linarith
  have hd : DiffContOnCl ℂ riemannZeta (Metric.ball w (1 / 2)) := by
    constructor
    · intro z hz
      exact (differentiableAt_riemannZeta
        (hne z (Metric.ball_subset_closedBall hz))).differentiableWithinAt
    · rw [closure_ball w (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      intro z hz
      exact (differentiableAt_riemannZeta (hne z hz)).continuousAt.continuousWithinAt
  have hC : ∀ z ∈ Metric.sphere w (1 / 2), ‖riemannZeta z‖ ≤ 12 * γ := fun z hz =>
    zeta_sphere_bound hu hu2 hγ (Metric.sphere_subset_closedBall hz)
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 2) hd hC
  calc ‖deriv riemannZeta w‖ ≤ 12 * γ / (1 / 2) := hcau
    _ = 24 * γ := by ring

/-- hcauchy step 3 -- the segment mean-value bound at a zero.  If `ζ(β+iγ) = 0` and `3/4 ≤ β ≤ σ ≤ 2`,
    `2 ≤ γ`, then along the horizontal segment `u ↦ ζ(u+iγ)` (whose derivative is `‖·‖ ≤ 24γ` by
    `zeta_deriv_bound`) the mean-value inequality gives `‖ζ(σ+iγ)‖ = ‖ζ(σ+iγ) - ζ(β+iγ)‖ ≤ 24γ·(σ-β)`. -/
theorem zeta_hcauchy {β σ γ : ℝ} (hβ : 3 / 4 ≤ β) (hσ : σ ≤ 2) (hβσ : β ≤ σ) (hγ : 2 ≤ γ)
    (hzero : riemannZeta ((β : ℂ) + γ * Complex.I) = 0) :
    ‖riemannZeta ((σ : ℂ) + γ * Complex.I)‖ ≤ 24 * γ * (σ - β) := by
  set g : ℝ → ℂ := fun u => riemannZeta ((u : ℂ) + γ * Complex.I) with hg
  have hderiv : ∀ u ∈ Set.Icc β σ,
      HasDerivWithinAt g (deriv riemannZeta ((u : ℂ) + γ * Complex.I)) (Set.Icc β σ) u := by
    intro u hu
    have hune : ((u : ℂ) + γ * Complex.I) ≠ 1 := by
      intro h; have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, Complex.one_im] at him
      linarith
    have hφ : HasDerivAt (fun t : ℝ => (t : ℂ) + γ * Complex.I) 1 u := by
      simpa using (Complex.ofRealCLM.hasDerivAt).add_const (γ * Complex.I)
    have hζ : HasDerivAt riemannZeta (deriv riemannZeta ((u : ℂ) + γ * Complex.I))
        ((u : ℂ) + γ * Complex.I) := (differentiableAt_riemannZeta hune).hasDerivAt
    have hcomp := hζ.scomp u hφ
    simp only [one_smul] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Icc β σ, ‖deriv riemannZeta ((u : ℂ) + γ * Complex.I)‖ ≤ 24 * γ := by
    intro u hu
    exact zeta_deriv_bound (by linarith [hu.1] : 3 / 4 ≤ u) (by linarith [hu.2] : u ≤ 2) hγ
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc β σ)
    (Set.left_mem_Icc.mpr hβσ) (Set.right_mem_Icc.mpr hβσ)
  simp only [hg] at hmv
  rw [hzero, sub_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - β)] at hmv
  linarith [hmv]

/-- The `hstrip` input at the `2γ` point: `‖ζ((2-β)+2iγ)‖ ≤ 5·γ` for `0 ≤ β ≤ 1`, `2 ≤ γ`.
    `Re s = 2-β ≥ 1 > 0`, `‖s-1‖ ≥ 2γ`, `‖s‖ ≤ 2γ+2`, so `zeta_strip_bound` gives the bound. -/
theorem zeta_strip_2t_bound {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hγ : 2 ≤ γ) :
    ‖riemannZeta ((2 - β : ℝ) + 2 * γ * Complex.I)‖ ≤ 5 * γ := by
  set s : ℂ := ((2 - β : ℝ) : ℂ) + 2 * γ * Complex.I with hs
  have hsre : s.re = 2 - β := by simp [hs]
  have hsim : s.im = 2 * γ := by simp [hs]
  have hsre_pos : (0 : ℝ) < s.re := by rw [hsre]; linarith
  have hsne1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hmem : s ∈ stripDomain := ⟨hsre_pos, by simpa using hsne1⟩
  have hsnorm : ‖s‖ ≤ 2 * γ + 2 := by
    have h1 : ‖s‖ ≤ ‖((2 - β : ℝ) : ℂ)‖ + ‖2 * γ * Complex.I‖ := by
      rw [hs]; exact norm_add_le ((2 - β : ℝ) : ℂ) (2 * γ * Complex.I)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - β)] at h1
    have hγ0 : (0 : ℝ) ≤ γ := by linarith
    have h2 : ‖2 * γ * Complex.I‖ = 2 * γ := by
      simp [Complex.norm_mul, abs_of_nonneg hγ0]
    rw [h2] at h1; linarith
  have hs1_lb : 2 * γ ≤ ‖s - 1‖ := by
    calc 2 * γ = |s.im| := by rw [hsim, abs_of_nonneg (by linarith)]
      _ = |(s - 1).im| := by rw [Complex.sub_im]; simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hsb := zeta_strip_bound hmem
  have hd1 : (0 : ℝ) < ‖s - 1‖ := by linarith
  have hb1 : ‖s‖ / ‖s - 1‖ ≤ 2 := by
    rw [div_le_iff₀ hd1]; nlinarith [hsnorm, hs1_lb, hγ]
  have hb2 : ‖s‖ / s.re ≤ 2 * γ + 2 := by
    rw [div_le_iff₀ hsre_pos, hsre]; nlinarith [hsnorm, hβ1, hβ0, hγ]
  calc ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := hsb
    _ ≤ 2 + (2 * γ + 2) := by linarith [hb1, hb2]
    _ ≤ 5 * γ := by linarith

/-- THE ELEMENTARY UNCONDITIONAL ZERO-FREE REGION (polynomial rate, Hadamard-free).
    There is `c > 0` such that every nontrivial-strip zero `β+iγ` of `riemannZeta` with `2 ≤ γ`
    satisfies `β ≤ 1 - c/γ⁵` -- i.e. `Re s > 1 - c/|t|⁵` is zero-free.  Assembled from the four
    kernel-verified elementary bounds (`zeta_norm_product_ge_one`, `zeta_pole_bound`,
    `zeta_strip_2t_bound`, `zeta_hcauchy`) via `zeta_zero_free_poly_of`, with the far-from-line case
    handled by Mathlib's `riemannZeta_ne_zero_of_one_le_re`.  Weaker than de la Vallee Poussin's
    `1 - c/log|t|` (the crude `|ζ| ≤ C|t|` growth costs the rate), but UNCONDITIONAL and sidestepping
    the Hadamard factorization entirely.  conjecture1_proved = False. -/
theorem riemannZeta_zero_free_poly :
    ∃ c > (0 : ℝ), ∀ β γ : ℝ,
      riemannZeta ((β : ℂ) + γ * Complex.I) = 0 → 2 ≤ γ → β ≤ 1 - c / γ ^ 5 := by
  obtain ⟨δ₀, hδ₀, hpoleδ⟩ := zeta_pole_bound
  set δ₁ : ℝ := min δ₀ (1 / 4) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ (by norm_num)
  refine ⟨min (32 * δ₁) (1 / 212336640), by positivity, ?_⟩
  set c := min (32 * δ₁) (1 / 212336640) with hc
  have hc_le1 : c ≤ 32 * δ₁ := min_le_left _ _
  have hc_le2 : c ≤ 1 / 212336640 := min_le_right _ _
  intro β γ hzero hγ
  have hγ5 : (32 : ℝ) ≤ γ ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ γ ^ 5 := by gcongr <;> linarith
  -- `β < 1`: else `ζ(β+iγ) ≠ 0` (Re ≥ 1).
  have hβ1 : β < 1 := by
    by_contra h; push_neg at h
    have hre : (1 : ℝ) ≤ ((β : ℂ) + γ * Complex.I).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_mul]; linarith
    exact riemannZeta_ne_zero_of_one_le_re hre hzero
  by_cases hcase : β ≤ 1 - δ₁
  · -- far case: `1 - β ≥ δ₁ ≥ c/γ⁵`.
    have hgap : c / γ ^ 5 ≤ δ₁ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hc_le1, hγ5, hδ₁0]
    linarith
  · -- near case: run the machinery at `σ = 2 - β`.
    push_neg at hcase
    have hβ34 : (3 : ℝ) / 4 ≤ β := by have : δ₁ ≤ 1 / 4 := min_le_right _ _; linarith
    have hσδ₀ : 2 - β < 1 + δ₀ := by have : δ₁ ≤ δ₀ := min_le_left _ _; linarith
    have hprod := zeta_norm_product_ge_one (show (0 : ℝ) < 1 - β by linarith) γ
    -- `he0` rewrites the common `1 + ↑(1-β)` in ALL three factors to `↑(2-β)`.
    have he0 : (1 : ℂ) + ((1 - β : ℝ) : ℂ) = ((2 - β : ℝ) : ℂ) := by push_cast; ring
    rw [he0] at hprod
    have hpole : ‖riemannZeta ((2 - β : ℝ) : ℂ)‖ ≤ 2 / (1 - β) := by
      have h := hpoleδ (2 - β) (by linarith) hσδ₀
      rw [show (2 - β) - 1 = 1 - β by ring] at h
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - β)]
      nlinarith [h]
    have hstrip : ‖riemannZeta (((2 - β : ℝ) : ℂ) + 2 * Complex.I * γ)‖ ≤ 5 * γ := by
      have h := zeta_strip_2t_bound (β := β) (by linarith) (by linarith) hγ
      rw [show ((2 - β : ℝ) : ℂ) + 2 * γ * Complex.I
          = ((2 - β : ℝ) : ℂ) + 2 * Complex.I * γ by ring] at h
      exact h
    have hcauchy : ‖riemannZeta (((2 - β : ℝ) : ℂ) + Complex.I * γ)‖ ≤ 2 * (1 - β) * 24 * γ := by
      have h := zeta_hcauchy hβ34 (by linarith : 2 - β ≤ 2) (by linarith : β ≤ 2 - β) hγ hzero
      rw [show 24 * γ * ((2 - β) - β) = 2 * (1 - β) * 24 * γ by ring,
          show ((2 - β : ℝ) : ℂ) + γ * Complex.I
          = ((2 - β : ℝ) : ℂ) + Complex.I * γ by ring] at h
      exact h
    have hgap := zeta_zero_free_poly_of hβ1 (by linarith : (1 : ℝ) ≤ γ)
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 24)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hprod hpole hstrip hcauchy
    rw [show (16 : ℝ) * 2 ^ 3 * 5 * 24 ^ 4 * γ ^ 5 = 212336640 * γ ^ 5 by ring] at hgap
    have hle : c / γ ^ 5 ≤ 1 - β := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 212336640 * γ ^ 5)] at hgap
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < γ ^ 5)]
      nlinarith [hgap, hc_le2, hγ5]
    linarith

end ZeroFreeBridge
