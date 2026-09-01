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
import ZeroFreeBridge

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
      calc ‖w‖ ≤ ‖(u : ℂ)‖ + ‖γ * Complex.I‖ := by simpa [hw] using norm_add_le _ _
        _ = |u| + |γ| := by rw [Complex.norm_real]; simp [Complex.norm_mul]
        _ = u + γ := by rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
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

end ZeroFreeBridge
