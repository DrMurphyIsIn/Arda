/-  RSTheta.lean -- ANDURIL Riemann-Siegel brick B0 (theta): a HEIGHT-UNIFORM kernel enclosure of
    the Riemann-Siegel phase, plus one instance at t = 280000.

    ## Provenance

    Promoted on 2026-09-23 from `Probes/RSDesign_theta.lean`, the calibration probe of the RS design
    memo (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 4.0 and op O-4). Every proof is
    unchanged. Two things differ from the probe:

      * The statement of the registry theorem `gaussBranch_theta_sub_thetaMain_le` now spells every
        name in full: `Filter.Tendsto`, `ThetaGap.imLnVal`, `Filter.atTop`, `nhds`. That makes it the
        verbatim text of the proposed `AND_theta_branch` statement (memo op O-4). The grant gate
        matches statement to artifact by normalized text, and the registry statement cannot rely on
        this file's `open` lines. Both spellings elaborate to the same term.
      * The trailing `#print axioms` lines moved to the guard `AxiomGuardRSTheta.lean`.

    The namespace stays `RSDesignTheta`, so names cited from the probe still resolve.

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms).

    The island's sign bridge `ZeroSignDecomp.gLine_sign_decomp_t` writes
        gLine t = M * (cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it)),   M > 0,
        phi = Lam - (t/2) log pi,   Lam = lim_n imLnVal (1/4) (t/2) n,
    so every on-line sign needs a box for `phi` (= the Riemann-Siegel theta).  The existing route
    (`ForgeRate.rate_at`) bounds `|Lam - imLnVal x y n0|` by `2(|y|(x+1) + |y|^3/(3 n0))/n0`, which needs
    `n0 >> y^(3/2)` arctan terms: about 10^9 terms at t = 280000.  That is the "theta Euler route
    dies above a few hundred" wall.

    This file replaces the rate bound by a CLOSED-FORM Stirling bracket with an explicit remainder,
    valid at EVERY height, proved by an elementary convex-trapezoid argument (no Bernoulli
    functions, no polygamma, no complex Stirling, no Mathlib gap):

      * `trapezoid_convex`   : for F' = f, f' = g, g monotone on [a, a+1]:
                               0 <= (f a + f (a+1))/2 - (F (a+1) - F a) <= (g (a+1) - g a)/4.
      * `lam_bracket`        : for x > 0, y >= 0, any n0, and Lam = lim imLnVal x y:
            C - y/(4((x+n0)^2 + y^2)) <= Lam <= C,
            C = FA n0 + fA n0 / 2 - sum_{k <= n0} fA k - y,
            fA u = arctan (y/(x+u)),  FA u = (x+u) arctan (y/(x+u)) + (y/2) log ((x+u)^2 + y^2).
      * `theta_bracket`      : n0 = 0, x = 1/4, y = t/2, for every t > 0:
            thetaS t - 1/(2t) <= Lam - (t/2) log pi <= thetaS t,
            thetaS t = (t/4) log (1/16 + t^2/4) - (1/4) arctan (2t) - t/2 - (t/2) log pi.
      * `theta_sub_thetaMain`, `gaussBranch_theta_sub_thetaMain_le` : against the corpus main term
            `ZeroFreeBridge.thetaMain`, |Lam - (t/2) log pi - thetaMain t| <= 1/t for every t > 0 --
            the statement DESIGN_AND_ladder_1e9 section 3.3 proposed for `AND_theta_branch` (there with
            t >= 200 and the misspelled `ZetaReflection.imLnVal`; the island name is `ThetaGap.imLnVal`).
      * `theta_280000_box`   : the numeric instance at t = 280000 (reduced mod 2 pi, K = 216236),
                               an interval of width about 2e-6 around 2.2434215934
                               (mpmath siegeltheta(280000) - 2 pi K = 2.2434215934093).

    So the theta brick of the RS era costs O(1) transcendental evaluations per point at any height
    (two logs, one arctan, log pi shared), instead of O(t^(3/2)) arctan terms.  The general
    `lam_bracket` (any x > 0) also covers the Gamma_R edge quantities Im log Gamma(x + iT/2) at
    x = 1 (sigma = 2) and, after one shift Gamma(z) = Gamma(z+1)/z, at sigma = -1.

    Calibration (the probe, 2026-09-23): 646 lines, two compile iterations. `lake env lean` took about
    20 s wall, of which kernel type checking was 0.33 s and `norm_num` elaboration 4.7 s.

    conjecture1_proved = False.  A finite enclosure of one special-function value plus a
    height-uniform inequality; nothing here bears on the Riemann Hypothesis.
-/
import ThetaConverge
import DlvpTheta

open Real Filter Topology Set ThetaGap

namespace RSDesignTheta

/-! ## 1.  The convex trapezoid lemma. -/

/-- Secant bounds from a monotone derivative (Lagrange MVT): for `a <= u <= v <= b`,
    `(v - u) g u <= f v - f u <= (v - u) g v`. -/
theorem secant_bounds {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ u ∈ Icc a b, HasDerivAt f (g u) u) (hg : MonotoneOn g (Icc a b))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    (v - u) * g u ≤ f v - f u ∧ f v - f u ≤ (v - u) * g v := by
  rcases eq_or_lt_of_le huv with h | h
  · subst h; simp
  · have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hcont : ContinuousOn f (Icc u v) := fun w hw =>
      (hf w (hsub hw)).continuousAt.continuousWithinAt
    have hderiv : ∀ w ∈ Ioo u v, HasDerivAt f (g w) w := fun w hw =>
      hf w (hsub (Ioo_subset_Icc_self hw))
    obtain ⟨c, hc, hgc⟩ := exists_hasDerivAt_eq_slope f g h hcont hderiv
    have hcI : c ∈ Icc a b := hsub (Ioo_subset_Icc_self hc)
    have h1 : g u ≤ g c := hg hu hcI hc.1.le
    have h2 : g c ≤ g v := hg hcI hv hc.2.le
    have hpos : 0 < v - u := sub_pos.mpr h
    rw [hgc] at h1 h2
    have h1' := (le_div_iff₀ hpos).mp h1
    have h2' := (div_le_iff₀ hpos).mp h2
    constructor <;> nlinarith [h1', h2']

/-- **Convex trapezoid lemma.**  If `F' = f` and `f' = g` on `[a, a+1]` with `g` monotone there,
    the trapezoid value of `f` exceeds the integral `F (a+1) - F a` by a nonnegative amount at most
    `(g (a+1) - g a)/4`. -/
theorem trapezoid_convex {f F g : ℝ → ℝ} {a : ℝ}
    (hF : ∀ u ∈ Icc a (a + 1), HasDerivAt F (f u) u)
    (hf : ∀ u ∈ Icc a (a + 1), HasDerivAt f (g u) u)
    (hg : MonotoneOn g (Icc a (a + 1))) :
    0 ≤ (f a + f (a + 1)) / 2 - (F (a + 1) - F a) ∧
      (f a + f (a + 1)) / 2 - (F (a + 1) - F a) ≤ (g (a + 1) - g a) / 4 := by
  have hmem : ∀ h ∈ Icc (0:ℝ) 1, a + h ∈ Icc a (a + 1) := fun h hh =>
    ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have haI : a ∈ Icc a (a + 1) := ⟨le_refl a, by linarith⟩
  have ha1I : a + 1 ∈ Icc a (a + 1) := ⟨by linarith, le_refl _⟩
  -- derivative of the shifted functions
  have hfs : ∀ h ∈ Icc (0:ℝ) 1, HasDerivAt (fun h => f (a + h)) (g (a + h)) h := by
    intro h hh
    have h1 : HasDerivAt (fun h => a + h) 1 h := (hasDerivAt_id' h).const_add a
    exact ((hf (a + h) (hmem h hh)).comp h h1).congr_deriv (mul_one _)
  have hFs : ∀ h ∈ Icc (0:ℝ) 1, HasDerivAt (fun h => F (a + h)) (f (a + h)) h := by
    intro h hh
    have h1 : HasDerivAt (fun h => a + h) 1 h := (hasDerivAt_id' h).const_add a
    exact ((hF (a + h) (hmem h hh)).comp h h1).congr_deriv (mul_one _)
  -- φ(h) = h (f a + f (a+h))/2 - (F (a+h) - F a)
  set φ : ℝ → ℝ := fun h => h * (f a + f (a + h)) / 2 - (F (a + h) - F a) with hφdef
  have hφd : ∀ h ∈ Icc (0:ℝ) 1,
      HasDerivAt φ ((f a - f (a + h)) / 2 + h * g (a + h) / 2) h := by
    intro h hh
    have hA : HasDerivAt (fun h => h * (f a + f (a + h)))
        (1 * (f a + f (a + h)) + h * g (a + h)) h :=
      (hasDerivAt_id' h).mul ((hfs h hh).const_add (f a))
    have hB := (hA.div_const 2).sub ((hFs h hh).sub_const (F a))
    exact hB.congr_deriv (by ring)
  -- secant facts at (a, a+h)
  have hsec : ∀ h ∈ Icc (0:ℝ) 1,
      h * g a ≤ f (a + h) - f a ∧ f (a + h) - f a ≤ h * g (a + h) := by
    intro h hh
    have := secant_bounds hf hg haI (hmem h hh) (by linarith [hh.1])
    simpa using this
  -- monotonicity of φ on [0,1]
  have hφmono : MonotoneOn φ (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · exact fun h hh => (hφd h hh).continuousAt.continuousWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      exact (hφd h (Ioo_subset_Icc_self hh)).hasDerivWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      have := (hsec h (Ioo_subset_Icc_self hh)).2
      linarith
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  have hφ1 : φ 1 = (f a + f (a + 1)) / 2 - (F (a + 1) - F a) := by simp [hφdef]
  have hlow : φ 0 ≤ φ 1 :=
    hφmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  -- ψ(h) = h^2 (g (a+1) - g a)/4 - φ h
  set D : ℝ := g (a + 1) - g a with hD
  set ψ : ℝ → ℝ := fun h => h ^ 2 * D / 4 - φ h with hψdef
  have hψd : ∀ h ∈ Icc (0:ℝ) 1,
      HasDerivAt ψ (2 * h * D / 4 - ((f a - f (a + h)) / 2 + h * g (a + h) / 2)) h := by
    intro h hh
    have hA : HasDerivAt (fun h : ℝ => h ^ 2 * D / 4) (2 * h * D / 4) h := by
      have := ((hasDerivAt_pow 2 h).mul_const D).div_const 4
      exact this.congr_deriv (by push_cast; ring)
    exact hA.sub (hφd h hh)
  have hψmono : MonotoneOn ψ (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · exact fun h hh => (hψd h hh).continuousAt.continuousWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      exact (hψd h (Ioo_subset_Icc_self hh)).hasDerivWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      have hhI : h ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hh
      have hs1 := (hsec h hhI).1
      have hgmono : g (a + h) ≤ g (a + 1) := hg (hmem h hhI) ha1I (by linarith [hh.2])
      have hprod : 0 ≤ h * (g (a + 1) - g (a + h)) :=
        mul_nonneg hh.1.le (by linarith)
      rw [hD]
      nlinarith [hs1, hprod]
  have hψ0 : ψ 0 = 0 := by simp [hψdef, hφ0]
  have hup : ψ 0 ≤ ψ 1 :=
    hψmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have hψ1 : ψ 1 = D / 4 - φ 1 := by simp [hψdef]
  constructor
  · rw [← hφ1]; linarith
  · rw [← hφ1]; linarith

/-! ## 2.  The θ-series summand, its antiderivative and derivative. -/

/-- The summand `u ↦ arctan (y/(x+u))` of `imLnVal x y`. -/
noncomputable def fA (x y u : ℝ) : ℝ := Real.arctan (y / (x + u))

/-- Its antiderivative: `(x+u) arctan (y/(x+u)) + (y/2) log ((x+u)^2 + y^2)`. -/
noncomputable def FA (x y u : ℝ) : ℝ :=
  (x + u) * Real.arctan (y / (x + u)) + y / 2 * Real.log ((x + u) ^ 2 + y ^ 2)

/-- Its derivative: `-(y/((x+u)^2 + y^2))`. -/
noncomputable def gA (x y u : ℝ) : ℝ := -(y / ((x + u) ^ 2 + y ^ 2))

theorem hasDerivAt_fA (x y u : ℝ) (hxu : 0 < x + u) :
    HasDerivAt (fA x y) (gA x y u) u := by
  have hne : x + u ≠ 0 := hxu.ne'
  have hd : HasDerivAt (fun u => x + u) 1 u := (hasDerivAt_id' u).const_add x
  have hq : HasDerivAt (fun u => y / (x + u)) ((0 * (x + u) - y * 1) / (x + u) ^ 2) u :=
    (hasDerivAt_const u y).div hd hne
  have h := hq.arctan
  unfold fA gA
  refine h.congr_deriv ?_
  have hpos : 0 < (x + u) ^ 2 + y ^ 2 := by positivity
  field_simp
  ring

theorem hasDerivAt_FA (x y u : ℝ) (hxu : 0 < x + u) :
    HasDerivAt (FA x y) (fA x y u) u := by
  have hne : x + u ≠ 0 := hxu.ne'
  have hpos : 0 < (x + u) ^ 2 + y ^ 2 := by positivity
  have hd : HasDerivAt (fun u => x + u) 1 u := (hasDerivAt_id' u).const_add x
  have h1 : HasDerivAt (fun u => (x + u) * Real.arctan (y / (x + u)))
      (1 * Real.arctan (y / (x + u)) + (x + u) * gA x y u) u :=
    hd.mul (hasDerivAt_fA x y u hxu)
  have hsq : HasDerivAt (fun u => (x + u) ^ 2 + y ^ 2) (2 * (x + u)) u := by
    have := (hd.pow 2).add_const (y ^ 2)
    exact this.congr_deriv (by push_cast; ring)
  have h2 : HasDerivAt (fun u => y / 2 * Real.log ((x + u) ^ 2 + y ^ 2))
      (y / 2 * (2 * (x + u) / ((x + u) ^ 2 + y ^ 2))) u :=
    (hsq.log hpos.ne').const_mul (y / 2)
  have h := h1.add h2
  unfold FA fA
  refine h.congr_deriv ?_
  unfold gA
  field_simp
  ring

theorem gA_monotoneOn (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) : MonotoneOn (gA x y) (Ici 0) := by
  intro u hu v hv huv
  simp only [mem_Ici] at hu hv
  unfold gA
  have hu' : 0 < x + u := by linarith
  have hsq : (x + u) ^ 2 + y ^ 2 ≤ (x + v) ^ 2 + y ^ 2 := by nlinarith
  have hpu : 0 < (x + u) ^ 2 + y ^ 2 := by positivity
  have := div_le_div_of_nonneg_left hy hpu hsq
  linarith

theorem gA_nonpos (x y u : ℝ) (hy : 0 ≤ y) : gA x y u ≤ 0 := by
  unfold gA
  have : 0 ≤ y / ((x + u) ^ 2 + y ^ 2) := by positivity
  linarith

/-! ## 3.  The finite sandwich of `imLnVal`. -/

/-- The trapezoid excess on `[k, k+1]`. -/
noncomputable def eA (x y : ℝ) (k : ℕ) : ℝ :=
  (fA x y k + fA x y ((k:ℝ) + 1)) / 2 - (FA x y ((k:ℝ) + 1) - FA x y k)

theorem eA_bounds (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (k : ℕ) :
    0 ≤ eA x y k ∧ eA x y k ≤ (gA x y ((k:ℝ) + 1) - gA x y k) / 4 := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hsub : Icc (k:ℝ) ((k:ℝ) + 1) ⊆ Ici 0 := fun u hu => le_trans hk hu.1
  have hF : ∀ u ∈ Icc (k:ℝ) ((k:ℝ) + 1), HasDerivAt (FA x y) (fA x y u) u := fun u hu =>
    hasDerivAt_FA x y u (by linarith [hu.1])
  have hf : ∀ u ∈ Icc (k:ℝ) ((k:ℝ) + 1), HasDerivAt (fA x y) (gA x y u) u := fun u hu =>
    hasDerivAt_fA x y u (by linarith [hu.1])
  have hg : MonotoneOn (gA x y) (Icc (k:ℝ) ((k:ℝ) + 1)) :=
    (gA_monotoneOn x y hx hy).mono hsub
  exact trapezoid_convex hF hf hg

/-- The telescoped split of the finite arctan sum at a base index `n0`. -/
theorem sum_split (x y : ℝ) (n0 : ℕ) :
    ∀ n, n0 ≤ n →
      ∑ k ∈ Finset.range (n + 1), fA x y k
        = (∑ k ∈ Finset.range (n0 + 1), fA x y k) - fA x y n0 / 2 + fA x y n / 2
          + (FA x y n - FA x y n0) + ∑ k ∈ Finset.Ico n0 n, eA x y k := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top hmn]
    unfold eA
    push_cast
    ring

theorem sumE_bounds (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (n0 n : ℕ) (hn : n0 ≤ n) :
    0 ≤ ∑ k ∈ Finset.Ico n0 n, eA x y k ∧
      ∑ k ∈ Finset.Ico n0 n, eA x y k ≤ (gA x y n - gA x y n0) / 4 := by
  constructor
  · exact Finset.sum_nonneg fun k _ => (eA_bounds x y hx hy k).1
  · have hle : ∑ k ∈ Finset.Ico n0 n, eA x y k
        ≤ ∑ k ∈ Finset.Ico n0 n, (gA x y (((k + 1 : ℕ) : ℝ)) - gA x y k) / 4 := by
      apply Finset.sum_le_sum
      intro k _
      have := (eA_bounds x y hx hy k).2
      push_cast
      exact this
    have htel : ∑ k ∈ Finset.Ico n0 n, (gA x y (((k + 1 : ℕ) : ℝ)) - gA x y k) / 4
        = (gA x y n - gA x y n0) / 4 := by
      rw [← Finset.sum_div]
      rw [Finset.sum_Ico_sub (fun k : ℕ => gA x y (k:ℝ)) hn]
    linarith

/-- **Finite sandwich.**  For `n >= n0`, with `H n = y log n - FA n - fA n / 2` and the constant
    `C0 = FA n0 + fA n0 / 2 - sum_{k <= n0} fA k`:
        H n + C0 + gA n0 / 4 <= imLnVal x y n <= H n + C0. -/
theorem imLnVal_sandwich (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (n0 n : ℕ) (hn : n0 ≤ n) :
    (y * Real.log n - FA x y n - fA x y n / 2)
        + (FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k)
        + gA x y n0 / 4 ≤ imLnVal x y n ∧
      imLnVal x y n ≤ (y * Real.log n - FA x y n - fA x y n / 2)
        + (FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k) := by
  have hsum := sum_split x y n0 n hn
  have hE := sumE_bounds x y hx hy n0 n hn
  have hgn := gA_nonpos x y (n:ℝ) hy
  have himl : imLnVal x y n = y * Real.log n - ∑ k ∈ Finset.range (n + 1), fA x y k := rfl
  rw [himl, hsum]
  constructor <;> linarith [hE.1, hE.2]

/-! ## 4.  The limit of `H n` and the Stirling bracket for `Lam`. -/

theorem tendsto_H (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    Tendsto (fun n : ℕ => y * Real.log n - FA x y n - fA x y n / 2) atTop (𝓝 (-y)) := by
  -- (a) the log part
  have hx0 : Tendsto (fun n : ℕ => x / (n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat x
  have hy0 : Tendsto (fun n : ℕ => y / (n:ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat y
  have hq : Tendsto (fun n : ℕ => (1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2) atTop
      (𝓝 ((1 + 0) ^ 2 + 0 ^ 2)) :=
    ((hx0.const_add 1).pow 2).add (hy0.pow 2)
  have hq1 : ((1:ℝ) + 0) ^ 2 + 0 ^ 2 = 1 := by norm_num
  rw [hq1] at hq
  have hlogq : Tendsto (fun n : ℕ => Real.log ((1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2)) atTop
      (𝓝 (Real.log 1)) :=
    ((Real.continuousAt_log (by norm_num)).tendsto).comp hq
  rw [Real.log_one] at hlogq
  have hA : Tendsto (fun n : ℕ => y * Real.log n - y / 2 * Real.log ((x + n) ^ 2 + y ^ 2))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => -(y / 2) * Real.log ((1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2))
        atTop (𝓝 (-(y / 2) * 0)) := hlogq.const_mul _
    rw [mul_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hfac : (x + n) ^ 2 + y ^ 2 = (n:ℝ) ^ 2 * ((1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2) := by
      field_simp
      ring
    have hqpos : 0 < (1 + x / (n:ℝ)) ^ 2 + (y / (n:ℝ)) ^ 2 := by
      have : 0 < 1 + x / (n:ℝ) := by positivity
      positivity
    rw [hfac, Real.log_mul (by positivity) hqpos.ne', Real.log_pow]
    push_cast
    ring
  -- (b) the arctan argument tends to 0
  have hden : Tendsto (fun n : ℕ => x + (n:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  have hu0 : Tendsto (fun n : ℕ => y / (x + (n:ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hC : Tendsto (fun n : ℕ => fA x y n) atTop (𝓝 0) := by
    have := ((Real.continuous_arctan.tendsto 0).comp hu0)
    rw [Real.arctan_zero] at this
    exact this
  -- (c) (x+n) arctan (y/(x+n)) -> y by squeezing
  have hB : Tendsto (fun n : ℕ => (x + n) * Real.arctan (y / (x + n))) atTop (𝓝 y) := by
    have hlow : Tendsto (fun n : ℕ => y - (y ^ 3 / 3) / (n:ℝ)) atTop (𝓝 (y - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [sub_zero] at hlow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hxn : 0 < x + n := by linarith
      set u : ℝ := y / (x + n) with hu
      have hu0' : 0 ≤ u := by positivity
      have hcube := ArctanTaylor.self_sub_cube_le_arctan hu0'
      have hxu : (x + n) * u = y := by rw [hu]; field_simp
      have hmul : (x + n) * (u - u ^ 3 / 3) ≤ (x + n) * Real.arctan u :=
        mul_le_mul_of_nonneg_left hcube hxn.le
      have hid : (x + n) * (u - u ^ 3 / 3) = y - y ^ 3 / (3 * (x + n) ^ 2) := by
        rw [hu]; field_simp
      have hsmall : y ^ 3 / (3 * (x + n) ^ 2) ≤ (y ^ 3 / 3) / (n:ℝ) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hxn : 0 < x + n := by linarith
      set u : ℝ := y / (x + n) with hu
      have hu0' : 0 ≤ u := by positivity
      have hle := ArctanTaylor.arctan_le_self hu0'
      have hxu : (x + n) * u = y := by rw [hu]; field_simp
      have := mul_le_mul_of_nonneg_left hle hxn.le
      linarith
  -- assemble: H = A - B - C/2
  have hsum : Tendsto (fun n : ℕ => (y * Real.log n - y / 2 * Real.log ((x + n) ^ 2 + y ^ 2))
      - (x + n) * Real.arctan (y / (x + n)) - fA x y n / 2) atTop (𝓝 (0 - y - 0 / 2)) :=
    (hA.sub hB).sub (hC.div_const 2)
  have hval : (0:ℝ) - y - 0 / 2 = -y := by ring
  rw [hval] at hsum
  refine hsum.congr' (Eventually.of_forall fun n => ?_)
  unfold FA
  ring

/-- **Stirling bracket for the Gauss-product branch (height-uniform).**  For `x > 0`, `y >= 0`, any
    base index `n0`, and `Lam` the limit of `imLnVal x y`:
        C - y/(4((x+n0)^2 + y^2)) <= Lam <= C,
    where `C = FA n0 + fA n0 / 2 - sum_{k <= n0} fA k - y` is elementary (logs and arctans). -/
theorem lam_bracket (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (n0 : ℕ) (Λ : ℝ)
    (hΛ : Tendsto (imLnVal x y) atTop (𝓝 Λ)) :
    (FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k - y)
        - y / (4 * ((x + n0) ^ 2 + y ^ 2)) ≤ Λ ∧
      Λ ≤ FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k - y := by
  set C0 : ℝ := FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k with hC0
  have hH := tendsto_H x y hx hy
  have hup : Tendsto (fun n : ℕ => (y * Real.log n - FA x y n - fA x y n / 2) + C0) atTop
      (𝓝 (-y + C0)) := hH.add_const C0
  have hlo : Tendsto (fun n : ℕ => (y * Real.log n - FA x y n - fA x y n / 2) + C0
      + gA x y n0 / 4) atTop (𝓝 (-y + C0 + gA x y n0 / 4)) := hup.add_const _
  have hgA : gA x y n0 / 4 = -(y / (4 * ((x + n0) ^ 2 + y ^ 2))) := by
    unfold gA
    have : 0 < (x + (n0:ℝ)) ^ 2 + y ^ 2 := by
      have : 0 < x + (n0:ℝ) := by positivity
      positivity
    field_simp
  constructor
  · have h := le_of_tendsto_of_tendsto hlo hΛ (by
      filter_upwards [eventually_ge_atTop n0] with n hn
      exact (imLnVal_sandwich x y hx hy n0 n hn).1)
    rw [hgA] at h
    linarith
  · have h := le_of_tendsto_of_tendsto hΛ hup (by
      filter_upwards [eventually_ge_atTop n0] with n hn
      exact (imLnVal_sandwich x y hx hy n0 n hn).2)
    linarith

/-! ## 5.  The Riemann-Siegel phase: the `n0 = 0`, `x = 1/4`, `y = t/2` specialisation. -/

/-- The closed-form Stirling value of the RS phase: `(t/4) log (1/16 + t^2/4) - (1/4) arctan (2t)
    - t/2 - (t/2) log pi`.  (Equal to `thetaMain t + 3/(16 t) + O(t^-3)`; the true phase lies in
    `[thetaS t - 1/(2t), thetaS t]`, and numerically sits at `thetaS t - 1/(6t)`.) -/
noncomputable def thetaS (t : ℝ) : ℝ :=
  t / 4 * Real.log (1 / 16 + t ^ 2 / 4) - 1 / 4 * Real.arctan (2 * t) - t / 2
    - t / 2 * Real.log Real.pi

/-- **The height-uniform θ bracket.**  For every `t > 0` and `Lam = lim imLnVal (1/4) (t/2)` (the
    branch `ZeroSignDecomp.gLine_sign_decomp_t` exposes),
        thetaS t - 1/(2t) <= Lam - (t/2) log pi <= thetaS t. -/
theorem theta_bracket (t : ℝ) (ht : 0 < t) (Λ : ℝ)
    (hΛ : Tendsto (imLnVal (1/4) (t/2)) atTop (𝓝 Λ)) :
    thetaS t - 1 / (2 * t) ≤ Λ - t / 2 * Real.log Real.pi ∧
      Λ - t / 2 * Real.log Real.pi ≤ thetaS t := by
  have hb := lam_bracket (1/4) (t/2) (by norm_num) (by positivity) 0 Λ hΛ
  have hC : FA (1/4) (t/2) ((0:ℕ):ℝ) + fA (1/4) (t/2) ((0:ℕ):ℝ) / 2
      - ∑ k ∈ Finset.range (0 + 1), fA (1/4) (t/2) (k:ℝ) - t / 2
      = t / 4 * Real.log (1 / 16 + t ^ 2 / 4) - 1 / 4 * Real.arctan (2 * t) - t / 2 := by
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero]
    unfold FA fA
    have h1 : t / 2 / (1 / 4 + 0) = 2 * t := by ring
    have h2 : ((1:ℝ) / 4 + 0) ^ 2 + (t / 2) ^ 2 = 1 / 16 + t ^ 2 / 4 := by ring
    rw [h1, h2]
    ring
  have hB : t / 2 / (4 * ((1 / 4 + ((0:ℕ):ℝ)) ^ 2 + (t / 2) ^ 2)) ≤ 1 / (2 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  rw [hC] at hb
  unfold thetaS
  constructor <;> linarith [hb.1, hb.2]

/-- **`AND_theta_branch` companion form (the 1e9 design memo's proposed statement, section 3.3).**
    Against the corpus main term `ZeroFreeBridge.thetaMain t = (t/2) log t - (t/2) log (2 pi) - t/2 - pi/8`:
        |Lam - (t/2) log pi - thetaMain t| <= 1/t      for every t > 0
    (in fact the difference lies in `[-1/(2t), 3/(16t)]`).  The memo asked for `t >= 200`; the
    trapezoid route gives it at every positive height. -/
theorem theta_sub_thetaMain (t : ℝ) (ht : 0 < t) (Λ : ℝ)
    (hΛ : Tendsto (imLnVal (1/4) (t/2)) atTop (𝓝 Λ)) :
    |Λ - t / 2 * Real.log Real.pi - ZeroFreeBridge.thetaMain t| ≤ 1 / t := by
  have hb := theta_bracket t ht Λ hΛ
  unfold thetaS at hb
  unfold ZeroFreeBridge.thetaMain
  set v : ℝ := 1 / (4 * t ^ 2) with hv
  have hv0 : 0 ≤ v := by positivity
  have hlog : Real.log (1 / 16 + t ^ 2 / 4)
      = 2 * Real.log t - 2 * Real.log 2 + Real.log (1 + v) := by
    have h1 : (1 / 16 + t ^ 2 / 4 : ℝ) = (t ^ 2 / 2 ^ 2) * (1 + v) := by
      rw [hv]; field_simp; ring
    rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have harc : Real.arctan (2 * t) = Real.pi / 2 - Real.arctan (1 / (2 * t)) := by
    have h := Real.arctan_inv_of_pos (by positivity : (0:ℝ) < 2 * t)
    rw [inv_eq_one_div] at h
    linarith
  have hL0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hL1 : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos (x := 1 + v) (by linarith)
    linarith
  have hA0 : 0 ≤ Real.arctan (1 / (2 * t)) := by
    have : (0:ℝ) ≤ 1 / (2 * t) := by positivity
    exact Real.arctan_nonneg.mpr this
  have hA1 : Real.arctan (1 / (2 * t)) ≤ 1 / (2 * t) :=
    ArctanTaylor.arctan_le_self (by positivity)
  have hP0 : 0 ≤ t / 4 * Real.log (1 + v) := by positivity
  have hP1 : t / 4 * Real.log (1 + v) ≤ 1 / (16 * t) := by
    have h := mul_le_mul_of_nonneg_left hL1 (by positivity : (0:ℝ) ≤ t / 4)
    have he : t / 4 * v = 1 / (16 * t) := by rw [hv]; field_simp; ring
    linarith
  have hq1 : 1 / (2 * t) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht]; linarith
  have hq2 : 1 / (16 * t) + 1 / 4 * (1 / (2 * t)) ≤ 1 / t := by
    have e : 1 / (16 * t) + 1 / 4 * (1 / (2 * t)) = (3 / 16) * (1 / t) := by field_simp; ring
    have : 0 ≤ 1 / t := by positivity
    rw [e]; linarith
  rw [hlog, harc] at hb
  rw [hlog2pi, abs_le]
  constructor <;> nlinarith [hb.1, hb.2, hP0, hP1, hA0, hA1, hq1, hq2]

/-- **The exact existential shape proposed for `AND_theta_branch`** (DESIGN_AND_ladder_1e9 section 3.3,
    `gaussBranch_theta_sub_thetaMain_le`), with the memo's `t >= 200` weakened to `t > 0` and the
    memo's `ZetaReflection.imLnVal` corrected to the island's actual name `ThetaGap.imLnVal`.
    The statement spells every name in full, so its text is the registry statement verbatim
    (ANDURIL_ARB_DISCHARGE_2026-09-23 op O-4). -/
theorem gaussBranch_theta_sub_thetaMain_le {t : ℝ} (ht : 0 < t) :
    ∃ Λ : ℝ, Filter.Tendsto (ThetaGap.imLnVal (1/4) (t/2)) Filter.atTop (nhds Λ) ∧
      |Λ - t / 2 * Real.log Real.pi - ZeroFreeBridge.thetaMain t| ≤ 1 / t := by
  have hG : Complex.Gamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ) * Complex.I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    linarith
  obtain ⟨Λ, hΛ, _⟩ := ThetaConverge.convergence_obligation (1/4) (t/2) (by norm_num) hG
  exact ⟨Λ, hΛ, theta_sub_thetaMain t ht Λ hΛ⟩

/-! ## 6.  The numeric instance at `t = 280000` (the top of the h280000 ladder).

All constants below are short decimals chosen by an untrusted script; every inequality between
them and the exact series values is re-checked by `norm_num`/`linarith` in the kernel.  The log
brackets use Mathlib's `Real.abs_log_sub_add_sum_range_le` (Taylor series of `log (1 - x)` with the
geometric remainder `|x|^(n+1)/(1-|x|)`), the pi bracket is Mathlib's `pi_gt_d20`/`pi_lt_d20`. -/

/-- `log 2` to about `7e-15` (48 terms of the `x = 1/2` series). -/
theorem log2_box :
    (3465735902799708427977/5000000000000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599487910229/10000000000000000000000 := by
  have hx : |(1/2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 48
  have hl : Real.log (1 - 1/2 : ℝ) = -Real.log 2 := by
    rw [show (1:ℝ) - 1/2 = 2⁻¹ by norm_num, Real.log_inv]
  have habs : |(1/2 : ℝ)| = 1/2 := abs_of_pos (by norm_num)
  rw [hl, habs, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log (1 - x)` for `x = 38722093057/313600000001` (so `1 - x = 2^38/313600000001`), 16 terms. -/
theorem log1mxv_box :
    (-658956320739656718961/5000000000000000000000 : ℝ)
        ≤ Real.log (1 - 38722093057/313600000001) ∧
      Real.log (1 - 38722093057/313600000001)
        ≤ -1317912641479305212213/10000000000000000000000 := by
  have hx : |(38722093057/313600000001 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 16
  have habs : |(38722093057/313600000001 : ℝ)| = 38722093057/313600000001 :=
    abs_of_pos (by norm_num)
  rw [habs, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log (1/16 + 280000^2/4) = log (313600000001/16)` to about `2.4e-13`. -/
theorem logv_box :
    (236987954031859478314649/10000000000000000000000 : ℝ) ≤ Real.log (313600000001/16) ∧
      Real.log (313600000001/16) ≤ 59246988507965475596427/2500000000000000000000 := by
  have hsplit : Real.log (313600000001/16 : ℝ)
      = 34 * Real.log 2 - Real.log (1 - 38722093057/313600000001) := by
    have h1 : (313600000001/16 : ℝ) = 2 ^ 34 / (1 - 38722093057/313600000001) := by norm_num
    rw [h1, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  obtain ⟨h2l, h2h⟩ := log2_box
  obtain ⟨hcl, hch⟩ := log1mxv_box
  rw [hsplit]
  constructor <;> linarith

/-- `log (1 - xL)` for `xL = 2146018366026/10^13` (so `4(1 - xL) = 3.1415926535896 < pi`), lower end. -/
theorem log1mxL_lo :
    (-2415644752705520655341/10000000000000000000000 : ℝ)
        ≤ Real.log (1 - 2146018366026/10000000000000) := by
  have hx : |(2146018366026/10000000000000 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 23
  have habs : |(2146018366026/10000000000000 : ℝ)| = 2146018366026/10000000000000 :=
    abs_of_pos (by norm_num)
  rw [habs, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log (1 - xH)` for `xH = 2146018366025/10^13` (so `4(1 - xH) = 3.14159265359 > pi`), upper end. -/
theorem log1mxH_hi :
    Real.log (1 - 2146018366025/10000000000000)
        ≤ -60391118817606127441/250000000000000000000 := by
  have hx : |(2146018366025/10000000000000 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 23
  have habs : |(2146018366025/10000000000000 : ℝ)| = 2146018366025/10000000000000 :=
    abs_of_pos (by norm_num)
  rw [habs, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.1, h.2]

/-- `log pi` to about `1.4e-13`, from the Mathlib `d20` pi bracket and the two series above. -/
theorem logpi_box :
    (11447298858493313056567/10000000000000000000000 : ℝ) ≤ Real.log Real.pi ∧
      Real.log Real.pi ≤ 5723649429247365361409/5000000000000000000000 := by
  have hpl := Real.pi_gt_d20
  have hph := Real.pi_lt_d20
  have hpL : (4 * (1 - 2146018366026/10000000000000) : ℝ) ≤ Real.pi := by norm_num at hpl ⊢; linarith
  have hpH : Real.pi ≤ (4 * (1 - 2146018366025/10000000000000) : ℝ) := by norm_num at hph ⊢; linarith
  have hlogL := Real.log_le_log (by norm_num) hpL
  have hlogH := Real.log_le_log Real.pi_pos hpH
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [Real.log_mul (by norm_num) (by norm_num), h4] at hlogL hlogH
  obtain ⟨h2l, h2h⟩ := log2_box
  have hL := log1mxL_lo
  have hH := log1mxH_hi
  constructor <;> linarith

/-- `arctan 560000 = pi/2 - arctan (1/560000)`, boxed by the cubic arctan bracket. -/
theorem arctan560000_box :
    Real.pi / 2 - 1/560000 ≤ Real.arctan 560000 ∧
      Real.arctan 560000 ≤ Real.pi / 2 - 1/560000 + (1/560000) ^ 3 / 3 := by
  have hinv := Real.arctan_inv_of_pos (x := (560000:ℝ)) (by norm_num)
  have hu : (0:ℝ) ≤ 1/560000 := by norm_num
  have h1 := ArctanTaylor.arctan_le_self hu
  have h2 := ArctanTaylor.self_sub_cube_le_arctan hu
  rw [show (560000:ℝ)⁻¹ = 1/560000 by norm_num] at hinv
  constructor <;> linarith

/-- **The RS phase at `t = 280000`, reduced mod `2 pi` (`K = 216236`).**  For the branch limit
    `Lam = lim imLnVal (1/4) 140000` (supplied by `ThetaConverge.convergence_obligation`, and the
    one `ZeroSignDecomp.gLine_sign_decomp_t 280000` exposes):
        2.243420384072 <= Lam - 140000 log pi - 2 pi * 216236 <= 2.243422206603
    (width 1.8e-6; mpmath `siegeltheta(280000) - 2 pi K = 2.2434215934093`). -/
theorem theta_280000_box (Λ : ℝ) (hΛ : Tendsto (imLnVal (1/4) (280000/2)) atTop (𝓝 Λ)) :
    (280427548009/125000000000 : ℝ)
        ≤ Λ - 280000 / 2 * Real.log Real.pi - 2 * Real.pi * 216236 ∧
      Λ - 280000 / 2 * Real.log Real.pi - 2 * Real.pi * 216236 ≤ 2243422206603/1000000000000 := by
  have hb := theta_bracket 280000 (by norm_num) Λ hΛ
  unfold thetaS at hb
  have hv : (1/16 + (280000:ℝ) ^ 2 / 4) = 313600000001/16 := by norm_num
  have h2t : (2 * (280000:ℝ)) = 560000 := by norm_num
  rw [hv, h2t] at hb
  obtain ⟨hvl, hvh⟩ := logv_box
  obtain ⟨hpl2, hph2⟩ := logpi_box
  obtain ⟨hal, hah⟩ := arctan560000_box
  have hpl := Real.pi_gt_d20
  have hph := Real.pi_lt_d20
  constructor <;> linarith [hb.1, hb.2]

/-- The phase box is not vacuous: the branch limit exists (hypothesis-free). -/
theorem theta_280000_exists :
    ∃ Λ : ℝ, Tendsto (imLnVal (1/4) (280000/2)) atTop (𝓝 Λ) ∧
      (280427548009/125000000000 : ℝ)
          ≤ Λ - 280000 / 2 * Real.log Real.pi - 2 * Real.pi * 216236 ∧
        Λ - 280000 / 2 * Real.log Real.pi - 2 * Real.pi * 216236 ≤ 2243422206603/1000000000000 := by
  have hG : Complex.Gamma (((1/4:ℝ):ℂ) + ((280000/2:ℝ):ℂ) * Complex.I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
  obtain ⟨Λ, hΛ, _⟩ := ThetaConverge.convergence_obligation (1/4) (280000/2) (by norm_num) hG
  exact ⟨Λ, hΛ, theta_280000_box Λ hΛ⟩

end RSDesignTheta
