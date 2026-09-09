/- TURING RUNG T2, brick 1: the Riemann–Siegel theta function, defined BRANCH-CUT-FREE as the
   integral of an explicit real integrand (TURING_METHOD_SCOPING §3, rung T2).

   Classically `θ(t) = Im logΓ(1/4 + it/2) − (t/2)·log π` with a continuously-tracked branch of
   `logΓ` — awkward to formalize.  Instead we DEFINE

     `θ(t) := ∫_0^t ( (1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π ) du`,

   where `ψ = Complex.digamma = logDeriv Γ` (Mathlib).  This agrees with the classical `θ`
   (both vanish at `0` and have the same derivative `θ'(u) = (1/2)·Re ψ(1/4 + iu/2) − (1/2)·log π`)
   and needs NO branch tracking: the integrand is a plain continuous real function of `u`.

   This brick: the ray `1/4 + (u/2)·i` avoids all Γ-poles (`Re = 1/4 > 0`), Γ is ANALYTIC there
   (differentiable on the open right half-plane ⟹ analytic), `ψ` is continuous on the ray
   (`deriv Γ / Γ`, with `Γ ≠ 0` by `Gamma_ne_zero_of_re_pos`), hence the integrand is continuous,
   `θ` is well-defined with `θ(0) = 0` and `θ' = integrand` (FTC for continuous integrands).

   Later bricks (T2 cont.): effective two-sided bounds `θ(t) = (t/2)log(t/2π) − t/2 − π/8 +
   O*(explicit/t)` via Binet-type digamma estimates; then T3 wires `θ` into the rectangle
   argument identity `N(T) = θ(T)/π + 1 + S(T)`.

   conjecture1_proved = False. -/
import Mathlib

open Complex

namespace ZeroFreeBridge

/-- The digamma ray for the Riemann–Siegel theta: `u ↦ 1/4 + (u/2)·i`. -/
noncomputable def thetaRay (u : ℝ) : ℂ := 1 / 4 + ((u / 2 : ℝ) : ℂ) * I

theorem thetaRay_re (u : ℝ) : (thetaRay u).re = 1 / 4 := by
  simp only [thetaRay, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

theorem thetaRay_continuous : Continuous thetaRay := by
  have h1 : Continuous fun u : ℝ => ((u / 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_id.div_const 2)
  exact continuous_const.add (h1.mul continuous_const)

/-- `Γ` is analytic at every ray point (the ray lies in the open right half-plane, where `Γ` is
    differentiable, hence analytic). -/
theorem gamma_analyticAt_thetaRay (u : ℝ) : AnalyticAt ℂ Gamma (thetaRay u) := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Gamma {s : ℂ | 0 < s.re} := by
    intro s hs
    refine (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    rw [hm] at hs
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  exact (hdiff.analyticOnNhd hopen) (thetaRay u)
    (by simp only [Set.mem_setOf_eq, thetaRay_re]; norm_num)

/-- `ψ = digamma` is continuous at every ray point (`deriv Γ / Γ`, `Γ ≠ 0` on `Re > 0`, and
    `deriv Γ` is continuous since `Γ` is analytic). -/
theorem digamma_continuousAt_thetaRay (u : ℝ) :
    ContinuousAt Complex.digamma (thetaRay u) := by
  have hana := gamma_analyticAt_thetaRay u
  have hne : Gamma (thetaRay u) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [thetaRay_re]; norm_num)
  have heq : Complex.digamma = fun s => deriv Gamma s / Gamma s := by
    funext s; rw [Complex.digamma_def, logDeriv_apply]
  rw [heq]
  exact (hana.deriv.continuousAt).div hana.continuousAt hne

/-- The θ integrand: `u ↦ (1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π`. -/
noncomputable def thetaIntegrand (u : ℝ) : ℝ :=
  (1 / 2) * (Complex.digamma (thetaRay u)).re - (1 / 2) * Real.log Real.pi

theorem thetaIntegrand_continuous : Continuous thetaIntegrand := by
  have hcomp : Continuous fun u : ℝ => (Complex.digamma (thetaRay u)).re := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (Complex.continuous_re.continuousAt).comp
      ((digamma_continuousAt_thetaRay u).comp thetaRay_continuous.continuousAt)
  exact (continuous_const.mul hcomp).sub continuous_const

/-- **The Riemann–Siegel theta function**, branch-cut-free:
    `θ(t) := ∫_0^t ((1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π) du`. -/
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, thetaIntegrand u

theorem riemannSiegelTheta_zero : riemannSiegelTheta 0 = 0 :=
  intervalIntegral.integral_same

theorem thetaIntegrand_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable thetaIntegrand MeasureTheory.volume a b :=
  thetaIntegrand_continuous.intervalIntegrable a b

/-- FTC: `θ'(t) = (1/2)·Re ψ(1/4 + i·t/2) − (1/2)·log π` (the integrand is continuous). -/
theorem riemannSiegelTheta_deriv (t : ℝ) :
    deriv riemannSiegelTheta t = thetaIntegrand t :=
  Continuous.deriv_integral thetaIntegrand thetaIntegrand_continuous 0 t

/-! ## Brick 2: the Archimedean bridge — `θ'` IS the `Gammaℝ` log-derivative on the critical line.

`Gammaℝ s = π^(-s/2)·Γ(s/2)` is the Archimedean factor of the completed zeta
(`Λ = Gammaℝ · ζ` up to the `s(s-1)` polynomial), the object the T3 rectangle identity
splits off of `logDeriv Λ`.  We compute `logDeriv Gammaℝ s = -(log π)/2 + (1/2)·ψ(s/2)`
on `Re(s/2) > 0` and specialize to the critical line `s = 1/2 + iu`, where `s/2 = thetaRay u`:
the θ integrand is EXACTLY `Re (logDeriv Gammaℝ (1/2 + iu))`.  This hard-wires the
branch-cut-free `θ` into the counting formula's Archimedean term. -/

/-- The π-power factor of `Gammaℝ`. -/
noncomputable def gammaRArch (z : ℂ) : ℂ := (Real.pi : ℂ) ^ (-z / 2)

theorem gammaRArch_exp :
    gammaRArch = fun z => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) :=
  funext fun z => Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) _

theorem gammaRArch_hasDerivAt (s : ℂ) :
    HasDerivAt gammaRArch
      (Complex.exp (Complex.log (Real.pi : ℂ) * (-s / 2))
        * (Complex.log (Real.pi : ℂ) * (-(1 / 2)))) s := by
  rw [gammaRArch_exp]
  have hL : HasDerivAt (fun z : ℂ => Complex.log (Real.pi : ℂ) * (-z / 2))
      (Complex.log (Real.pi : ℂ) * (-(1 / 2))) s := by
    have hbase : HasDerivAt (fun z : ℂ => -z / 2) (-(1 / 2) : ℂ) s := by
      have h1 : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) s := (hasDerivAt_id s).neg
      have h2 := h1.div_const 2
      norm_num at h2
      exact h2
    exact hbase.const_mul _
  exact hL.cexp

theorem gammaRArch_ne_zero (s : ℂ) : gammaRArch s ≠ 0 := by
  rw [gammaRArch_exp]
  exact Complex.exp_ne_zero _

theorem logDeriv_gammaRArch (s : ℂ) :
    logDeriv gammaRArch s = -(Real.log Real.pi : ℂ) / 2 := by
  rw [logDeriv_apply, (gammaRArch_hasDerivAt s).deriv]
  rw [show gammaRArch s = Complex.exp (Complex.log (Real.pi : ℂ) * (-s / 2)) by
    rw [gammaRArch_exp]]
  rw [mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  rw [← Complex.ofReal_log Real.pi_pos.le]
  ring

/-- **The `Gammaℝ` log-derivative** on `Re(s/2) > 0`:
    `logDeriv Gammaℝ s = -(log π)/2 + (1/2)·ψ(s/2)`. -/
theorem logDeriv_gammaR (s : ℂ) (hs : 0 < (s / 2).re) :
    logDeriv Gammaℝ s = -(Real.log Real.pi : ℂ) / 2
      + (1 / 2) * Complex.digamma (s / 2) := by
  have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    rw [hm] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
    have h := (hasDerivAt_id s).div_const 2
    norm_num at h
    exact h
  have hΓd : HasDerivAt Gamma (deriv Gamma (s / 2)) (s / 2) :=
    (Complex.differentiableAt_Gamma _ hpole).hasDerivAt
  have hB : HasDerivAt (fun z : ℂ => Gamma (z / 2)) (deriv Gamma (s / 2) * (1 / 2)) s :=
    hΓd.comp s hhalf
  have hBne : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hGdef : Gammaℝ = fun z : ℂ => gammaRArch z * Gamma (z / 2) := rfl
  rw [hGdef, logDeriv_mul s (gammaRArch_ne_zero s) hBne
    (gammaRArch_hasDerivAt s).differentiableAt hB.differentiableAt]
  rw [logDeriv_gammaRArch]
  have hlogB : logDeriv (fun z : ℂ => Gamma (z / 2)) s = (1 / 2) * Complex.digamma (s / 2) := by
    rw [logDeriv_apply, hB.deriv, Complex.digamma_def, logDeriv_apply]
    field_simp [hBne]
    ring
  rw [hlogB]

/-- **The Archimedean bridge:** the θ integrand equals `Re (logDeriv Gammaℝ)` on the critical
    line — `thetaIntegrand u = Re (logDeriv Gammaℝ (1/2 + iu))`.  With `θ(0) = 0` and the FTC
    derivative (`riemannSiegelTheta_deriv`), this identifies the branch-cut-free `θ` with the
    Archimedean phase of the completed zeta, the term the T3 rectangle identity
    `N(T) = θ(T)/π + 1 + S(T)` splits off of `logDeriv Λ`. -/
theorem thetaIntegrand_eq_re_logDeriv_gammaR (u : ℝ) :
    thetaIntegrand u = (logDeriv Gammaℝ ((1 / 2 : ℂ) + u * I)).re := by
  have hhalf : ((1 / 2 : ℂ) + u * I) / 2 = thetaRay u := by
    unfold thetaRay
    push_cast
    ring
  have hs : 0 < ((((1 / 2 : ℂ) + u * I)) / 2).re := by
    rw [hhalf, thetaRay_re]; norm_num
  rw [logDeriv_gammaR _ hs, hhalf]
  have h1 : (-(Real.log Real.pi : ℂ) / 2) = ((-(Real.log Real.pi) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  unfold thetaIntegrand
  ring

/-! ## Brick 3a: the θ-asymptotics skeleton (T2 rung, first sub-brick).

Target (brick 3 complete): `θ(t) = (t/2)·log(t/(2π)) − t/2 − π/8 + O*(explicit/t)`.
This sub-brick ships the three UNCONDITIONAL pieces every derivation route needs:

  * `digamma_shift` — the iterated recursion `ψ(s+N) = ψ(s) + Σ_{k<N} (s+k)⁻¹` (from Mathlib's
    single-step `digamma_apply_add_one`), which moves the evaluation point right, where the
    Stirling comparison is easy;
  * `norm_inv_sub_log_one_add_inv_le` — the telescoping step bound
    `‖s⁻¹ − log(1+s⁻¹)‖ ≤ ‖s⁻¹‖²·(1−‖s⁻¹‖)⁻¹/2` (Mathlib `norm_log_one_add_sub_self_le`):
    the summand of the Binet-series `ψ(s) − log s = −Σ_{k≥0} [(s+k)⁻¹ − log(1+(s+k)⁻¹)] + …`
    is quadratically small, so the telescoped series converges with an explicit `O(1/‖s‖)` tail;
  * `thetaMain` + `thetaMain_hasDerivAt` — the main term and its derivative
    `(log(t/(2π)))/2`, matching `θ'`'s leading behaviour, so brick 3c can compare the two via
    FTC on `[t₀, t]`.

Remaining sub-bricks: 3b = sum the telescoped series (Summable + tail bound ⟹ effective
`|ψ(s) − log s| ≤ C/‖s‖` on `Re s ≥ 1`, plus the anchor `ψ(s+N) − log(s+N) → 0`); 3c = integrate
`θ' − thetaMain'` and fix the `−π/8` constant.  conjecture1_proved = False. -/

/-- **Iterated digamma recursion:** `ψ(s+N) = ψ(s) + Σ_{k<N} (s+k)⁻¹` for `Re s > 0`. -/
theorem digamma_shift {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Complex.digamma (s + N) = Complex.digamma s + ∑ k ∈ Finset.range N, (s + k)⁻¹ := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hpole : ∀ m : ℕ, s + (n : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
    have hcast : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
    rw [hcast, Complex.digamma_apply_add_one _ hpole, ih, Finset.sum_range_succ, add_assoc]

/-- Subtraction form of the shift, for moving `ψ` evaluations rightward. -/
theorem digamma_eq_shift_sub {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Complex.digamma s = Complex.digamma (s + N) - ∑ k ∈ Finset.range N, (s + k)⁻¹ := by
  rw [digamma_shift hs N]; ring

/-- **The Stirling telescoping step bound:** for `1 < ‖s‖`,
    `‖s⁻¹ − log(1 + s⁻¹)‖ ≤ ‖s⁻¹‖²·(1 − ‖s⁻¹‖)⁻¹/2` — the summand of the Binet series is
    quadratically small in `1/‖s‖`. -/
theorem norm_inv_sub_log_one_add_inv_le {s : ℂ} (hs : 1 < ‖s‖) :
    ‖s⁻¹ - Complex.log (1 + s⁻¹)‖ ≤ ‖s⁻¹‖ ^ 2 * (1 - ‖s⁻¹‖)⁻¹ / 2 := by
  have h0 : (0 : ℝ) < ‖s‖ := lt_trans one_pos hs
  have hz : ‖s⁻¹‖ < 1 := by
    rw [norm_inv, inv_eq_one_div, div_lt_one h0]
    exact hs
  rw [← norm_neg, neg_sub]
  exact Complex.norm_log_one_add_sub_self_le hz

/-- The Riemann–Siegel main term `(t/2)·log(t/(2π)) − t/2 − π/8`, in globally-defined expanded
    form (see `thetaMain_eq` for the classical shape on `t > 0`). -/
noncomputable def thetaMain (t : ℝ) : ℝ :=
  t / 2 * Real.log t - t / 2 * Real.log (2 * Real.pi) - t / 2 - Real.pi / 8

theorem thetaMain_eq {t : ℝ} (ht : 0 < t) :
    thetaMain t = t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8 := by
  rw [Real.log_div ht.ne' (by positivity : (2 * Real.pi) ≠ 0)]
  unfold thetaMain
  ring

/-- The main term's derivative is `(log(t/(2π)))/2` — the leading behaviour of `θ'`. -/
theorem thetaMain_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt thetaMain (Real.log (t / (2 * Real.pi)) / 2) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h1 : HasDerivAt (fun x : ℝ => x / 2 * Real.log x)
      (1 / 2 * Real.log t + t / 2 * t⁻¹) t :=
    ((hasDerivAt_id t).div_const 2).mul hlog
  have h2 : HasDerivAt (fun x : ℝ => x / 2 * Real.log (2 * Real.pi))
      (1 / 2 * Real.log (2 * Real.pi)) t :=
    ((hasDerivAt_id t).div_const 2).mul_const (Real.log (2 * Real.pi))
  have h3 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) t := (hasDerivAt_id t).div_const 2
  have h4 := ((h1.sub h2).sub h3).sub_const (Real.pi / 8)
  have heq : 1 / 2 * Real.log t + t / 2 * t⁻¹ - 1 / 2 * Real.log (2 * Real.pi) - 1 / 2
      = Real.log (t / (2 * Real.pi)) / 2 := by
    rw [Real.log_div ht.ne' (by positivity : (2 * Real.pi) ≠ 0)]
    have hcancel : t / 2 * t⁻¹ = 1 / 2 := by
      have hmul : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
      calc t / 2 * t⁻¹ = t * t⁻¹ / 2 := by ring
        _ = 1 / 2 := by rw [hmul]
    rw [hcancel]
    ring
  rw [heq] at h4
  exact h4

end ZeroFreeBridge
