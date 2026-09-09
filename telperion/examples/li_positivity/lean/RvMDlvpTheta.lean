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

/-! ## Brick 3b: the telescoped Binet series — `|ψ(s) − log s| ≤ 1/(Re s − 1)` modulo the anchor.

Telescoping `d(s) = ψ(s) − log s` with `d(s+1) − d(s) = s⁻¹ − log(1+s⁻¹)` (branch-safe on
`Re s > 0` since `|arg| < π/2` on the right half-plane) gives the FINITE identity
`d(s) = d(s+N) − Σ_{k<N} [(s+k)⁻¹ − log(1+(s+k)⁻¹)]`; the 3a step bound + an elementary
inline telescoping estimate `Σ_{k<N} 1/(x+k)² ≤ 1/(x−1)` bound the sum UNIFORMLY in `N`;
letting `N → ∞` against the anchor `d(s+N) → 0` (the ONE remaining analytic input, carried as
an explicit hypothesis — brick 3b′ discharges it) yields the effective Binet bound.
conjecture1_proved = False. -/

/-- **Branch-safe log-quotient step** on the right half-plane:
    `log(s+1) − log s = log(1+s⁻¹)` for `Re s > 0` (both args have `|arg| < π/2`, so the
    difference of logs has imaginary part in `(−π, π)` and `log_exp` applies). -/
theorem log_succ_sub_log {s : ℂ} (hs : 0 < s.re) :
    Complex.log (s + 1) - Complex.log s = Complex.log (1 + s⁻¹) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hexp : Complex.exp (Complex.log (s + 1) - Complex.log s) = 1 + s⁻¹ := by
    rw [Complex.exp_sub, Complex.exp_log hs1, Complex.exp_log hs0, add_div,
      div_self hs0, one_div]
  have harg1 : |Complex.arg (s + 1)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by
      simp only [Complex.add_re, Complex.one_re]; linarith))
  have harg2 : |Complex.arg s| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hs)
  have hIm : (Complex.log (s + 1) - Complex.log s).im
      = Complex.arg (s + 1) - Complex.arg s := by
    simp [Complex.sub_im, Complex.log_im]
  rw [abs_lt] at harg1 harg2
  have h1 : -Real.pi < (Complex.log (s + 1) - Complex.log s).im := by
    rw [hIm]; linarith [harg1.1, harg2.2]
  have h2 : (Complex.log (s + 1) - Complex.log s).im ≤ Real.pi := by
    rw [hIm]; linarith [harg1.2, harg2.1]
  rw [← hexp, Complex.log_exp h1 h2]

/-- Telescoped log shift: `log(s+N) − log s = Σ_{k<N} log(1+(s+k)⁻¹)` on `Re s > 0`. -/
theorem log_shift {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Complex.log (s + N) - Complex.log s
      = ∑ k ∈ Finset.range N, Complex.log (1 + (s + k)⁻¹) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsk : 0 < (s + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hcast : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
    rw [hcast, Finset.sum_range_succ, ← ih, ← log_succ_sub_log hsk]
    ring

/-- **The telescoped Binet identity** (finite form): for `Re s > 0` and any `N`,
    `ψ(s) − log s = (ψ(s+N) − log(s+N)) − Σ_{k<N} ((s+k)⁻¹ − log(1+(s+k)⁻¹))`. -/
theorem digamma_sub_log_telescoped {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Complex.digamma s - Complex.log s
      = (Complex.digamma (s + N) - Complex.log (s + N))
        - ∑ k ∈ Finset.range N, ((s + k)⁻¹ - Complex.log (1 + (s + k)⁻¹)) := by
  have h1 := digamma_shift hs N
  have h2 := log_shift hs N
  rw [Finset.sum_sub_distrib, h1]
  have h2' : Complex.log (s + N)
      = Complex.log s + ∑ k ∈ Finset.range N, Complex.log (1 + (s + k)⁻¹) := by
    linear_combination h2
  rw [h2']
  ring

/-- Elementary inline telescoping tail: `Σ_{k<N} 1/(x+k)² ≤ 1/(x−1) − 1/(x−1+N)` for `1 < x`. -/
theorem sum_one_div_sq_le {x : ℝ} (hx : 1 < x) (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / (x + k) ^ 2 ≤ 1 / (x - 1) - 1 / (x - 1 + N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hp1 : (0:ℝ) < x - 1 + n := by linarith
    have hp2 : (0:ℝ) < x + n := by linarith
    have hstep : 1 / (x + n) ^ 2 ≤ 1 / (x - 1 + n) - 1 / (x + n) := by
      have hsplit : 1 / (x - 1 + n) - 1 / (x + n) = 1 / ((x - 1 + n) * (x + n)) := by
        rw [div_sub_div _ _ (ne_of_gt hp1) (ne_of_gt hp2)]
        congr 1 <;> ring
      rw [hsplit]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hcast : x - 1 + ((n + 1 : ℕ) : ℝ) = x + n := by push_cast; ring
    rw [Finset.sum_range_succ, hcast]
    linarith [ih, hstep]

/-- The Binet-series tail is bounded UNIFORMLY in `N`: for `2 ≤ Re s`,
    `Σ_{k<N} ‖(s+k)⁻¹ − log(1+(s+k)⁻¹)‖ ≤ 1/(Re s − 1)`. -/
theorem sum_norm_inv_sub_log_le {s : ℂ} (hs : 2 ≤ s.re) (N : ℕ) :
    ∑ k ∈ Finset.range N, ‖(s + k)⁻¹ - Complex.log (1 + (s + k)⁻¹)‖ ≤ 1 / (s.re - 1) := by
  have hterm : ∀ k ∈ Finset.range N,
      ‖(s + k)⁻¹ - Complex.log (1 + (s + k)⁻¹)‖ ≤ 1 / (s.re + k) ^ 2 := by
    intro k _
    have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hre : s.re + k ≤ ‖s + k‖ := by
      have h := Complex.re_le_norm (s + k)
      simpa [Complex.add_re, Complex.natCast_re] using h
    have h2 : (2:ℝ) ≤ ‖s + k‖ := by linarith
    have h1 : (1:ℝ) < ‖s + k‖ := by linarith
    have hb := norm_inv_sub_log_one_add_inv_le (s := s + k) h1
    have hnormpos : (0:ℝ) < ‖s + k‖ := by linarith
    have hrepos : (0:ℝ) < s.re + k := by linarith
    have htv : ‖(s + k)⁻¹‖ = 1 / ‖s + k‖ := by rw [norm_inv, inv_eq_one_div]
    have htle : ‖(s + k)⁻¹‖ ≤ 1 / (s.re + k) := by
      rw [htv]; exact one_div_le_one_div_of_le hrepos hre
    have hthalf : ‖(s + k)⁻¹‖ ≤ 1 / 2 := by
      rw [htv]; exact one_div_le_one_div_of_le (by norm_num) h2
    have htnn : (0:ℝ) ≤ ‖(s + k)⁻¹‖ := norm_nonneg _
    have hinv2 : (1 - ‖(s + k)⁻¹‖)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div]
      have hhalf : (1:ℝ) / 2 ≤ 1 - ‖(s + k)⁻¹‖ := by linarith
      calc 1 / (1 - ‖(s + k)⁻¹‖) ≤ 1 / (1 / 2) :=
            one_div_le_one_div_of_le (by norm_num) hhalf
        _ = 2 := by norm_num
    have hinvnn : (0:ℝ) ≤ (1 - ‖(s + k)⁻¹‖)⁻¹ := by
      apply inv_nonneg.mpr; linarith
    calc ‖(s + k)⁻¹ - Complex.log (1 + (s + k)⁻¹)‖
        ≤ ‖(s + k)⁻¹‖ ^ 2 * (1 - ‖(s + k)⁻¹‖)⁻¹ / 2 := hb
      _ ≤ ‖(s + k)⁻¹‖ ^ 2 * 2 / 2 := by
          have := mul_le_mul_of_nonneg_left hinv2 (sq_nonneg ‖(s + k)⁻¹‖)
          linarith
      _ = ‖(s + k)⁻¹‖ ^ 2 := by ring
      _ ≤ (1 / (s.re + k)) ^ 2 := by
          have := mul_le_mul htle htle htnn (le_trans htnn htle)
          calc ‖(s + k)⁻¹‖ ^ 2 = ‖(s + k)⁻¹‖ * ‖(s + k)⁻¹‖ := pow_two _
            _ ≤ (1 / (s.re + k)) * (1 / (s.re + k)) := this
            _ = (1 / (s.re + k)) ^ 2 := (pow_two _).symm
      _ = 1 / (s.re + k) ^ 2 := by rw [div_pow, one_pow]
  have hx : (1:ℝ) < s.re := by linarith
  calc ∑ k ∈ Finset.range N, ‖(s + k)⁻¹ - Complex.log (1 + (s + k)⁻¹)‖
      ≤ ∑ k ∈ Finset.range N, 1 / (s.re + k) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ 1 / (s.re - 1) - 1 / (s.re - 1 + N) := sum_one_div_sq_le hx N
    _ ≤ 1 / (s.re - 1) := by
        have : (0:ℝ) ≤ 1 / (s.re - 1 + N) := by positivity
        linarith

/-- **The effective Binet bound, modulo the anchor** (brick 3b capstone):
    for `2 ≤ Re s`, given the anchor `ψ(s+N) − log(s+N) → 0` (the one remaining analytic
    input — brick 3b′), `‖ψ(s) − log s‖ ≤ 1/(Re s − 1)`. -/
theorem norm_digamma_sub_log_le_of_anchor {s : ℂ} (hs : 2 ≤ s.re)
    (hanchor : Filter.Tendsto
      (fun N : ℕ => Complex.digamma (s + N) - Complex.log (s + N))
      Filter.atTop (nhds 0)) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 1 / (s.re - 1) := by
  have hs0 : 0 < s.re := by linarith
  have hbound : ∀ N : ℕ, ‖Complex.digamma s - Complex.log s‖
      ≤ ‖Complex.digamma (s + N) - Complex.log (s + N)‖ + 1 / (s.re - 1) := by
    intro N
    rw [digamma_sub_log_telescoped hs0 N]
    refine le_trans (norm_sub_le _ _) (add_le_add le_rfl ?_)
    exact le_trans (norm_sum_le _ _) (sum_norm_inv_sub_log_le hs N)
  have hlim : Filter.Tendsto
      (fun N : ℕ => ‖Complex.digamma (s + N) - Complex.log (s + N)‖ + 1 / (s.re - 1))
      Filter.atTop (nhds (0 + 1 / (s.re - 1))) := by
    have hnorm := hanchor.norm
    rw [norm_zero] at hnorm
    exact hnorm.add tendsto_const_nhds
  have hfin := ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  linarith [hfin]

/-! ## Brick 3b′-i: the INTEGER anchor — `ψ(1+N) − log(1+N) → 0`.

The first of the anchor's three sub-bricks (3b′ plan: (i) integer anchor via the Euler–Mascheroni
limit, (ii) real-axis sandwich via `ψ` monotonicity (log-convexity of `Γ`) killing the 1-periodic
ambiguity `L(s+1) = L(s)` on a full real interval, (iii) identity theorem
(`eqOn_of_preconnected_of_frequently_eq`, the corpus `DlvpTransfer` pattern) extending `L ≡ 0`
to all `Re s > 1`).  Here: `ψ(1+N) = −γ + H_N` (our `digamma_shift` at `s = 1` + Mathlib
`digamma_one`), so `ψ(1+N) − log(1+N) = −γ + (H_N − log(N+1)) → −γ + γ = 0` by Mathlib's
`Real.tendsto_harmonic_sub_log_add_one`.  conjecture1_proved = False. -/

/-- **The integer anchor:** `ψ(1+N) − log(1+N) → 0` along `ℕ`. -/
theorem tendsto_digamma_sub_log_one_add_nat :
    Filter.Tendsto (fun N : ℕ => Complex.digamma (1 + N) - Complex.log (1 + N))
      Filter.atTop (nhds 0) := by
  have hγ := Real.tendsto_harmonic_sub_log_add_one
  have hshifted : Filter.Tendsto
      (fun N : ℕ => -Real.eulerMascheroniConstant + ((harmonic N : ℝ) - Real.log ((N : ℝ) + 1)))
      Filter.atTop
      (nhds (-Real.eulerMascheroniConstant + Real.eulerMascheroniConstant)) :=
    tendsto_const_nhds.add hγ
  rw [neg_add_cancel] at hshifted
  have hC := (Complex.continuous_ofReal.tendsto _).comp hshifted
  rw [Complex.ofReal_zero] at hC
  refine hC.congr fun N => ?_
  have hlogN : Complex.log ((1 : ℂ) + N) = ((Real.log ((N : ℝ) + 1) : ℝ) : ℂ) := by
    rw [show ((1 : ℂ) + N) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have hsumN : ∑ k ∈ Finset.range N, ((1 : ℂ) + k)⁻¹ = ((harmonic N : ℝ) : ℂ) := by
    simp only [harmonic]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
  show (((-Real.eulerMascheroniConstant + ((harmonic N : ℝ) - Real.log ((N : ℝ) + 1))) : ℝ) : ℂ)
      = Complex.digamma (1 + N) - Complex.log (1 + N)
  rw [digamma_shift (s := 1) (by norm_num) N, Complex.digamma_one, hsumN, hlogN]
  push_cast
  ring

/-! ## Brick 3b′-ii-a: `ψ` is REAL on the positive reals, equals `deriv (log ∘ Γ)`, and that
derivative is MONOTONE (log-convexity of `Γ`, Bohr–Mollerup).  These are the sandwich's two
pillars; 3b′-ii-b squeezes `ψ(x+N) − log(x+N) → 0` for real `x` between integer anchors. -/

/-- At a positive real point, the complex `Γ` has a REAL derivative that is simultaneously the
    derivative of the real `Γ` (Schwarz-reflection style, via `HasDerivAt.real_of_complex` applied
    to both the real part and the `(-I)·`-twisted real part). -/
theorem gamma_hasDerivAt_ofReal {x : ℝ} (hx : 0 < x) :
    ∃ d : ℝ, HasDerivAt Complex.Gamma ((d : ℝ) : ℂ) ((x : ℝ) : ℂ) ∧ HasDerivAt Real.Gamma d x := by
  have hpole : ∀ m : ℕ, ((x : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hC : HasDerivAt Complex.Gamma (deriv Complex.Gamma ((x : ℝ) : ℂ)) ((x : ℝ) : ℂ) :=
    (Complex.differentiableAt_Gamma _ hpole).hasDerivAt
  set d := deriv Complex.Gamma ((x : ℝ) : ℂ) with hd
  have hre : HasDerivAt (fun t : ℝ => (Complex.Gamma ((t : ℝ) : ℂ)).re) d.re x :=
    hC.real_of_complex
  have him0 : HasDerivAt (fun t : ℝ => ((-Complex.I) * Complex.Gamma ((t : ℝ) : ℂ)).re)
      ((-Complex.I) * d).re x := (hC.const_mul _).real_of_complex
  have hzero : (fun t : ℝ => ((-Complex.I) * Complex.Gamma ((t : ℝ) : ℂ)).re)
      = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rw [Complex.Gamma_ofReal]
    simp [Complex.mul_re]
  have himval : ((-Complex.I) * d).re = 0 :=
    (hzero ▸ him0).unique (hasDerivAt_const x 0)
  have him' : d.im = 0 := by
    have hcalc : ((-Complex.I) * d).re = d.im := by
      simp [Complex.mul_re]
    rw [hcalc] at himval
    exact himval
  have hdeq : d = ((d.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him'
  refine ⟨d.re, hdeq ▸ hC, ?_⟩
  have hgr : (fun t : ℝ => (Complex.Gamma ((t : ℝ) : ℂ)).re) = Real.Gamma := by
    funext t
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  exact hgr ▸ hre

/-- **`ψ` is real on the positive reals**, and equals `deriv (log ∘ Γ)` there:
    `ψ(x) = ↑(deriv (Real.log ∘ Real.Gamma) x)` for `0 < x`. -/
theorem digamma_ofReal_eq {x : ℝ} (hx : 0 < x) :
    Complex.digamma ((x : ℝ) : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  obtain ⟨d, hC, hR⟩ := gamma_hasDerivAt_ofReal hx
  have hΓpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hlog : HasDerivAt (Real.log ∘ Real.Gamma) ((Real.Gamma x)⁻¹ * d) x :=
    (Real.hasDerivAt_log hΓpos.ne').comp x hR
  rw [Complex.digamma_def, logDeriv_apply, hC.deriv, hlog.deriv, Complex.Gamma_ofReal]
  push_cast
  rw [div_eq_mul_inv, mul_comm]

/-- **The real digamma is monotone on `(0, ∞)`** — the derivative of the log-convex
    `log ∘ Γ` (Bohr–Mollerup `Real.convexOn_log_Gamma` + `ConvexOn.monotoneOn_deriv`).
    The sandwich pillar of the anchor's real-axis step. -/
theorem monotoneOn_deriv_log_Gamma :
    MonotoneOn (deriv (Real.log ∘ Real.Gamma)) (Set.Ioi (0 : ℝ)) := by
  refine Real.convexOn_log_Gamma.monotoneOn_deriv ?_
  intro x hx
  obtain ⟨d, _, hR⟩ := gamma_hasDerivAt_ofReal (Set.mem_Ioi.mp hx)
  exact ((Real.hasDerivAt_log
    (Real.Gamma_pos_of_pos (Set.mem_Ioi.mp hx)).ne').comp x hR).differentiableAt

/-! ## Brick 3b′-ii-b: the REAL-AXIS SQUEEZE — the anchor discharged on `[1, 3]`.

Sandwich `d(x+N) = ψ(x+N) − log(x+N)` for real `x ∈ [1,3]` between the integer-anchor
sequences: `ψ` monotone (pillar ii-a) gives `ψ(1+N) ≤ ψ(x+N) ≤ ψ(3+N)`; `log` monotone gives
the reverse for the log part; both outer sequences → 0 by the integer anchor (3b′-i, plus its
`N ↦ N+2` shift) and the vanishing log gap (`Real.tendsto_log_comp_add_sub_log`).  Squeeze ⟹
`d(x+N) → 0` for every real `x ∈ [1,3]` — the anchor hypothesis of
`norm_digamma_sub_log_le_of_anchor` is DISCHARGED on the real segment, yielding the first
UNCONDITIONAL effective Binet points (`norm_digamma_sub_log_le_ofReal`).  Brick (iii) extends
to complex `s` by the identity theorem.  conjecture1_proved = False. -/

/-- The real Binet difference `deriv (log ∘ Γ) t − log t`. -/
noncomputable def binetR (t : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) t - Real.log t

/-- Pointwise complex-to-real identification: for `t > 0`,
    `ψ(↑t) − log ↑t = ↑(binetR t)`. -/
theorem digamma_sub_log_ofReal_eq {t : ℝ} (ht : 0 < t) :
    Complex.digamma ((t : ℝ) : ℂ) - Complex.log ((t : ℝ) : ℂ) = ((binetR t : ℝ) : ℂ) := by
  rw [digamma_ofReal_eq ht, ← Complex.ofReal_log ht.le, ← Complex.ofReal_sub]
  rfl

/-- **The real integer anchor:** `binetR (1+N) → 0` (real part of brick 3b′-i). -/
theorem tendsto_binetR_one_add : Filter.Tendsto (fun N : ℕ => binetR (1 + N))
    Filter.atTop (nhds 0) := by
  have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp tendsto_digamma_sub_log_one_add_nat
  rw [Complex.zero_re] at h
  refine h.congr fun N => ?_
  show (Complex.digamma (1 + N) - Complex.log (1 + N)).re = binetR (1 + N)
  have hcast : (1 : ℂ) + (N : ℂ) = (((1 + N : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, digamma_sub_log_ofReal_eq (by positivity), Complex.ofReal_re]

/-- Shifted real anchor: `binetR (3+N) → 0` (the `N ↦ N+2` shift of the integer anchor). -/
theorem tendsto_binetR_three_add : Filter.Tendsto (fun N : ℕ => binetR (3 + N))
    Filter.atTop (nhds 0) := by
  have h := (Filter.tendsto_add_atTop_iff_nat (f := fun N : ℕ => binetR (1 + N))
    (l := nhds 0) 2).mpr tendsto_binetR_one_add
  refine h.congr fun N => ?_
  show binetR (1 + ↑(N + 2)) = binetR (3 + N)
  congr 1
  push_cast
  ring

/-- The log gap vanishes: `log(3+N) − log(1+N) → 0`. -/
theorem tendsto_log_gap : Filter.Tendsto
    (fun N : ℕ => Real.log (3 + N) - Real.log (1 + N)) Filter.atTop (nhds 0) := by
  have hn : Filter.Tendsto (fun N : ℕ => (1 + N : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    push_cast
    linarith
  have h := (Real.tendsto_log_comp_add_sub_log 2).comp hn
  refine h.congr fun N => ?_
  show Real.log ((1 + N) + 2) - Real.log (1 + N) = Real.log (3 + N) - Real.log (1 + N)
  congr 2
  ring

/-- **THE SQUEEZE (brick ii-b):** for real `x ∈ [1, 3]`, `binetR (x+N) → 0`. -/
theorem tendsto_binetR_add {x : ℝ} (hx1 : 1 ≤ x) (hx3 : x ≤ 3) :
    Filter.Tendsto (fun N : ℕ => binetR (x + N)) Filter.atTop (nhds 0) := by
  have hψ := monotoneOn_deriv_log_Gamma
  have hlow : Filter.Tendsto
      (fun N : ℕ => binetR (1 + N) - (Real.log (3 + N) - Real.log (1 + N)))
      Filter.atTop (nhds (0 - 0)) := tendsto_binetR_one_add.sub tendsto_log_gap
  have hup : Filter.Tendsto
      (fun N : ℕ => binetR (3 + N) + (Real.log (3 + N) - Real.log (1 + N)))
      Filter.atTop (nhds (0 + 0)) := tendsto_binetR_three_add.add tendsto_log_gap
  rw [sub_zero] at hlow
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun N => ?_) (fun N => ?_)
  · -- lower: ψ(1+N) − log(3+N) ≤ ψ(x+N) − log(x+N)
    have hm : deriv (Real.log ∘ Real.Gamma) (1 + N) ≤ deriv (Real.log ∘ Real.Gamma) (x + N) :=
      hψ (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) (by linarith)
    have hl : Real.log (x + N) ≤ Real.log (3 + N) :=
      Real.log_le_log (by positivity) (by linarith)
    simp only [binetR]
    linarith
  · -- upper: ψ(x+N) − log(x+N) ≤ ψ(3+N) − log(1+N)
    have hm : deriv (Real.log ∘ Real.Gamma) (x + N) ≤ deriv (Real.log ∘ Real.Gamma) (3 + N) :=
      hψ (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) (by linarith)
    have hl : Real.log (1 + N) ≤ Real.log (x + N) :=
      Real.log_le_log (by positivity) (by linarith)
    simp only [binetR]
    linarith

/-- **The COMPLEX anchor on the real segment `[1,3]`** — brick ii-b's conclusion in the exact
    shape `norm_digamma_sub_log_le_of_anchor` consumes. -/
theorem tendsto_digamma_sub_log_ofReal {x : ℝ} (hx1 : 1 ≤ x) (hx3 : x ≤ 3) :
    Filter.Tendsto
      (fun N : ℕ => Complex.digamma (((x : ℝ) : ℂ) + N) - Complex.log (((x : ℝ) : ℂ) + N))
      Filter.atTop (nhds 0) := by
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tendsto_binetR_add hx1 hx3)
  rw [Complex.ofReal_zero] at h
  refine h.congr fun N => ?_
  show ((binetR (x + N) : ℝ) : ℂ)
      = Complex.digamma (((x : ℝ) : ℂ) + N) - Complex.log (((x : ℝ) : ℂ) + N)
  have hcast : ((x : ℝ) : ℂ) + (N : ℂ) = (((x + N : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, digamma_sub_log_ofReal_eq (by positivity)]

/-- **UNCONDITIONAL effective Binet points** (anchor fully discharged): for real `x ∈ [2, 3]`,
    `‖ψ(x) − log x‖ ≤ 1/(x−1)`.  The first Binet bounds in this corpus with NO analytic
    hypothesis remaining.  conjecture1_proved = False. -/
theorem norm_digamma_sub_log_le_ofReal {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    ‖Complex.digamma ((x : ℝ) : ℂ) - Complex.log ((x : ℝ) : ℂ)‖ ≤ 1 / (x - 1) := by
  have hre : (2 : ℝ) ≤ (((x : ℝ) : ℂ)).re := by simpa using hx2
  have h := norm_digamma_sub_log_le_of_anchor hre
    (tendsto_digamma_sub_log_ofReal (by linarith) hx3)
  simpa using h

/-! ## Brick 3b′-iii: the IDENTITY THEOREM — the anchor discharged for ALL `Re s ≥ 2`.

The limit function `binetLimit s := (ψ(s) − log s) + Σ′_k [(s+k)⁻¹ − log(1+(s+k)⁻¹)]` is the
`N → ∞` limit of `ψ(s+N) − log(s+N)` (partial sums = the telescoped Binet identity).  It is
HOLOMORPHIC on `U = {Re > 3/2}` (Weierstrass M-test: `‖tail_k‖ ≤ (3/2)/(3/2+k)²`, uniform on
`U`, summable by our own partial-sum lemma), and VANISHES on the real segment `[2,3]` (brick
ii-b's squeeze + uniqueness of limits).  The identity theorem on the convex half-plane then
forces `binetLimit ≡ 0` on all of `U` — so the anchor `ψ(s+N) − log(s+N) → 0` holds for EVERY
`s` with `Re s ≥ 2`, and the effective Binet bound `‖ψ(s) − log s‖ ≤ 1/(Re s − 1)` is
UNCONDITIONAL.  The analytic heart of Turing rung T2 is complete.
conjecture1_proved = False. -/

/-- The Binet tail term. -/
noncomputable def binetTail (s : ℂ) (k : ℕ) : ℂ := (s + k)⁻¹ - Complex.log (1 + (s + k)⁻¹)

/-- The Binet limit function. -/
noncomputable def binetLimit (s : ℂ) : ℂ :=
  (Complex.digamma s - Complex.log s) + ∑' k : ℕ, binetTail s k

/-- Uniform tail bound on `{Re > 3/2}`: `‖binetTail s k‖ ≤ (3/2)/(3/2+k)²`. -/
theorem binetTail_norm_le {s : ℂ} (hs : 3/2 < s.re) (k : ℕ) :
    ‖binetTail s k‖ ≤ (3/2) * (1 / (3/2 + k) ^ 2) := by
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hre : (3/2 + k : ℝ) ≤ ‖s + k‖ := by
    have h := Complex.re_le_norm (s + k)
    simp only [Complex.add_re, Complex.natCast_re] at h
    linarith
  have hrepos : (0:ℝ) < 3/2 + k := by linarith
  have h1 : (1:ℝ) < ‖s + k‖ := by linarith
  have hb := norm_inv_sub_log_one_add_inv_le (s := s + k) h1
  have htv : ‖(s + k)⁻¹‖ = 1 / ‖s + k‖ := by rw [norm_inv, inv_eq_one_div]
  have htle : ‖(s + k)⁻¹‖ ≤ 1 / (3/2 + k) := by
    rw [htv]; exact one_div_le_one_div_of_le hrepos hre
  have hth : ‖(s + k)⁻¹‖ ≤ 2/3 := by
    refine le_trans htle ?_
    rw [div_le_div_iff₀ hrepos (by norm_num)]
    linarith
  have htnn : (0:ℝ) ≤ ‖(s + k)⁻¹‖ := norm_nonneg _
  have hinv3 : (1 - ‖(s + k)⁻¹‖)⁻¹ ≤ 3 := by
    rw [inv_eq_one_div]
    have hthird : (1:ℝ)/3 ≤ 1 - ‖(s + k)⁻¹‖ := by linarith
    calc 1 / (1 - ‖(s + k)⁻¹‖) ≤ 1 / (1/3) := one_div_le_one_div_of_le (by norm_num) hthird
      _ = 3 := by norm_num
  calc ‖binetTail s k‖
      ≤ ‖(s + k)⁻¹‖ ^ 2 * (1 - ‖(s + k)⁻¹‖)⁻¹ / 2 := hb
    _ ≤ ‖(s + k)⁻¹‖ ^ 2 * 3 / 2 := by
        have := mul_le_mul_of_nonneg_left hinv3 (sq_nonneg ‖(s + k)⁻¹‖)
        linarith
    _ ≤ (1 / (3/2 + k)) ^ 2 * 3 / 2 := by
        have hsq : ‖(s + k)⁻¹‖ ^ 2 ≤ (1 / (3/2 + k)) ^ 2 := by
          calc ‖(s + k)⁻¹‖ ^ 2 = ‖(s + k)⁻¹‖ * ‖(s + k)⁻¹‖ := pow_two _
            _ ≤ (1 / (3/2 + k)) * (1 / (3/2 + k)) :=
                mul_le_mul htle htle htnn (le_trans htnn htle)
            _ = (1 / (3/2 + k)) ^ 2 := (pow_two _).symm
        linarith
    _ = (3/2) * (1 / (3/2 + k) ^ 2) := by rw [div_pow, one_pow]; ring

/-- The uniform majorant is summable (our own partial-sum lemma + boundedness). -/
theorem summable_binetMajorant : Summable (fun k : ℕ => (3/2 : ℝ) * (1 / (3/2 + k) ^ 2)) := by
  refine summable_of_sum_range_le (c := 3) (fun n => by positivity) (fun n => ?_)
  rw [← Finset.mul_sum]
  have h := sum_one_div_sq_le (x := (3/2 : ℝ)) (by norm_num) n
  have h3 : (0:ℝ) ≤ 1 / (3/2 - 1 + n) := by positivity
  nlinarith [h]

/-- Each tail term is differentiable on `{Re > 3/2}`. -/
theorem binetTail_differentiableOn (k : ℕ) :
    DifferentiableOn ℂ (fun s => binetTail s k) {s : ℂ | 3/2 < s.re} := by
  intro s hs
  have hsre : 3/2 < s.re := hs
  have hne : s + k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hinvDA : DifferentiableAt ℂ (fun z : ℂ => (z + k)⁻¹) s :=
    (differentiableAt_id.add_const (k : ℂ)).inv hne
  have hgDA : DifferentiableAt ℂ (fun z : ℂ => 1 + (z + k)⁻¹) s := hinvDA.const_add 1
  have hrepos : (0:ℝ) < (s + k).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hslit : (1 + (s + k)⁻¹) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hinvre : (0:ℝ) ≤ ((s + k)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hrepos.le (Complex.normSq_nonneg _)
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hlogDA : DifferentiableAt ℂ (fun z : ℂ => Complex.log (1 + (z + k)⁻¹)) s :=
    hgDA.clog hslit
  exact (hinvDA.sub hlogDA).differentiableWithinAt

/-- `Γ` is analytic at every point of the right half-plane. -/
theorem gamma_analyticAt_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Complex.Gamma s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    rw [hm] at hz
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hz
    linarith [Nat.cast_nonneg (α := ℝ) m]
  exact (hdiff.analyticOnNhd hopen) s hs

/-- **`binetLimit` is holomorphic on `{Re > 3/2}`** (M-test + Weierstrass). -/
theorem binetLimit_differentiableOn :
    DifferentiableOn ℂ binetLimit {s : ℂ | 3/2 < s.re} := by
  have hUopen : IsOpen {z : ℂ | 3/2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun s => Complex.digamma s - Complex.log s)
      {z : ℂ | 3/2 < z.re} := by
    intro z hz
    have hzre : (3/2:ℝ) < z.re := hz
    have hana := gamma_analyticAt_re_pos (s := z) (by linarith)
    have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hψ : DifferentiableAt ℂ Complex.digamma z := by
      have heq : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
        funext w; rw [Complex.digamma_def, logDeriv_apply]
      rw [heq]
      exact (hana.deriv.differentiableAt).div hana.differentiableAt hΓne
    have hzslit : z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; linarith
    have hlog : DifferentiableAt ℂ Complex.log z := by
      have h : DifferentiableAt ℂ (fun w : ℂ => Complex.log w) z :=
        differentiableAt_id.clog hzslit
      exact h
    exact (hψ.sub hlog).differentiableWithinAt
  have hts : DifferentiableOn ℂ (fun s => ∑' k : ℕ, binetTail s k) {z : ℂ | 3/2 < z.re} := by
    refine differentiableOn_tsum_of_summable_norm summable_binetMajorant
      binetTail_differentiableOn hUopen (fun k w hw => ?_)
    exact binetTail_norm_le hw k
  exact fun z hz => ((hd z hz).add (hts z hz))

/-- The partial sums of the tail are the telescoped Binet identity:
    `ψ(s+N) − log(s+N) → binetLimit s` for `Re s ≥ 2`. -/
theorem tendsto_binetLimit {s : ℂ} (hs : 2 ≤ s.re) :
    Filter.Tendsto (fun N : ℕ => Complex.digamma (s + N) - Complex.log (s + N))
      Filter.atTop (nhds (binetLimit s)) := by
  have hs0 : 0 < s.re := by linarith
  have hsummn : Summable (fun k => ‖binetTail s k‖) := by
    refine summable_of_sum_range_le (c := 1 / (s.re - 1)) (fun n => norm_nonneg _) (fun n => ?_)
    exact sum_norm_inv_sub_log_le hs n
  have hsumm : Summable (binetTail s) := hsummn.of_norm
  have hpartial := (hsumm.hasSum_iff_tendsto_nat).mp hsumm.hasSum
  have hlim := (tendsto_const_nhds (x := Complex.digamma s - Complex.log s)
    (f := Filter.atTop (α := ℕ))).add hpartial
  refine hlim.congr fun N => ?_
  have h := digamma_sub_log_telescoped hs0 N
  simp only [binetTail]
  linear_combination h

/-- `binetLimit` vanishes on the real segment `[2, 3]` (squeeze + uniqueness of limits). -/
theorem binetLimit_eq_zero_ofReal {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    binetLimit ((x : ℝ) : ℂ) = 0 := by
  have h1 := tendsto_binetLimit (s := ((x:ℝ):ℂ)) (by simpa using hx2)
  have h2 := tendsto_digamma_sub_log_ofReal (by linarith) hx3
  exact tendsto_nhds_unique h1 h2

/-- **THE IDENTITY THEOREM:** `binetLimit ≡ 0` on `{Re > 3/2}`. -/
theorem binetLimit_eq_zero {s : ℂ} (hs : 3/2 < s.re) : binetLimit s = 0 := by
  have hUopen : IsOpen {z : ℂ | 3/2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hFana : AnalyticOnNhd ℂ binetLimit {z : ℂ | 3/2 < z.re} :=
    binetLimit_differentiableOn.analyticOnNhd hUopen
  have h0ana : AnalyticOnNhd ℂ (fun _ => (0:ℂ)) {z : ℂ | 3/2 < z.re} :=
    fun z _ => analyticAt_const
  have hpre : IsPreconnected {z : ℂ | 3/2 < z.re} :=
    (convex_halfSpace_re_gt (3/2)).isPreconnected
  have hz₀ : ((5/2 : ℝ) : ℂ) ∈ {z : ℂ | 3/2 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]; norm_num
  have hfreq : ∃ᶠ z in nhdsWithin ((5/2 : ℝ) : ℂ) {((5/2 : ℝ) : ℂ)}ᶜ,
      binetLimit z = (fun _ => (0:ℂ)) z := by
    rw [Filter.frequently_iff]
    intro V hV
    rw [Metric.mem_nhdsWithin_iff] at hV
    obtain ⟨ε, hε, hsub⟩ := hV
    set δ : ℝ := min (ε/2) (1/2) with hδdef
    have hδpos : 0 < δ := by
      apply lt_min <;> [linarith; norm_num]
    have hδle : δ ≤ 1/2 := min_le_right _ _
    have hδlt : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨((5/2 + δ : ℝ) : ℂ), hsub ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have : ((5/2 + δ : ℝ) : ℂ) - ((5/2 : ℝ) : ℂ) = ((δ : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
      exact hδlt
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp only [Complex.ofReal_re] at this
      linarith
    · exact binetLimit_eq_zero_ofReal (by linarith) (by linarith)
  exact (hFana.eqOn_of_preconnected_of_frequently_eq h0ana hpre hz₀ hfreq) hs

/-- **THE ANCHOR, UNCONDITIONAL:** for every `s` with `2 ≤ Re s`,
    `ψ(s+N) − log(s+N) → 0`. -/
theorem tendsto_digamma_sub_log {s : ℂ} (hs : 2 ≤ s.re) :
    Filter.Tendsto (fun N : ℕ => Complex.digamma (s + N) - Complex.log (s + N))
      Filter.atTop (nhds 0) := by
  have h := tendsto_binetLimit hs
  rwa [binetLimit_eq_zero (by linarith)] at h

/-- **THE UNCONDITIONAL EFFECTIVE BINET BOUND** (T2 analytic heart, complete):
    `‖ψ(s) − log s‖ ≤ 1/(Re s − 1)` for ALL `s` with `Re s ≥ 2` — no hypotheses.
    conjecture1_proved = False. -/
theorem norm_digamma_sub_log_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 1 / (s.re - 1) :=
  norm_digamma_sub_log_le_of_anchor hs (tendsto_digamma_sub_log hs)

end ZeroFreeBridge
