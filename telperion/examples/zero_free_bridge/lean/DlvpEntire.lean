/- PHASE 4 (dVP frontier, obligation (i) FOUNDATIONS): the ζ canonical factorization on a
   disk, and the analyticity of the entire part.

   `DlvpHerglotz.herglotz_split` computes `logDeriv ((∏_ρ (·-ρ)^{m}) · g) = Z + logDeriv g`
   GIVEN the factored form.  This file supplies the two ζ-specific ingredients that produce
   that form and identify the entire part:

     * `zeta_extract_zeros_poles` (obligation (i-a)) — ζ IS such a factorization on a disk
       about `c` (Re c > 1) avoiding the pole `s = 1`: `ζ = (∏ᶠ_ρ (·-ρ)^{divisor}) • g` with
       `g` analytic and zero-free.  Discharges Mathlib `MeromorphicOn.extract_zeros_poles`'s
       three hypotheses for ζ — MeromorphicOn (ζ analytic), order ≠ ⊤ everywhere (ζ c ≠ 0 +
       the disk is connected, `exists_meromorphicOrderAt_ne_top_iff_forall`), and finite
       divisor support (compactness).

     * `differentiableAt_logDeriv` / `analyticOnNhd_logDeriv` (obligation (i-b), first half) —
       the entire part `E = logDeriv g = g'/g` is analytic where `g` is analytic and nonzero.

   What remains of obligation (i): (i-a') transfer the CODISCRETE factorization equality to a
   POINTWISE `logDeriv ζ z = Z + E` at a zero-free `z` (codiscrete → nhds → deriv), with the
   finprod↔Finset bridge to `herglotz_split`; (i-b') the Borel-Caratheodory BOUND `‖E‖ ≤ A·L`
   on the entire part.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaDisk

open Complex

namespace ZeroFreeBridge

/-- (i-b) The ENTIRE PART `E = logDeriv g = g'/g` is differentiable where `g` is analytic and
    nonzero — a quotient of analytic functions with nonvanishing denominator. -/
theorem differentiableAt_logDeriv {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hne : g z ≠ 0) :
    DifferentiableAt ℂ (logDeriv g) z := by
  have h1 : DifferentiableAt ℂ (deriv g) z := (hg.deriv).differentiableAt
  have h2 : DifferentiableAt ℂ g z := hg.differentiableAt
  have hfun : logDeriv g = fun w => deriv g w / g w := rfl
  rw [hfun]
  exact h1.div h2 hne

/-- The entire part is analytic (differentiable) throughout a set where `g` is analytic and
    nonvanishing. -/
theorem analyticOnNhd_logDeriv {g : ℂ → ℂ} {U : Set ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hne : ∀ z ∈ U, g z ≠ 0) :
    ∀ z ∈ U, DifferentiableAt ℂ (logDeriv g) z :=
  fun z hz => differentiableAt_logDeriv (hg z hz) (hne z hz)

/-- (i-a) **The ζ canonical factorization.**  On a disk about `c` (Re c > 1) avoiding the pole
    `s = 1`, `ζ = (∏ᶠ_ρ (·-ρ)^{divisor ζ}) • g` with `g` analytic and zero-free — the factored
    form `herglotz_split` consumes. -/
theorem zeta_extract_zeros_poles (c : ℂ) (R : ℝ) (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ Metric.closedBall c R) (hc : 1 < c.re) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ u : Metric.closedBall c R, g u ≠ 0) ∧
      riemannZeta =ᶠ[Filter.codiscreteWithin (Metric.closedBall c R)]
        (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u)) • g := by
  have hana := zeta_analyticOnNhd_disk c R h1
  have hmero := hana.meromorphicOn
  have hcin : c ∈ Metric.closedBall c R := Metric.mem_closedBall_self hR.le
  have hconn : IsConnected (Metric.closedBall c R) :=
    (convex_closedBall c R).isConnected ⟨c, hcin⟩
  have hord_c : meromorphicOrderAt riemannZeta c ≠ ⊤ := by
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hana c hcin).meromorphicAt]
    exact (hana c hcin).continuousAt.eventually_ne (zeta_ne_zero_of_one_lt_re c hc)
      |>.filter_mono nhdsWithin_le_nhds
  have hord : ∀ u : Metric.closedBall c R, meromorphicOrderAt riemannZeta u ≠ ⊤ :=
    (hmero.exists_meromorphicOrderAt_ne_top_iff_forall hconn).1 ⟨⟨c, hcin⟩, hord_c⟩
  have hfin : (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R)).support.Finite :=
    (MeromorphicOn.divisor riemannZeta _).finiteSupport (isCompact_closedBall c R)
  exact hmero.extract_zeros_poles hord hfin

/-- (piece A) The ζ zero-part finprod is ANALYTIC on the disk: ζ has no poles there, so its
    divisor is `≥ 0`, making `∏ᶠ u, (·-u)^{divisor u}` a polynomial (analytic).  With this, the
    factored form `(∏ᶠ..) • g` is analytic — the missing hypothesis for `logDeriv_congr_of_codiscrete`
    to apply to ζ vs its factorization. -/
theorem zeta_finprod_analyticOnNhd (c : ℂ) (R : ℝ) (h1 : (1 : ℂ) ∉ Metric.closedBall c R) :
    AnalyticOnNhd ℂ
      (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u))
      (Metric.closedBall c R) := by
  have hana := zeta_analyticOnNhd_disk c R h1
  have hdiv := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana
  intro z _hz
  exact Function.FactorizedRational.analyticAt (hdiv z)

end ZeroFreeBridge
