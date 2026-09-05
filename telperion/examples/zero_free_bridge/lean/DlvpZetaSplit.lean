/- PHASE 4 (dVP frontier, obligation (i-a) CAPSTONE): the log-derivative of ζ splits pointwise
   as the Herglotz zero-sum plus the entire part.

   Assembles the full obligation (i-a) for the actual ζ, tying together the pieces:
     * `DlvpEntire.zeta_extract_zeros_poles` — ζ = (∏ᶠ_ρ (·-ρ)^{divisor}) • g (codiscrete, g analytic zero-free);
     * `DlvpEntire.zeta_finprod_analyticOnNhd` — the zero-part is analytic (divisor ζ ≥ 0);
     * `DlvpTransfer.logDeriv_congr_of_codiscrete` — codiscrete equality of analytic functions
       ⟹ pointwise log-derivative equality (on the open disk);
     * `DlvpBridge.herglotz_split_finprod` — logDeriv of the factored form = Herglotz sum + logDeriv g.

   Result: for `z` in the open disk with `z` avoiding the zeros,
       ζ'/ζ(z) = Σ_ρ (divisor ζ ρ)/(z-ρ) + g'/g(z)     ( = Z + E ).

   This closes obligation (i) of the de la Vallee Poussin frontier.  The SOLE remaining analytic
   step is (i-b') the Borel-Caratheodory BOUND `‖E‖ = ‖logDeriv g‖ ≤ A·L` on the entire part.
   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpEntire
import DlvpBridge
import DlvpTransfer

open Complex

namespace ZeroFreeBridge

/-- **Obligation (i-a) CAPSTONE.**  On the open disk about `c` (Re c > 1) avoiding `s = 1`, the
    log-derivative of ζ splits pointwise (at a `z` avoiding the zeros) as the Herglotz zero-sum
    plus the entire part `logDeriv g`. -/
theorem zeta_logDeriv_split (c : ℂ) (R : ℝ) (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ Metric.closedBall c R) (hc : 1 < c.re) :
    ∃ (g : ℂ → ℂ)
      (hfin : (Function.support
        (fun u => MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u)).Finite),
      AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧ (∀ u : Metric.closedBall c R, g u ≠ 0) ∧
      ∀ z ∈ Metric.ball c R, (∀ ρ ∈ hfin.toFinset, z ≠ ρ) →
        logDeriv riemannZeta z
          = (∑ ρ ∈ hfin.toFinset,
              (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) ρ : ℂ) / (z - ρ))
            + logDeriv g z := by
  obtain ⟨g, hg_ana, hg_ne, hfact⟩ := zeta_extract_zeros_poles c R hR h1 hc
  have hfin : (Function.support
      (fun u => MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u)).Finite :=
    (MeromorphicOn.divisor riemannZeta _).finiteSupport (isCompact_closedBall c R)
  refine ⟨g, hfin, hg_ana, hg_ne, ?_⟩
  intro z hz_ball hz_ne
  have hUsub : Metric.ball c R ⊆ Metric.closedBall c R := Metric.ball_subset_closedBall
  have hsm : (∏ᶠ u, ((· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u))) • g
      = (∏ᶠ u, ((· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u))) * g := by
    funext w; simp [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have hζU : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) :=
    (zeta_analyticOnNhd_disk c R h1).mono hUsub
  have hPgU : AnalyticOnNhd ℂ ((∏ᶠ u, ((· - u) ^
      (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u))) * g) (Metric.ball c R) :=
    ((zeta_finprod_analyticOnNhd c R h1).mono hUsub).mul (hg_ana.mono hUsub)
  have hfactU : riemannZeta =ᶠ[Filter.codiscreteWithin (Metric.ball c R)]
      ((∏ᶠ u, ((· - u) ^
      (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u))) * g) := by
    have := hfact.filter_mono (Filter.codiscreteWithin_mono hUsub)
    rwa [hsm] at this
  have htrans := logDeriv_congr_of_codiscrete hζU hPgU Metric.isOpen_ball
    (convex_ball c R).isPreconnected (Metric.mem_ball_self hR) hz_ball hfactU
  rw [htrans]
  exact herglotz_split_finprod _ hfin g z hz_ne
    (hg_ne ⟨z, hUsub hz_ball⟩) (hg_ana z (hUsub hz_ball)).differentiableAt

end ZeroFreeBridge
