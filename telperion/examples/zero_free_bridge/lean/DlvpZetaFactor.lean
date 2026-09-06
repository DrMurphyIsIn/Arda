/- PHASE 4 (dVP frontier, entire-part composition — the POINTWISE ζ = P·g factorization on the open
   disk): lift `MeromorphicOn.extract_zeros_poles`'s CODISCRETE factorization to a genuine `EqOn`.

   `DlvpEntire.zeta_extract_zeros_poles` gives `ζ =ᶠ[codiscreteWithin (closedBall c R)] (P • g)` with
   `P = ∏ᶠ_ρ (·-ρ)^{divisor}` and `g` analytic + zero-free.  `norm_logDeriv_le_of_boundary_split`
   (`DlvpBoundaryDecomp`) instead needs the factorization POINTWISE.  Both `ζ` and `P·g` are analytic on
   the open ball (ζ avoids the pole; `P·g` = `zeta_finprod_analyticOnNhd` × `g`), so the analytic
   identity principle upgrades the codiscrete agreement to `EqOn ζ (P·g) (ball c R)` — mirroring the
   `logDeriv` transfer `DlvpTransfer.logDeriv_congr_of_codiscrete`, but at the FUNCTION level.

   This discharges the centre factorization `hfac_c : ζ c = P c * g c` (`c ∈ ball c R`).  The sphere
   factorization `hfac` (boundary points, `∉ ball`) additionally needs a continuity/density extension to
   `closedBall` and a no-zero-on-the-sphere choice of `R` — the remaining plumbing for the full
   composition.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpEntire

open Complex Metric Filter Topology

namespace ZeroFreeBridge

/-- **Pointwise ζ = P·g on the open disk.**  The `extract_zeros_poles` codiscrete factorization,
    upgraded by the analytic identity principle to a genuine `EqOn` on `ball c R`. -/
theorem zeta_eqOn_prod_smul_g (c : ℂ) (R : ℝ) (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ Metric.closedBall c R) (hc : 1 < c.re) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ u : Metric.closedBall c R, g u ≠ 0) ∧
      Set.EqOn riemannZeta
        ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u)) • g)
        (Metric.ball c R) := by
  obtain ⟨g, hg_an, hg_ne, hcodisc⟩ := zeta_extract_zeros_poles c R hR h1 hc
  refine ⟨g, hg_an, hg_ne, ?_⟩
  set P := (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u)) with hP
  -- both sides analytic on the open ball
  have hζ_an : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) :=
    (zeta_analyticOnNhd_disk c R h1).mono Metric.ball_subset_closedBall
  have hPg_an : AnalyticOnNhd ℂ (P • g) (Metric.ball c R) :=
    ((zeta_finprod_analyticOnNhd c R h1).smul hg_an).mono Metric.ball_subset_closedBall
  -- codiscrete agreement gives frequent agreement near the centre
  have hz₀ : c ∈ Metric.closedBall c R := Metric.mem_closedBall_self hR.le
  have hmem : {x | riemannZeta x = (P • g) x} ∪ (Metric.closedBall c R)ᶜ ∈ 𝓝[≠] c :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hcodisc) c hz₀
  have hcb_nhds : Metric.closedBall c R ∈ 𝓝[≠] c :=
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds c hR)
  have hev : ∀ᶠ x in 𝓝[≠] c, riemannZeta x = (P • g) x := by
    filter_upwards [hmem, hcb_nhds] with x hx hxcb
    rcases hx with h1' | h2'
    · exact h1'
    · exact absurd hxcb h2'
  exact hζ_an.eqOn_of_preconnected_of_frequently_eq hPg_an
    (convex_ball c R).isPreconnected (Metric.mem_ball_self hR) hev.frequently

/-- **Pointwise ζ = P·g on the CLOSED disk.**  The open-ball `EqOn` (`zeta_eqOn_prod_smul_g`) extends to
    `closedBall c R` by continuity + density (`ball` is dense in `closedBall`; both `ζ` and `P·g` are
    analytic hence continuous on the closed disk).  This discharges the centre factorization
    `hfac_c : ζ c = P c * g c` and — at every non-zero sphere point — the boundary factorization `hfac`
    for `norm_logDeriv_le_of_boundary_split`. -/
theorem zeta_eqOn_prod_smul_g_closedBall (c : ℂ) (R : ℝ) (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ Metric.closedBall c R) (hc : 1 < c.re) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ u : Metric.closedBall c R, g u ≠ 0) ∧
      Set.EqOn riemannZeta
        ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u)) • g)
        (Metric.closedBall c R) := by
  obtain ⟨g, hg_an, hg_ne, hball⟩ := zeta_eqOn_prod_smul_g c R hR h1 hc
  refine ⟨g, hg_an, hg_ne, ?_⟩
  set P := (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta (Metric.closedBall c R) u)) with hP
  have hcont_ζ : ContinuousOn riemannZeta (Metric.closedBall c R) :=
    (zeta_analyticOnNhd_disk c R h1).continuousOn
  have hcont_Pg : ContinuousOn (P • g) (Metric.closedBall c R) :=
    ((zeta_finprod_analyticOnNhd c R h1).smul hg_an).continuousOn
  have hclosure : closure (Metric.ball c R) = Metric.closedBall c R :=
    closure_ball c (ne_of_gt hR)
  exact hball.of_subset_closure hcont_ζ hcont_Pg Metric.ball_subset_closedBall
    (le_of_eq hclosure.symm)

end ZeroFreeBridge
