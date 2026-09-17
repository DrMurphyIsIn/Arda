/- PHASE 4 (dVP frontier, item 1 — the recentred-ζ CanonicalDecomp): produce the `CanonicalDecomp` of
   `f = ζ(c₀+·)` on `ball 0 R` that `dlvp_zeta_region_of_canonical_decomp` (and `bc_sum_blaschke`) require.

   `bc_sum_blaschke`/`CanonicalDecomp` are centred at `0`, so ζ enters shifted.  Following the corpus
   pattern (`DlvpEntire.zeta_extract_zeros_poles`): `ζ` is analytic on `closedBall c₀ R` (avoiding the
   pole, `zeta_analyticOnNhd_disk`); the shift `w ↦ c₀+w` is analytic and maps `closedBall 0 R` into it,
   so `ζ(c₀+·)` is analytic (hence meromorphic) on `closedBall 0 R`.  Its order is `≠ ⊤` at the centre
   (`ζ(c₀) ≠ 0`, translation-invariant via `meromorphicOrderAt_comp_of_deriv_ne_zero`), hence everywhere
   (connected disk).  `MeromorphicOn.exists_canonicalDecomp` then yields the decomposition.

   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaDisk
import Mathlib

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **The recentred-ζ CanonicalDecomp.**  `∃ g, CanonicalDecomp (fun w => ζ(c₀+w)) g R`. -/
theorem zeta_recentered_canonical_decomp (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (h1 : (1 : ℂ) ∉ closedBall c₀ R) (hc : 1 < c₀.re) :
    ∃ g : ℂ → ℂ, CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R := by
  have hshift_ana : AnalyticOnNhd ℂ (fun w => c₀ + w) (closedBall 0 R) :=
    fun z _ => analyticAt_const.add analyticAt_id
  have hmaps : Set.MapsTo (fun w => c₀ + w) (closedBall (0 : ℂ) R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    rw [mem_closedBall, Complex.dist_eq, add_sub_cancel_left]
    simpa using hw
  have hζ_ana : AnalyticOnNhd ℂ riemannZeta (closedBall c₀ R) := zeta_analyticOnNhd_disk c₀ R h1
  have hana : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (closedBall 0 R) :=
    hζ_ana.comp hshift_ana hmaps
  have hmero := hana.meromorphicOn
  -- order ≠ ⊤ at the centre 0
  have hc0 : c₀ ∈ closedBall c₀ R := mem_closedBall_self hR.le
  have hord_0 : meromorphicOrderAt (fun w => riemannZeta (c₀ + w)) 0 ≠ ⊤ := by
    have hg0 : AnalyticAt ℂ (fun w => c₀ + w) (0 : ℂ) := analyticAt_const.add analyticAt_id
    have hg0' : deriv (fun w => c₀ + w) (0 : ℂ) ≠ 0 := by rw [deriv_const_add']; simp
    have hcomp : (fun w => riemannZeta (c₀ + w)) = riemannZeta ∘ (fun w => c₀ + w) := rfl
    rw [hcomp, meromorphicOrderAt_comp_of_deriv_ne_zero hg0 hg0']
    simp only [Function.comp, add_zero]
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hζ_ana c₀ hc0).meromorphicAt]
    exact ((hζ_ana c₀ hc0).continuousAt.eventually_ne (zeta_ne_zero_of_one_lt_re c₀ hc)).filter_mono
      nhdsWithin_le_nhds
  -- extend to all points via connectedness
  have hconn : IsConnected (closedBall (0 : ℂ) R) :=
    (convex_closedBall 0 R).isConnected ⟨0, mem_closedBall_self hR.le⟩
  have hord : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt (fun w => riemannZeta (c₀ + w)) u ≠ ⊤ :=
    (hmero.exists_meromorphicOrderAt_ne_top_iff_forall hconn).1
      ⟨⟨0, mem_closedBall_self hR.le⟩, hord_0⟩
  exact hmero.exists_canonicalDecomp hord

end ZeroFreeBridge
