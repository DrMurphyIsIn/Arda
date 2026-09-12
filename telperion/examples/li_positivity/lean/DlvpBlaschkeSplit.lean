/- PHASE 4 (dVP frontier, BLASCHKE item (d2)): the log-derivative split for the canonical
   decomposition — `logDeriv ζ = Σ (canonical-factor log-derivatives) + logDeriv g`.

   Off the zeros, the codiscrete factorization `f =ᶠ (∏ᶠ canonicalFactor^{-divisor}) • g` upgrades to
   a pointwise log-derivative identity: work on a small CONVEX ball `B(z,ε) ⊆ ball 0 R` that avoids
   the finitely many zeros (extracted from the OPEN set `ball 0 R \ zeros`), where both `f` and the
   Blaschke·g product are analytic (`DlvpBlaschkeProdAnalytic.blaschke_analyticAt` for the Blaschke
   part), then apply the function-agnostic transfer `DlvpTransfer.logDeriv_congr_of_codiscrete`,
   `logDeriv_mul`, and the Blaschke Herglotz sum `DlvpBlaschkeHerglotz.logDeriv_finprod_canonicalFactor`.

     `logDeriv_split_off_zeros` :  for a `CanonicalDecomp f g R` with `f, g` analytic and `g` zero-free,
       at `z ∈ ball 0 R` off the zeros,
         `logDeriv f z = Σ_u (-divisor f (ball 0 R) u)·logDeriv (canonicalFactor R u) z + logDeriv g z`.

   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpBlaschkeHerglotz
import DlvpBlaschkeProdAnalytic
import DlvpTransfer

open Complex Metric MeromorphicOn Filter

namespace ZeroFreeBridge

/-- **(d2) Log-derivative split for the canonical decomposition.**  At `z ∈ ball 0 R` off the zeros,
    `logDeriv f = Σ_u (-divisor u)·logDeriv (canonicalFactor R u) + logDeriv g`. -/
theorem logDeriv_split_off_zeros {f g : ℂ → ℂ} {R : ℝ}
    (D : CanonicalDecomp f g R)
    (hf_ana : AnalyticOnNhd ℂ f (ball 0 R)) (hg_ana : AnalyticOnNhd ℂ g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hzne : ∀ u ∈ hfin.toFinset, z ≠ u) :
    logDeriv f z
      = (∑ u ∈ hfin.toFinset,
          ((-(divisor f (ball 0 R) u) : ℤ) : ℂ) * logDeriv (canonicalFactor R u) z)
        + logDeriv g z := by
  set n : ℂ → ℤ := fun u => -(divisor f (ball 0 R) u) with hn_def
  set B : ℂ → ℂ := ∏ᶠ u, (canonicalFactor R u) ^ (n u) with hB_def
  have hzcb : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
  -- support ⊆ ball.
  have hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) R := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hdu : divisor f (ball 0 R) u ≠ 0 := fun h => hu (by rw [hn_def]; simp [h])
    exact (divisor f (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hdu)
  -- per-factor differentiability and non-vanishing at z.
  have hdiff : ∀ u ∈ hfin.toFinset, DifferentiableAt ℂ (canonicalFactor R u) z := fun u hu =>
    (analyticOnNhd_canonicalFactor R u z (Set.mem_compl_singleton_iff.mpr (hzne u hu))).differentiableAt
  have hne_cf : ∀ u ∈ hfin.toFinset, canonicalFactor R u z ≠ 0 := fun u hu =>
    canonicalFactor_ne_zero (hsupp u hu) hzcb (hzne u hu)
  -- a small convex ball around z inside `ball 0 R` and avoiding the zeros.
  have hopen : IsOpen (ball (0 : ℂ) R \ (↑hfin.toFinset : Set ℂ)) :=
    isOpen_ball.sdiff hfin.toFinset.finite_toSet.isClosed
  have hzmem : z ∈ ball (0 : ℂ) R \ (↑hfin.toFinset : Set ℂ) :=
    ⟨hz, fun hzin => hzne z (Finset.mem_coe.mp hzin) rfl⟩
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hopen z hzmem
  have hUsub : ball z ε ⊆ ball (0 : ℂ) R := fun w hw => (hε_sub hw).1
  have hUavoid : ∀ w ∈ ball z ε, ∀ u ∈ hfin.toFinset, w ≠ u := fun w hw u hu hwu =>
    (hε_sub hw).2 (Finset.mem_coe.mpr (hwu ▸ hu))
  -- `f` and `B • g` are analytic on the small ball.
  have hf_U : AnalyticOnNhd ℂ f (ball z ε) := hf_ana.mono hUsub
  have hsmul : (B • g) = fun w => B w * g w := by funext x; simp [smul_eq_mul]
  have hBg_U : AnalyticOnNhd ℂ (B • g) (ball z ε) := by
    intro w hw
    have hwR : w ∈ ball (0 : ℂ) R := hUsub hw
    have hBw : AnalyticAt ℂ B w :=
      blaschke_analyticAt n hfin (ball_subset_closedBall hwR) hsupp (fun u hu => hUavoid w hw u hu)
    rw [hsmul]
    exact hBw.mul (hg_ana w hwR)
  -- codiscrete factorization restricted to the small ball.
  have hfac_U : f =ᶠ[codiscreteWithin (ball z ε)] (B • g) :=
    D.eventuallyEq.filter_mono (codiscreteWithin_mono (hUsub.trans ball_subset_closedBall))
  -- transfer the log-derivative pointwise.
  have hzU : z ∈ ball z ε := mem_ball_self hε_pos
  have htrans := logDeriv_congr_of_codiscrete hf_U hBg_U isOpen_ball
    (convex_ball z ε).isPreconnected hzU hzU hfac_U
  rw [htrans, hsmul]
  -- split off `g`, then expand the Blaschke product via (d1).
  have hBz_ne : B z ≠ 0 := by
    have hFPz : B z = ∏ u ∈ hfin.toFinset, (canonicalFactor R u z) ^ (n u) := by
      rw [hB_def]
      have hsub : Function.mulSupport (fun u => (canonicalFactor R u) ^ (n u)) ⊆ hfin.toFinset := by
        intro u hu
        rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
        intro hnu; apply hu; funext w; simp [hnu]
      rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_apply]
      rfl
    rw [hFPz]
    exact Finset.prod_ne_zero_iff.mpr (fun u hu => zpow_ne_zero _ (hne_cf u hu))
  have hBz_diff : DifferentiableAt ℂ B z :=
    (blaschke_analyticAt n hfin hzcb hsupp hzne).differentiableAt
  rw [logDeriv_mul z hBz_ne (hg_ne z hz) hBz_diff (hg_ana z hz).differentiableAt]
  congr 1
  rw [hB_def]
  exact logDeriv_finprod_canonicalFactor n hfin z hdiff hne_cf

end ZeroFreeBridge
