/- PHASE 4 (dVP frontier, the LHS recentring bridge): connect `bc_sum_blaschke`'s output form
   `(-(logDeriv f z)).re` (with `f = ζ(c₀+·)` the recentred ζ) to the `(-deriv ζ w / ζ w).re` form that
   the region skeleton (`DlvpPole.dlvp_region_of_bc_inputs`, `DlvpZetaRegion.dlvp_zeta_region`) consumes.

   `logDeriv (fun w => ζ(c₀+w)) z = logDeriv ζ (c₀+z)` (`DlvpEntirePlumbing.logDeriv_comp_const_add`), and
   `logDeriv ζ w = deriv ζ w / ζ w` by definition, with `-(a/b) = -a/b`.  So the recentred BC-SUM's
   left-hand side is exactly the skeleton's.  This is the last piece of connective tissue between the
   Blaschke BC-SUM and the region skeleton (the remaining work is the Herglotz-sum reindexing, whose
   VALUE is recentring-invariant since `(z-c₀)-(ρ-c₀) = z-ρ`).  conjecture1_proved = False (NOT RH).
-/
import DlvpEntirePlumbing

open Complex

namespace ZeroFreeBridge

/-- **LHS recentring.**  The recentred log-derivative real part equals the skeleton's `-Re(ζ'/ζ)` at the
    shifted point: `(-(logDeriv (fun w => ζ(c₀+w)) z)).re = (-deriv ζ (c₀+z) / ζ (c₀+z)).re`. -/
theorem neg_logDeriv_zeta_recenter_re (c₀ z : ℂ)
    (hf : DifferentiableAt ℂ riemannZeta (c₀ + z)) :
    (-(logDeriv (fun w => riemannZeta (c₀ + w)) z)).re
      = (-deriv riemannZeta (c₀ + z) / riemannZeta (c₀ + z)).re := by
  rw [logDeriv_comp_const_add riemannZeta c₀ z hf]
  simp only [logDeriv, Pi.div_apply, neg_div]

end ZeroFreeBridge
