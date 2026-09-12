/- PHASE 4 (dVP frontier, item (B) — the recentring equivalence for hbc₂): the c₀- and c₁-recentred
   `-logDeriv ζ` at a point `s` have equal real part (both = `Re(-ζ'/ζ(s))`).

   dlvp_zeta_region_of_bc_sums states hbc₂ in terms of `logDeriv(ζ(c₀+·))` (the SAME c₀=2+iγ as hbc₁),
   but the height-2γ eval point `σ+2iγ` is ≈|γ| from c₀, so its bound must be proved on the PARALLEL
   disk c₁=2+2iγ (where σ+2iγ is at distance 2-σ).  This lemma bridges: a bound on the c₁-recentred
   `-logDeriv` transfers to hbc₂'s c₀-recentred form, via `neg_logDeriv_zeta_recenter_re` at both
   centres (both collapse to `Re(-deriv ζ s/ζ s)`).  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaRecenter
open Complex

namespace ZeroFreeBridge

/-- **Recentring equivalence.**  The `c₀`- and `c₁`-recentred `-logDeriv ζ` at `s` agree (both equal
    `Re(-ζ'/ζ(s))`) — so a bound proved on the c₁=2+2iγ disk feeds hbc₂'s c₀=2+iγ form. -/
theorem neg_logDeriv_recenter_eq (c₀ c₁ s : ℂ) (hf : DifferentiableAt ℂ riemannZeta s) :
    (-(logDeriv (fun w => riemannZeta (c₀ + w)) (s - c₀))).re
      = (-(logDeriv (fun w => riemannZeta (c₁ + w)) (s - c₁))).re := by
  have e0 : c₀ + (s - c₀) = s := by ring
  have e1 : c₁ + (s - c₁) = s := by ring
  rw [neg_logDeriv_zeta_recenter_re c₀ (s - c₀) (e0.symm ▸ hf),
      neg_logDeriv_zeta_recenter_re c₁ (s - c₁) (e1.symm ▸ hf), e0, e1]

end ZeroFreeBridge
