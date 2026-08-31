/- PHASE 4 (core): the quantitative de la Vallee Poussin estimate for the zero-free REGION,
   conditional on the Borel-Caratheodory-derived log-derivative bounds.

   From the 3-4-1 positivity `zeta_logDeriv_comb_nonneg` and the three analytic bounds
     -Re(ζ'/ζ)(σ)      ≤ 1/(σ-1) + A       (simple pole at s = 1),
     -Re(ζ'/ζ)(σ+iγ)   ≤ A·L - k/(σ-β)     (a zero of order k ≥ 1 at β+iγ; L ~ log|γ|),
     -Re(ζ'/ζ)(σ+2iγ)  ≤ A·L               (no forced pole),
   the pole contribution of the zero must beat the log-size background:
     4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5·A·L.
   Choosing σ = 1 + c/L then forces β ≤ 1 - c'/L -- the classical zero-free region (the next step).

   The three bounds are the genuine analytic frontier (Borel-Caratheodory applied to `log ζ` on a
   disk, fed by the crude strip bound `zeta_strip_bound`); they are ISOLATED here as explicit
   hypotheses, exactly as `zeta_boundary_contradiction` isolates its residue limits.  This lemma is
   the exact real-inequality CORE that turns them into the region.  It improves the region CONSTANT
   only (the 3-4-1 cosine cone is Fejer-capped), NOT the Vinogradov-Korobov rate, and is NOT a proof
   of RH.  conjecture1_proved = False.
-/
import ZeroFreeBridge

namespace ZeroFreeBridge

/-- de la Vallee Poussin CORE ESTIMATE (conditional on the log-derivative bounds).  Given the 3-4-1
    positivity and the pole/zero/double bounds on `-Re(ζ'/ζ)`, the order-`k` zero at `β+iγ` must
    satisfy `4·(k/(σ-β)) ≤ 3/(σ-1) + 3A + 5·A·L`.  See the file header for how this yields the
    region on optimizing `σ = 1 + c/L`. -/
theorem dlvp_core_estimate (σ t β : ℝ) (k : ℤ) (A L : ℝ) (hσ : 1 < σ)
    (hpole : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hzero : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ A * L - (k : ℝ) / (σ - β))
    (htwo : (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re ≤ A * L) :
    (4 : ℝ) * ((k : ℝ) / (σ - β)) ≤ 3 / (σ - 1) + 3 * A + 5 * (A * L) := by
  have hpos := zeta_logDeriv_comb_nonneg σ t hσ
  nlinarith [hpos, hpole, hzero, htwo]

end ZeroFreeBridge
