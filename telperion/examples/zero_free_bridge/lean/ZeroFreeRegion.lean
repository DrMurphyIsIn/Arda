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
  rw [show (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  linarith [hpos, hpole, hzero, htwo]

/-- REGION GAP (cleared form): with a zero of order `k ≥ 1`, the dlvp core estimate pushes the zero
    left of the 1-line by an explicit amount.  Writing `B = 3A + 5AL` and `δ = σ-1`, cross-multiplied:
      `δ·(1 - δ·B) ≤ (1 - β)·(3 + δ·B)`.
    Dividing by `3 + δB > 0` gives `1 - β ≥ δ(1-δB)/(3+δB)`; optimizing `δ` (max at `δ ≈ 0.464/B`)
    recovers the classical de la Vallee Poussin region `β ≤ 1 - 0.01436/(A·L)` to leading order
    (e.g. `δ = 1/(2B)` gives `β ≤ 1 - 1/(14 B) ≤ 1 - 1/(112·A·L)` for `L ≥ 1`).  The analytic bounds
    feeding `hcore` are the Borel-Caratheodory frontier; this is the exact real-algebra step that
    turns them into the region.  conjecture1_proved = False. -/
theorem dlvp_region_gap (σ β A L : ℝ) (k : ℤ) (hk : 1 ≤ k) (hσ : 1 < σ) (hβσ : β < σ)
    (hcore : (4 : ℝ) * ((k : ℝ) / (σ - β)) ≤ 3 / (σ - 1) + (3 * A + 5 * (A * L))) :
    (σ - 1) * (1 - (σ - 1) * (3 * A + 5 * (A * L)))
      ≤ (1 - β) * (3 + (σ - 1) * (3 * A + 5 * (A * L))) := by
  have hd : (0 : ℝ) < σ - 1 := by linarith
  have hd' : σ - 1 ≠ 0 := hd.ne'
  have hsb : (0 : ℝ) < σ - β := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set B := 3 * A + 5 * (A * L) with hBdef
  -- Clear denominators in `hcore`: `4·k·(σ-1) ≤ (3 + B·(σ-1))·(σ-β)`.
  have lhs_eq : 4 * ((k : ℝ) / (σ - β)) = (4 * (k : ℝ)) / (σ - β) := by ring
  have rhs_eq : 3 / (σ - 1) + B = (3 + B * (σ - 1)) / (σ - 1) := by field_simp; ring
  rw [lhs_eq, rhs_eq, div_le_iff₀ hsb, div_mul_eq_mul_div, le_div_iff₀ hd] at hcore
  -- With `k ≥ 1`: `4·(σ-1) ≤ (3 + B·(σ-1))·(σ-β)`.
  have key : 4 * (σ - 1) ≤ (3 + B * (σ - 1)) * (σ - β) := by nlinarith [hcore, hk1, hd, hsb]
  -- `1 - β = (σ-β) - (σ-1)`, so the cleared gap follows from `key` by a ring identity.
  nlinarith [key, hd, hsb]

end ZeroFreeBridge
