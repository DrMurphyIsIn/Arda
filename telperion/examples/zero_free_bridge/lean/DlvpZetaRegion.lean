/- PHASE 4 (dVP frontier, the REGION CAPSTONE): the de la Vallée Poussin zero-free region
   `β ≤ 1 - c/(A·L)` from the three Borel–Carathéodory inputs, at the OPTIMAL width `σ - 1 = 1/(2B)`.

   `DlvpPole.dlvp_region_of_bc_inputs` turns the three inputs (pole `hpole_pf`, zero-height `hzero`,
   double-height `htwo_bc`) at a width `σ > 1` into the cleared region GAP.  `DlvpRegionBound.
   dlvp_region_bound` optimizes the gap at `σ - 1 = 1/(2B)`, `B = 3A + 5AL`, into `β ≤ 1 - 1/(112 A L)`.
   This capstone chains them: it is the dVP region theorem, reduced to the three BC inputs (which
   `bc_sum_blaschke` + the Herglotz lower bound + the interior entire-part bound + rung 3 supply).

   conjecture1_proved = False (NOT a proof of RH — the region constant is improved from the polylog one).
-/
import DlvpPole
import DlvpRegionBound

open Complex

namespace ZeroFreeBridge

/-- **The de la Vallée Poussin region, from the three BC inputs.**  At the optimal width
    `σ - 1 = 1/(2B)` (`B = 3A + 5AL`), the pole / zero-height / double-height Borel–Carathéodory bounds
    on `-Re(ζ'/ζ)` force the zero `β = Re ρ₀` off the line by `β ≤ 1 - 1/(112·A·L)` (`= 1 - c/log|t|`). -/
theorem dlvp_zeta_region (σ A L β t : ℝ) (k : ℤ) (hA : 0 < A) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L)))) (hβσ : β < σ)
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    (hzero : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
              ≤ A * L - (k : ℝ) / (σ - β))
    (rest₂ : ℝ) (hr₂ : 0 ≤ rest₂)
    (htwo_bc : (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                  / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
                ≤ A * L - rest₂) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  have hAL : 0 < A * L := mul_pos hA (by linarith)
  have hBpos : 0 < 3 * A + 5 * (A * L) := by nlinarith
  have hδpos : 0 < σ - 1 := by rw [hσ_opt]; positivity
  have hσ1 : 1 < σ := by linarith
  -- the region gap from the three BC inputs
  have hgap := dlvp_region_of_bc_inputs σ t β A L k hk hσ1 hβσ hpole_pf hzero rest₂ hr₂ htwo_bc
  -- the optimal choice δ = σ - 1 = 1/(2B) makes δ·B = 1/2
  have hδB : (σ - 1) * (3 * A + 5 * (A * L)) = 1 / 2 := by rw [hσ_opt]; field_simp
  exact dlvp_region_bound A L β (σ - 1) hA hL hδpos hδB hgap

end ZeroFreeBridge
