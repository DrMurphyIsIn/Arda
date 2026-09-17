/- PHASE 4 (dVP frontier, rung 1): the ZERO-EXTRACTION core of the de la Vallee Poussin
   `hzero` bound.

   `dlvp_core_estimate` (ZeroFreeRegion.lean) is proved but CONDITIONAL on three bounds on
   `-Re(ζ'/ζ)`; the analytic frontier is producing them from Borel-Caratheodory + the
   Hadamard zero-sum.  The `hzero` bound
     -Re(ζ'/ζ)(σ+iγ) ≤ A·L - k/(σ-β)
   has a clean mathematical HEART, isolated here: evaluated at the height of the zero,
   `s - ρ = σ - β` is a POSITIVE REAL (the imaginary parts cancel), so
   `Re(k/(s-ρ)) = k/(σ-β)` EXACTLY (`re_smul_inv_sub_at_equal_height`); and every OTHER
   zero `ρ'` (with `Re ρ' ≤ 1 < σ`) contributes a NONNEGATIVE real part
   (`re_inv_sub_nonneg_of_re_lt`), so it may be dropped from the Herglotz sum.

   `hzero_of_herglotz` combines these: it REDUCES the conditional `hzero` to a single
   Herglotz-form bound `hbound`, which is exactly the Borel-Caratheodory output
     -Re(ζ'/ζ)(s) ≤ A·L - Σ_ρ Re(k_ρ/(s-ρ)).
   This shrinks the dVP frontier for `hzero` to that one sum bound (see the effort spec).
   It improves the region CONSTANT chain only; NOT a proof of RH.  conjecture1_proved = False.
-/
import ZeroFreeBridge

open Complex

namespace ZeroFreeBridge

/-- At the zero's OWN height `s = σ+iγ`, `ρ = β+iγ`, the difference `s-ρ = σ-β` is a REAL
    number (the `iγ` cancels), so `Re(k/(s-ρ)) = k/(σ-β)` EXACTLY.  This is why the de la
    Vallee Poussin argument evaluates the log-derivative at the height of the zero.  Stated
    unconditionally; in use `β < σ` makes `k/(σ-β) > 0` a genuine gain. -/
theorem re_smul_inv_sub_at_equal_height (σ γ β : ℝ) (k : ℝ) :
    (((k : ℂ)) / (((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I))).re = k / (σ - β) := by
  have hsub : ((σ : ℂ) + (γ : ℂ) * I) - ((β : ℂ) + (γ : ℂ) * I) = ((σ - β : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Any zero `ρ'` with `Re ρ' < s.re` contributes a NONNEGATIVE real part at `s`, so it may
    be dropped from the Herglotz sum (for `σ > 1`, every nontrivial zero has `Re ρ' ≤ 1 < σ`). -/
theorem re_inv_sub_nonneg_of_re_lt (s ρ : ℂ) (h : ρ.re < s.re) :
    0 ≤ (1 / (s - ρ)).re := by
  have hz : 0 < (s - ρ).re := by rw [Complex.sub_re]; linarith
  rw [one_div, Complex.inv_re]
  exact div_nonneg hz.le (Complex.normSq_nonneg _)

/-- REDUCTION rung: the dVP `hzero` bound follows from the Herglotz-form bound
    `-Re(ζ'/ζ)(s) ≤ A·L - (Re(k/(s-ρ₀)) + rest)` once the dominant zero `ρ₀=β+iγ` is at the
    height of `s=σ+iγ` and the `rest` (the OTHER zeros' contributions) is `≥ 0` (which it is,
    by `re_inv_sub_nonneg_of_re_lt`).  This isolates the remaining analytic frontier for
    `hzero` to the single Herglotz/Borel-Caratheodory bound `hbound`. -/
theorem hzero_of_herglotz (σ γ β A L k rest : ℝ) (hrest : 0 ≤ rest)
    (hbound : (-deriv riemannZeta ((σ : ℂ) + (γ : ℂ) * I)
                / riemannZeta ((σ : ℂ) + (γ : ℂ) * I)).re
              ≤ A * L - ((((k : ℂ)) / (((σ : ℂ) + (γ : ℂ) * I)
                            - ((β : ℂ) + (γ : ℂ) * I))).re + rest)) :
    (-deriv riemannZeta ((σ : ℂ) + (γ : ℂ) * I)
        / riemannZeta ((σ : ℂ) + (γ : ℂ) * I)).re ≤ A * L - k / (σ - β) := by
  rw [re_smul_inv_sub_at_equal_height σ γ β k] at hbound
  linarith

end ZeroFreeBridge
