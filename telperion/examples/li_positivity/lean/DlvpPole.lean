/- PHASE 4 (dVP frontier, rungs 3-5): the pole bound `hpole`, the double bound `htwo`,
   and the REGION ASSEMBLY.

   `dlvp_core_estimate` (ZeroFreeRegion.lean) is conditional on three bounds on `-Re(ζ'/ζ)`;
   `DlvpZeroSum.lean` (rung 1) reduced `hzero` to a Herglotz/Borel-Caratheodory sum bound.
   This file reduces the other two and assembles the region:

   * `hpole` — the pole term `1/(s-1)` at REAL argument σ is exactly `1/(σ-1)`
     (`re_inv_sub_one_at_real`); off-axis it is bounded by `1/(σ-1)` and nonneg
     (`re_inv_sub_one_le`, `re_inv_sub_one_nonneg`).  `hpole_of_partialfraction` reduces
     the conditional `hpole` to the partial-fraction bound.
   * `htwo` — the zero sum is NONNEGATIVE (`sum_re_inv_sub_nonneg`, via rung 1's per-term
     lemma), so it drops (`htwo_of_bound`), leaving the `A·L` background.
   * `dlvp_region_of_bc_inputs` — chains rungs 1/3/4 into `dlvp_core_estimate` then
     `dlvp_region_gap`, so the WHOLE de la Vallee Poussin region reduces to the three
     Borel-Caratheodory inputs (the pole partial-fraction bound + the two Herglotz/BC sum
     bounds).  The sole remaining analytic frontier is BC-SUM itself (rung 2).

   Improves the region CONSTANT only; NOT a proof of RH.  conjecture1_proved = False.
-/
import DlvpZeroSum
import ZeroFreeRegion

open Complex

namespace ZeroFreeBridge

/-! ### Rung 3 — the pole term `1/(s-1)` -/

/-- At a REAL argument σ the pole term is real: `Re(1/((σ:ℂ)-1)) = 1/(σ-1)`. -/
theorem re_inv_sub_one_at_real (σ : ℝ) :
    (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
  have h : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div, Complex.ofReal_re]

/-- The pole term has NONNEGATIVE real part for `Re s > 1`. -/
theorem re_inv_sub_one_nonneg (s : ℂ) (hσ : 1 < s.re) :
    0 ≤ (1 / (s - 1)).re := by
  have hz : 0 < (s - 1).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  rw [one_div, Complex.inv_re]
  exact div_nonneg hz.le (Complex.normSq_nonneg _)

/-- The pole bound `Re(1/(s-1)) ≤ 1/(σ-1)` for `σ = Re s > 1` (the imaginary part only
    shrinks the real part). -/
theorem re_inv_sub_one_le (s : ℂ) (hσ : 1 < s.re) :
    (1 / (s - 1)).re ≤ 1 / (s.re - 1) := by
  have hre : (s - 1).re = s.re - 1 := by rw [Complex.sub_re, Complex.one_re]
  have hpos : 0 < s.re - 1 := by linarith
  have hns : Complex.normSq (s - 1) = (s.re - 1) ^ 2 + (s - 1).im ^ 2 := by
    rw [Complex.normSq_apply, hre]; ring
  have hrw : (s.re - 1) / ((s.re - 1) ^ 2) = 1 / (s.re - 1) := by
    rw [pow_two, ← div_div, div_self hpos.ne']
  rw [one_div, Complex.inv_re, hre, ← hrw]
  gcongr
  rw [hns]; nlinarith [sq_nonneg (s - 1).im]

/-- REDUCTION rung 3 (`hpole`): the pole bound of `dlvp_core_estimate` follows from the
    partial-fraction bound `-Re(ζ'/ζ)(σ) ≤ Re(1/(σ-1)) + A` by evaluating the pole term at
    the real argument. -/
theorem hpole_of_partialfraction (σ A : ℝ)
    (hbound : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
              ≤ (1 / ((σ : ℂ) - 1)).re + A) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A := by
  rwa [re_inv_sub_one_at_real σ] at hbound

/-! ### Rung 4 — the double bound `htwo` (drop the nonnegative zero sum) -/

/-- The Herglotz zero sum `Σ_ρ Re(1/(s-ρ))` is NONNEGATIVE when every zero has `Re ρ < Re s`
    (true for `σ > 1`), so it may be dropped — the content behind `htwo`.  Uses rung 1's
    per-term `re_inv_sub_nonneg_of_re_lt`. -/
theorem sum_re_inv_sub_nonneg (s : ℂ) (Z : Finset ℂ) (h : ∀ ρ ∈ Z, ρ.re < s.re) :
    0 ≤ (∑ ρ ∈ Z, 1 / (s - ρ)).re := by
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun ρ hρ => re_inv_sub_nonneg_of_re_lt s ρ (h ρ hρ)

/-- REDUCTION rung 4 (`htwo`): dropping a nonnegative remainder from the Borel-Caratheodory
    bound at height `2γ` leaves the `A·L` background. -/
theorem htwo_of_bound (x AL rest : ℝ) (hrest : 0 ≤ rest) (h : x ≤ AL - rest) : x ≤ AL := by
  linarith

/-! ### Rung 5 — the region assembly from the three Borel-Caratheodory inputs -/

/-- **REGION ⟸ Borel-Caratheodory inputs.**  Given the three inputs the analytic frontier
    must supply — the partial-fraction pole bound (`hpole_pf`, reduced by rung 3), the
    reduced Herglotz zero bound at height `t` (`hzero`, the output of rung 1's
    `hzero_of_herglotz`), and the Borel-Caratheodory bound at height `2t` (`htwo_bc`,
    nonnegative rest dropped by rung 4) — the cleared de la Vallee Poussin region gap
    follows, via `dlvp_core_estimate` → `dlvp_region_gap`.  Composed with rung 1, the WHOLE
    region reduces to producing those bounds, i.e. to BC-SUM (rung 2). -/
theorem dlvp_region_of_bc_inputs (σ t β A L : ℝ) (k : ℤ)
    (hk : 1 ≤ k) (hσ : 1 < σ) (hβσ : β < σ)
    (hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
                ≤ (1 / ((σ : ℂ) - 1)).re + A)
    (hzero : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
              ≤ A * L - (k : ℝ) / (σ - β))
    (rest₂ : ℝ) (hr₂ : 0 ≤ rest₂)
    (htwo_bc : (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
                  / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
                ≤ A * L - rest₂) :
    (σ - 1) * (1 - (σ - 1) * (3 * A + 5 * (A * L)))
      ≤ (1 - β) * (3 + (σ - 1) * (3 * A + 5 * (A * L))) := by
  have hpole := hpole_of_partialfraction σ A hpole_pf
  have htwo := htwo_of_bound _ (A * L) rest₂ hr₂ htwo_bc
  have hcore := dlvp_core_estimate σ t β k A L hσ hpole hzero htwo
  have hcore' : (4 : ℝ) * ((k : ℝ) / (σ - β))
      ≤ 3 / (σ - 1) + (3 * A + 5 * (A * L)) := by linarith [hcore]
  exact dlvp_region_gap σ β A L k hk hσ hβσ hcore'

end ZeroFreeBridge
