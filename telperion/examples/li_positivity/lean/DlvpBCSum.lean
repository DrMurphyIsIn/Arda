/- PHASE 4 (dVP frontier, rung 2 COMBINE): the Borel-Caratheodory / Jensen "sum bound"
   step, reduced to its two genuinely-analytic inputs.

   BC-SUM (the sole remaining analytic frontier after rungs 1,3,4,5) is:
       -Re(ζ'/ζ)(s) ≤ A·L - Σ_ρ Re(1/(s-ρ)),   L ~ log|t|.
   The classical (Titchmarsh §3.9) route splits the log-derivative on a disk about `2+iγ`:
       ζ'/ζ(s) = Z + E,   Z = Σ_{ρ near s} 1/(s-ρ)  (Herglotz zero sum),  E = entire part,
   and bounds the entire part `‖E‖ ≤ A·L` via Borel-Caratheodory fed by the crude strip
   bound `|ζ| ≤ C|t|`, with the number of zeros controlled by Jensen.

   `bc_sum_of_split` here is the COMBINE: given that split and `‖E‖ ≤ A·L`, it derives the
   BC-SUM inequality `-Re(ζ'/ζ)(s) ≤ A·L - Re(Z)` — exactly the shape rung 1
   (`hzero_of_herglotz`) and rung 4 (`htwo_of_bound`) consume.  So the WHOLE dVP region now
   reduces to the TWO named analytic inputs below, each backed by a concrete Mathlib API:

     (i)  the partial-fraction SPLIT `ζ'/ζ = Z + E` — Jensen divisor machinery
          (`AnalyticOnNhd.circleAverage_log_norm`, `Mathlib.Analysis.Complex.JensenFormula`);
     (ii) the ENTIRE-PART bound `‖E‖ ≤ A·L` — `borel_caratheodory_deriv`
          (`telperion/examples/borel_caratheodory`) with the zero count from
          `AnalyticOnNhd.sum_divisor_le` (Jensen) and the boundary bound `zeta_strip_bound`.

   Improves the region CONSTANT/rate chain only; NOT a proof of RH.  conjecture1_proved = False.
-/
import DlvpZeroSum

open Complex

namespace ZeroFreeBridge

/-- **BC-SUM COMBINE.**  From the log-derivative split `w = Z + E` with the entire part
    bounded `‖E‖ ≤ A·L`, the BC-SUM inequality `-Re(w) ≤ A·L - Re(Z)` follows: the real part
    of the bounded entire part costs at most `‖E‖ ≤ A·L`.  (`Z` is the Herglotz zero sum,
    `w = ζ'/ζ(s)`.) -/
theorem bc_sum_of_split (w Z E : ℂ) (AL : ℝ) (hw : w = Z + E) (hE : ‖E‖ ≤ AL) :
    (-w).re ≤ AL - Z.re := by
  have h1 : (-w).re = -Z.re - E.re := by rw [hw]; simp; ring
  have h2 : -E.re ≤ ‖E‖ := le_trans (neg_le_abs E.re) (Complex.abs_re_le_norm E)
  rw [h1]; linarith [h2, hE]

/-- The `htwo` background bound directly from the split: when the zero sum has nonnegative
    real part (rung 4, `sum_re_inv_sub_nonneg`), it drops entirely. -/
theorem htwo_of_bc_split (w Z E : ℂ) (AL : ℝ)
    (hw : w = Z + E) (hE : ‖E‖ ≤ AL) (hZ : 0 ≤ Z.re) :
    (-w).re ≤ AL := by
  have := bc_sum_of_split w Z E AL hw hE
  linarith

end ZeroFreeBridge
