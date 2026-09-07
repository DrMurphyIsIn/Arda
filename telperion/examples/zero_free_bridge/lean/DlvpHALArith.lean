/- PHASE 4 (dVP frontier, item 2 — the `hAL` arithmetic packaging): reduce the region theorem's
   `hAL` hypothesis `(∑ |divisor|)/(R-‖w‖) + Bg ≤ A·L` to the three O(L) component bounds plus a
   choice of `A`.

   `dlvp_zeta_region_of_canonical_decomp` (`DlvpZetaCanonical`) takes, at each height, the packed
   hypothesis `hAL : (∑_u |divisor u|)/(R - ‖w‖) + Bg ≤ A·L`.  Its three ingredients are each
   `O(L)`: the zero-count sum `S = ∑ |divisor u| ≤ Ccount·L` (Jensen), the entire-part bound
   `Bg ≤ CBg·L` (`norm_logDeriv_g_le_strip`), and the geometric gap `den = R - ‖w‖ > 0`.  Choosing
   `A ≥ Ccount/den + CBg` closes it.  This packaging is the mechanical last step of item 2 — it
   leaves only "supply the two O(L) constants and pick A" for the final concrete instantiation.

   conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

namespace ZeroFreeBridge

/-- **The `hAL` arithmetic.**  `S/den + Bg ≤ A·L` from the O(L) component bounds `S ≤ Ccount·L`,
    `Bg ≤ CBg·L`, `den > 0`, and the choice `A ≥ Ccount/den + CBg`.  (`S` is the nonnegative zero-
    count sum, `den = R - ‖w‖`, matching the shape of `dlvp_zeta_region_of_canonical_decomp.hAL`.) -/
theorem hAL_arith {S den Bg Ccount CBg L A : ℝ}
    (hScount : S ≤ Ccount * L) (hden0 : 0 < den) (hBg : Bg ≤ CBg * L) (hL0 : 0 ≤ L)
    (hA : Ccount / den + CBg ≤ A) :
    S / den + Bg ≤ A * L := by
  calc S / den + Bg
      ≤ (Ccount * L) / den + CBg * L := by gcongr
    _ = (Ccount / den + CBg) * L := by ring
    _ ≤ A * L := mul_le_mul_of_nonneg_right hA hL0

/-- The zero-count sum `∑ |divisor u|` equals `∑ divisor u` when the divisor is nonnegative (ζ has
    no poles), so the Jensen count `∑ divisor ≤ Ccount·L` feeds `hAL_arith` directly. -/
theorem sum_abs_divisor_eq {ι : Type*} (T : Finset ι) (D : ι → ℤ)
    (hD : ∀ u ∈ T, 0 ≤ D u) :
    ∑ u ∈ T, |(D u : ℝ)| = ∑ u ∈ T, (D u : ℝ) := by
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [abs_of_nonneg (by exact_mod_cast hD u hu)]

end ZeroFreeBridge
