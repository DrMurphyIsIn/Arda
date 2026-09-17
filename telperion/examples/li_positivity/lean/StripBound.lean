/- PHASE 2: the UNCONDITIONAL crude strip growth bound for `riemannZeta`.

     ‖riemannZeta s‖ ≤ ‖s‖/‖s-1‖ + ‖s‖/Re s,     for s ∈ stripDomain = {0 < Re s} \ {1}.

   Assembled from the two now-discharged inputs of `zeta_strip_bound_of` (ZeroFreeBridge):
     input (R)  `zeta_fract_repr`          (StripReprAssembled) -- the fractional-part representation
                                            `ζ(s) = s/(s-1) - s·fractIntegral s`, and
     input (B)  `zeta_repr_integral_bound` (ZeroFreeBridge)     -- `‖fractIntegral s‖ ≤ 1/Re s`.
   `zeta_repr_integral_bound`'s inline integrand is DEFINITIONALLY `fractIntegral s` (StripRepr's def),
   and `stripRHS s` unfolds to `s/(s-1) - s·fractIntegral s`, so the two inputs slot straight in.

   This closes Layer 2's crude magnitude tier to a single UNCONDITIONAL theorem.  Crude growth only
   (grows like `|t|`); NOT the sharp `|t|^{1-σ}` nor the `log|t|` that feeds the zero-free region, and
   the Vinogradov-Korobov rate needs VMVT (absent from Mathlib).  Feeds Layer 3 (the region), NOT a
   proof of RH.  conjecture1_proved = False.
-/
import ZeroFreeBridge
import StripReprAssembled

namespace ZeroFreeBridge

/-- The UNCONDITIONAL crude strip growth bound: on the punctured right half-plane,
    `‖ζ(s)‖ ≤ ‖s‖/‖s-1‖ + ‖s‖/Re s`.  Assembled from input (R) `zeta_fract_repr` and input (B)
    `zeta_repr_integral_bound` via `zeta_strip_bound_of`. -/
theorem zeta_strip_bound {s : ℂ} (hs : s ∈ stripDomain) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have hs0 : 0 < s.re := hs.1
  exact zeta_strip_bound_of (I := fractIntegral s) (zeta_fract_repr hs)
    (zeta_repr_integral_bound hs0)

end ZeroFreeBridge
