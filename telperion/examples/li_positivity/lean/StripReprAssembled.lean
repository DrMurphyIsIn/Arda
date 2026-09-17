/- UNCONDITIONAL strip representation, assembled from the discharged inputs R1 + R2 + R3.

     riemannZeta s = s/(s-1) - s · ∫_{x>1} {x} x^{-(s+1)} dx = stripRHS s,   for s ∈ {0<Re s}\{1}.

   All three inputs of `zeta_fract_repr_of` (the identity-theorem assembly in StripRepr) are now
   kernel-verified:
     R1  `zeta_repr_R1`                    (StripReprR1) -- Abel-summation identity on Re s > 1,
     R2  `differentiableAt_fractIntegral`  (StripReprR2) -- differentiation under the integral,
     R3  `isPreconnected_stripDomain`      (StripReprR3) -- 4-convex-cover preconnectedness.
   Feeding them to `zeta_fract_repr_of` gives the fully-UNCONDITIONAL strip representation on the
   punctured right half-plane.  Together with `zeta_repr_integral_bound` (input B) and
   `zeta_strip_bound_of` (both in ZeroFreeBridge), this closes the crude strip growth bound
   |ζ(σ+it)| ≤ ‖s‖/‖s-1‖ + ‖s‖/σ to a single unconditional input.  Crude growth only (~|t|); NOT
   the sharp |t|^{1-σ} nor the log|t| region rate (which needs the Vinogradov-Korobov machinery
   absent from Mathlib).  A gap-filler FEEDING Layer 2, NOT a proof of RH.  conjecture1_proved = False.
-/
import StripReprR1
import StripReprR2
import StripReprR3

namespace ZeroFreeBridge

/-- The UNCONDITIONAL fractional-part strip representation of `riemannZeta` on the punctured right
    half-plane `stripDomain = {s | 0 < Re s} \ {1}`, assembled from the discharged R1/R2/R3 via
    `zeta_fract_repr_of`.  This is the input (R) that `zeta_strip_bound_of` consumes. -/
theorem zeta_fract_repr {s : ℂ} (hs : s ∈ stripDomain) : riemannZeta s = stripRHS s :=
  zeta_fract_repr_of
    (fun {z} hz => zeta_repr_R1 hz)
    (fun {z} hz => differentiableAt_fractIntegral (show (0 : ℝ) < z.re from hz.1))
    isPreconnected_stripDomain hs

end ZeroFreeBridge
