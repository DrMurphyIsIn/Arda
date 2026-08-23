/-
  R47 / R5-tiebreak brick -- the DOUBLE-HUB-vs-SINGLE-HUB surface-constant comparison,
  machine-checked in exact rational arithmetic.

  Context (proof/verification/rem_tie.py).  Among de-loaded cherry-bundle configurations at
  matched vertex count, an m-hub backbone contributes a surface constant
      C_m := pi / rho_B^n = Psi_m / rho_B^m,      rho_B := (621/64)^(1/11).
  Single hub:  Psi_1 = 26/23,  so C_1 = (26/23)/rho_B.
  Double hub (ka,kb):  Psi_D(ka,kb) = 1 + ka zA z + kb zB z + zA zB + ka kb zA zB z^2,
      with z = 3/23, zA = 1/(ka+1), zB = 1/(kb+1).  At (ka,kb)=(2,2):  Psi_D = 6154/4761.

  The tiebreak says the double hub STRICTLY LOSES to the single hub: C_2 < C_1.  Unfolding,
      C_2 < C_1  <=>  Psi_D / rho_B^2 < (26/23) / rho_B
                 <=>  Psi_D < (26/23) * rho_B
                 <=>  Psi_D^11 < (26/23)^11 * rho_B^11 = (26/23)^11 * (621/64)   [clearing the 11th root].
  For the exact configuration (ka,kb)=(2,2) this is a pure closed rational inequality
      (6154/4761)^11 < (26/23)^11 * (621/64),
  verified in exact Python (Fraction) arithmetic before being stated here and discharged by `norm_num`.

  This is DISTINCT from `R3Cert.ExactCruxes.r5_crux` (which is the base crux `(26/23)^11 < 621/64`,
  i.e. `26/23 < rho_B` alone): here we compare a concrete double-hub backbone factor `Psi_D(2,2)`
  against the single-hub factor scaled by one extra rho_B, encoding "two hubs lose to one hub" rather
  than the bare `C_1 < 1`.

  HONEST SCOPE: this settles the constant-order single-vs-double-hub tiebreak at the (2,2) config among
  de-loaded cherry-bundle configurations.  It does NOT prove Conjecture 1 (which still needs Phi<=1 and
  the global structural reduction).  `conjecture1_proved = False`.  Self-contained: `import Mathlib` only.
-/
import Mathlib

namespace R3Cert.Step3

/-- The exact double-hub backbone factor at `(ka,kb) = (2,2)`:
    `Psi_D(2,2) = 1 + 2·(1/3)·(3/23) + 2·(1/3)·(3/23) + (1/3)·(1/3) + 4·(1/3)·(1/3)·(3/23)^2 = 6154/4761`.
    (`4761 = 3^2 · 23^2`.) -/
theorem psiD_2_2_value :
    (1 + 2 * (1 / 3) * (3 / 23) + 2 * (1 / 3) * (3 / 23) + (1 / 3) * (1 / 3)
      + 4 * (1 / 3) * (1 / 3) * (3 / 23) ^ 2 : ℚ) = 6154 / 4761 := by
  norm_num

/-- **The double-hub-loses-to-single-hub tiebreak, cleared of the 11th root** (config `(2,2)`).

    `C_2 < C_1` for the double hub `(ka,kb)=(2,2)` versus the single hub reduces, on clearing
    `rho_B = (621/64)^(1/11)`, to the closed rational inequality
        `(6154/4761)^11 < (26/23)^11 · (621/64)`
    (i.e. `Psi_D(2,2) < (26/23)·rho_B`).  A pure rational fact, discharged by `norm_num`. -/
theorem double_hub_surface_lt_single :
    (6154 / 4761 : ℚ) ^ 11 < (26 / 23 : ℚ) ^ 11 * (621 / 64) := by
  norm_num

/-- Sanity companion: the double-hub factor `Psi_D(2,2) = 6154/4761` strictly exceeds the single-hub
    factor `Psi_1 = 26/23` at the raw (un-scaled) level, so the strict loss `C_2 < C_1` genuinely comes
    from the extra `rho_B` denominator, not from the backbone factor being smaller.  (`6154·23 < 4761·26`
    is FALSE; the inequality flips the other way.) -/
theorem psiD_2_2_gt_single : (26 / 23 : ℚ) < 6154 / 4761 := by
  norm_num

end R3Cert.Step3
