/-
  R47 / R5-tie2 brick -- FURTHER double-hub surface-constant tiebreaks, machine-checked in exact
  rational arithmetic.  This is a SECOND batch, distinct from `R47R5TiebreakCert` (which handled the
  symmetric `(ka,kb)=(2,2)` double hub).

  Context (proof/verification/rem_tie.py).  Among de-loaded cherry-bundle configurations at matched
  vertex count, an m-hub backbone contributes a surface constant
      C_m := pi / rho_B^n = Psi_m / rho_B^m,      rho_B := (621/64)^(1/11).
  Single hub:  Psi_1 = 26/23,  so C_1 = (26/23)/rho_B.
  Double hub (ka,kb):  Psi_D(ka,kb) = 1 + ka·zA·z + kb·zB·z + zA·zB + ka·kb·zA·zB·z^2,
      with z = 3/23, zA = 1/(ka+1), zB = 1/(kb+1).

  The tiebreak "two hubs lose to one hub" is C_2 < C_1, which unfolds (clearing the shared 11th root
  rho_B) to the pure rational inequality
      C_2 < C_1  <=>  Psi_D < (26/23)·rho_B  <=>  Psi_D^11 < (26/23)^11 · (621/64).

  This file certifies THREE distinct instances not covered by `R47R5TiebreakCert`:
    * the ASYMMETRIC config (ka,kb) = (2,3):  Psi_D = 2026/1587,  1587 = 3·23^2;
    * the SYMMETRIC config   (ka,kb) = (3,3):  Psi_D = 5365/4232,  4232 = 8·23^2;
    * the CONSTANT-ORDER LIMIT Psi_D -> (26/23)^2 = 676/529 as ka,kb -> inf, whose surface constant
      likewise loses to the single hub.
  Every closed form was verified in exact Python (`fractions.Fraction`) against the permanent before
  being stated here, and each inequality is discharged by `norm_num`.

  Numerically the strict inequalities hold with room:  Psi_D(2,3) = 2026/1587 ~ 1.2766,
  Psi_D(3,3) = 5365/4232 ~ 1.2678, the limit 676/529 ~ 1.2779, all below (26/23)·rho_B ~ 1.4054.

  HONEST SCOPE: this settles further constant-order single-vs-double-hub tiebreaks among de-loaded
  cherry-bundle configurations.  It does NOT prove Conjecture 1 (which still needs Phi<=1 and the
  global structural reduction).  conjecture1_proved stays False (prose only; no `def` here, to avoid
  colliding with the shared-namespace definitions in sibling bricks).  Self-contained: `import Mathlib`.
-/
import Mathlib

namespace R3Cert.Step3

/-- The exact ASYMMETRIC double-hub backbone factor at `(ka,kb) = (2,3)`:
    `Psi_D(2,3) = 1 + 2·(1/3)·(3/23) + 3·(1/4)·(3/23) + (1/3)·(1/4) + 6·(1/3)·(1/4)·(3/23)^2 = 2026/1587`.
    (`1587 = 3·23^2`.) -/
theorem psiD_2_3_value :
    (1 + 2 * (1 / 3) * (3 / 23) + 3 * (1 / 4) * (3 / 23) + (1 / 3) * (1 / 4)
      + 6 * (1 / 3) * (1 / 4) * (3 / 23) ^ 2 : ℚ) = 2026 / 1587 := by
  norm_num

/-- The exact SYMMETRIC double-hub backbone factor at `(ka,kb) = (3,3)`:
    `Psi_D(3,3) = 1 + 3·(1/4)·(3/23) + 3·(1/4)·(3/23) + (1/4)·(1/4) + 9·(1/4)·(1/4)·(3/23)^2 = 5365/4232`.
    (`4232 = 8·23^2`.) -/
theorem psiD_3_3_value :
    (1 + 3 * (1 / 4) * (3 / 23) + 3 * (1 / 4) * (3 / 23) + (1 / 4) * (1 / 4)
      + 9 * (1 / 4) * (1 / 4) * (3 / 23) ^ 2 : ℚ) = 5365 / 4232 := by
  norm_num

/-- **Asymmetric double-hub loses to single hub, cleared of the 11th root** (config `(2,3)`).

    `C_2 < C_1` for `(ka,kb)=(2,3)` reduces, on clearing `rho_B = (621/64)^(1/11)`, to
        `(2026/1587)^11 < (26/23)^11 · (621/64)`
    (i.e. `Psi_D(2,3) < (26/23)·rho_B`).  A pure rational fact, discharged by `norm_num`. -/
theorem double_hub_surface_lt_single_2_3 :
    (2026 / 1587 : ℚ) ^ 11 < (26 / 23 : ℚ) ^ 11 * (621 / 64) := by
  norm_num

/-- **Symmetric double-hub loses to single hub, cleared of the 11th root** (config `(3,3)`).

    `C_2 < C_1` for `(ka,kb)=(3,3)` reduces to
        `(5365/4232)^11 < (26/23)^11 · (621/64)`
    (i.e. `Psi_D(3,3) < (26/23)·rho_B`).  Discharged by `norm_num`. -/
theorem double_hub_surface_lt_single_3_3 :
    (5365 / 4232 : ℚ) ^ 11 < (26 / 23 : ℚ) ^ 11 * (621 / 64) := by
  norm_num

/-- The constant-order LIMIT of the double-hub backbone factor, `Psi_D(ka,kb) -> (26/23)^2` as
    `ka, kb -> inf`, is the exact rational `(26/23)^2 = 676/529`.  (`529 = 23^2`.) -/
theorem psiD_limit_value : (26 / 23 : ℚ) ^ 2 = 676 / 529 := by
  norm_num

/-- **The limiting double-hub surface constant still loses to the single hub, cleared of the 11th root.**

    As `ka, kb -> inf`, `Psi_D -> 676/529`, and the tiebreak `C_2 < C_1` in the limit reduces to
        `(676/529)^11 < (26/23)^11 · (621/64)`
    (i.e. `(26/23)^2 < (26/23)·rho_B`, equivalently the base crux `(26/23)^11 < 621/64`).  So even the
    most favorable double hub -- both hubs saturated with arms -- is beaten by the single hub.
    Discharged by `norm_num`. -/
theorem psiD_limit_surface_lt_single :
    (676 / 529 : ℚ) ^ 11 < (26 / 23 : ℚ) ^ 11 * (621 / 64) := by
  norm_num

end R3Cert.Step3
