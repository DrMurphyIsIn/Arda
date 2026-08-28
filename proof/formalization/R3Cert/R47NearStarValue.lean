import Mathlib
import R3Cert.R47SingleHubFormula
import R3Cert.R47HeadId
import R3Cert.R47HubState

/-!
  # The exact near-star objective value (the asymptotic Brualdi-Goldwasser tie)

  Computational finding (this session): the fixed-n maximizer of `Aobj = per(L)/∏deg`
  has `Aobj_max(n)/rhoB^n` DECREASING with a damping oscillation to the limit
  `(26/23)/rhoB ≈ 0.9194` as `n → ∞` — a three-regime picture: a small-`n` CHERRY regime
  (`Aobj/rhoB^n ≈ 1.0–1.06`, mod-2 parity oscillation), a transition, and a large-`n` ARM
  regime converging to the near-star tie.  The limit is achieved by the LOAD-5-ARM STAR.

  This file pins that limiting object's objective EXACTLY.  A single hub of `K` load-5 arms
  has, via `singleHub_Aobj_formula` and `armVal(5) = 621/64` (`Ztot_armU_five`):

      Aobj = (∏ 621/64)·(1 + K·3/(K·23)) = (621/64)^K · (26/23),

  a fully RATIONAL value (no `rhoB`), since `621/64 = rhoB^11`.  Its `rhoB`-normalized value
  is `(26/23)/rhoB` — the asymptotic tie constant, the limit of `Aobj_max(n)/rhoB^n`.

  This is the concrete anchor the convergence analysis produces: the exact objective of the
  asymptotic extremizer, in closed rational form, connecting the arm-rate peak
  (`armVal(5) = 621/64`) to the objective tie.  It is a LOWER bound witness for the
  single-hub template max `tmaxHub(1+11K)`.  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

open RTree

/-- **The near-star objective, exact.**  A single hub of `K ≥ 1` load-5 arms has
    `Aobj = (26/23)·(621/64)^K` — fully rational, since `Ztot(dtSub(armU 5)) = 621/64`.
    Normalizing by `rhoB^(usize)` gives the asymptotic tie `(26/23)/rhoB ≈ 0.9194`. -/
theorem nearstar_arms_Aobj (K : ℕ) (hK : 0 < K) :
    Aobj (backboneU [(List.replicate K 5, 0)]) = (26 / 23 : ℝ) * (621 / 64) ^ K := by
  have hlen : (List.replicate K 5).length = K := by simp
  have hd : 0 < (List.replicate K 5).length + 0 := by rw [hlen]; exact hK
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [singleHub_Aobj_formula (List.replicate K 5) 0 hd]
  simp only [List.length_replicate, List.map_replicate, List.prod_replicate,
    List.sum_replicate, Ztot_armU_five, nsmul_eq_mul, Nat.add_zero, Nat.cast_zero,
    zero_mul, add_zero, pow_zero, mul_one]
  push_cast
  field_simp
  ring

end Step3
end R3Cert
