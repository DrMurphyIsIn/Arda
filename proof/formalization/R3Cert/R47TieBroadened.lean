/-
  R3Cert.R47TieBroadened -- the BROADENED tie family (M1 of the BG closure plan).

  The correct per-size maximizer candidate (the near-star is refuted for K<23 by
  `nearStar_not_maximal_at_five`): a single hub carrying `(K-m)` load-5 arms + `m` load-4 arms
  + `m` cherries. This file defines the family, its exact `Aobj` closed form (via
  `singleHub_Aobj_formula`), and the trade constants (`114/115`, `473/1311`) driving unimodality.

  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.R47SingleHubFormula
import R3Cert.R47HeadId
import R3Cert.R47HubState

namespace R3Cert
namespace Step3

open RTree

/-- The broadened trade-state: a single hub with `(K-m)` load-5 arms, `m` load-4 arms, `m` cherries. -/
def tieState (K m : ℕ) : List Hub := [(List.replicate (K - m) 5 ++ List.replicate m 4, m)]

/-- The exact trade constants: one `load-5 -> load-4 + cherry` trade multiplies the Ztot product by
    `114/115` and shifts the per-vertex qSum weight by `473/1311`. -/
theorem tie_trade_factor :
    (513 / 80 : ℝ) * (3 / 2) / (621 / 64) = 114 / 115 ∧
      (-(3 / 23 : ℝ) + 3 / 19 + 1 / 3) = 473 / 1311 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **The exact closed form** of the broadened tie's objective (degree `d = K + m`):
    `Aobj = (621/64)^(K-m)·(513/80)^m·(3/2)^m·(1 + qSum/d)`, matching the 3-engine-verified
    `V(K,m)` in `proof/verification/broadened_tie_family.py`. -/
theorem tie_Aobj_eq_V (K m : ℕ) (hmK : m ≤ K) (hpos : 0 < K + m) :
    Aobj (backboneU (tieState K m))
      = (621 / 64 : ℝ) ^ (K - m) * (513 / 80) ^ m * (3 / 2) ^ m
        * (1 + ((((K - m : ℕ) : ℝ) * (3 / (((K + m : ℕ) : ℝ) * 23))
                 + (m : ℝ) * (3 / (((K + m : ℕ) : ℝ) * 19)))
                + (m : ℝ) * (1 / (3 * ((K + m : ℕ) : ℝ))))) := by
  have hlen : (List.replicate (K - m) 5 ++ List.replicate m 4).length = K := by
    simp only [List.length_append, List.length_replicate]; omega
  have hd : 0 < (List.replicate (K - m) 5 ++ List.replicate m 4).length + m := by
    rw [hlen]; exact hpos
  unfold tieState
  rw [singleHub_Aobj_formula _ m hd]
  simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate,
    List.sum_append, List.sum_replicate, List.length_append, List.length_replicate,
    Ztot_armU_five, Ztot_armU_four, nsmul_eq_mul]
  have hne : (K : ℝ) + m ≠ 0 := by
    have h : (0 : ℝ) < (K : ℝ) + m := by exact_mod_cast hpos
    linarith
  push_cast [Nat.cast_sub hmK]
  field_simp [hne]
  ring
