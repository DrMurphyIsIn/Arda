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

/-- The `(1 + qSum/d)` weight factor of the tie value (so `Aobj = <power product> * tieQ`). -/
noncomputable def tieQ (K m : ℕ) : ℝ :=
  1 + ((((K - m : ℕ) : ℝ) * (3 / (((K + m : ℕ) : ℝ) * 23))
        + (m : ℝ) * (3 / (((K + m : ℕ) : ℝ) * 19))) + (m : ℝ) * (1 / (3 * ((K + m : ℕ) : ℝ))))

theorem tie_Aobj_factored (K m : ℕ) (hmK : m ≤ K) (hpos : 0 < K + m) :
    Aobj (backboneU (tieState K m))
      = (621 / 64 : ℝ) ^ (K - m) * (513 / 80) ^ m * (3 / 2) ^ m * tieQ K m := by
  rw [tie_Aobj_eq_V K m hmK hpos, tieQ]

/-- **Trade-step comparison** (the atom for the trade unimodality / m-argmax): trading a load-5 arm
    for a load-4 arm + a cherry is `Aobj`-non-increasing at `m` iff the exact `114/115`-weighted
    rational condition on the `tieQ` factors holds.  The power product at `m+1` is exactly `114/115`
    times the product at `m` (by `tie_trade_factor`), so the objective comparison collapses to the
    `tieQ` comparison. -/
theorem tie_trade_le (K m : ℕ) (hm1K : m + 1 ≤ K) (hpos : 0 < K + m) :
    Aobj (backboneU (tieState K (m + 1))) ≤ Aobj (backboneU (tieState K m))
      ↔ (114 / 115 : ℝ) * tieQ K (m + 1) ≤ tieQ K m := by
  have hmK : m ≤ K := by omega
  have hpos1 : 0 < K + (m + 1) := by omega
  have hprod : (621 / 64 : ℝ) ^ (K - (m + 1)) * (513 / 80) ^ (m + 1) * (3 / 2) ^ (m + 1)
      = (114 / 115) * ((621 / 64 : ℝ) ^ (K - m) * (513 / 80) ^ m * (3 / 2) ^ m) := by
    rw [show K - m = (K - (m + 1)) + 1 from by omega, pow_succ, pow_succ, pow_succ]
    ring
  rw [tie_Aobj_factored K m hmK hpos, tie_Aobj_factored K (m + 1) (by omega) hpos1, hprod]
  set Q := (621 / 64 : ℝ) ^ (K - m) * (513 / 80) ^ m * (3 / 2) ^ m with hQ
  have hQpos : (0 : ℝ) < Q := by rw [hQ]; positivity
  constructor
  · intro h
    have h2 : Q * ((114 / 115 : ℝ) * tieQ K (m + 1)) ≤ Q * tieQ K m := by
      have e : Q * ((114 / 115 : ℝ) * tieQ K (m + 1)) = 114 / 115 * Q * tieQ K (m + 1) := by ring
      rw [e]; exact h
    exact le_of_mul_le_mul_left h2 hQpos
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h hQpos.le
    have e : 114 / 115 * Q * tieQ K (m + 1) = Q * ((114 / 115 : ℝ) * tieQ K (m + 1)) := by ring
    rw [e]; exact h2

/-- **The trade condition in POLYNOMIAL form** (`d = K+m`): trading a load-5 arm for a load-4 arm +
    a cherry does NOT increase `Aobj` at `m` iff the exact integer-coefficient polynomial inequality
    `203376·(K+m) ≤ (1482K + 1784m)·(K+m+115)` holds.  The `m`-argmax / unimodality reduces to
    analyzing this quadratic; the `m=0` threshold is exactly `K = 23` (matching
    `broadened_tie_family.py`'s `m(K)`, near-star optimal iff `K ≥ 23`). -/
theorem tie_trade_le_poly (K m : ℕ) (hm1K : m + 1 ≤ K) (hpos : 0 < K + m) :
    Aobj (backboneU (tieState K (m + 1))) ≤ Aobj (backboneU (tieState K m))
      ↔ (203376 : ℝ) * ((K : ℝ) + m) ≤ (1482 * (K : ℝ) + 1784 * m) * ((K : ℝ) + m + 115) := by
  rw [tie_trade_le K m hm1K hpos]
  have hmK : m ≤ K := by omega
  have hd : (0 : ℝ) < (K : ℝ) + m := by exact_mod_cast hpos
  have hd1 : (0 : ℝ) < (K : ℝ) + m + 1 := by linarith
  have hdne : (K : ℝ) + m ≠ 0 := ne_of_gt hd
  have hd1ne : (K : ℝ) + m + 1 ≠ 0 := ne_of_gt hd1
  simp only [tieQ]
  push_cast [Nat.cast_sub hmK, Nat.cast_sub hm1K]
  constructor
  · intro h
    field_simp at h
    nlinarith [h, hd, hd1, mul_pos hd hd1]
  · intro h
    field_simp
    nlinarith [h, hd, hd1, mul_pos hd hd1]

end Step3
end R3Cert
