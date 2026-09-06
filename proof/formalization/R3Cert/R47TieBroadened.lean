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

/-- A GENERAL Balanced single hub: `a` load-5 arms, `b` load-4 arms, `c` cherries. -/
def hubState (a b c : ℕ) : List Hub := [(List.replicate a 5 ++ List.replicate b 4, c)]

/-- **Exact closed form of the general Balanced single hub** (degree `d = a+b+c`):
    `Aobj = (621/64)^a·(513/80)^b·(3/2)^c·(1 + qSum/d)`.  The foundation for the M3 joint single-hub
    optimum: `tieState K m = hubState (K-m) m m` (the `a+b=K, c=b` slice). -/
theorem hub_Aobj_eq (a b c : ℕ) (hpos : 0 < a + b + c) :
    Aobj (backboneU (hubState a b c))
      = (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c
        * (1 + (((a : ℝ) * (3 / (((a + b + c : ℕ) : ℝ) * 23))
                 + (b : ℝ) * (3 / (((a + b + c : ℕ) : ℝ) * 19)))
                + (c : ℝ) * (1 / (3 * ((a + b + c : ℕ) : ℝ))))) := by
  have hlen : (List.replicate a 5 ++ List.replicate b 4).length = a + b := by
    simp only [List.length_append, List.length_replicate]
  have hd : 0 < (List.replicate a 5 ++ List.replicate b 4).length + c := by
    rw [hlen]; omega
  have hne : (a : ℝ) + b + c ≠ 0 := by
    have h : (0 : ℝ) < (a : ℝ) + b + c := by exact_mod_cast hpos
    linarith
  unfold hubState
  rw [singleHub_Aobj_formula _ c hd]
  simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate,
    List.sum_append, List.sum_replicate, List.length_append, List.length_replicate,
    Ztot_armU_five, Ztot_armU_four, nsmul_eq_mul]
  push_cast
  field_simp [hne]
  ring

/-- The `(1 + qSum/d)` weight factor of a general single hub `(a,b,c)`. -/
noncomputable def hubQ (a b c : ℕ) : ℝ :=
  1 + (((a : ℝ) * (3 / (((a + b + c : ℕ) : ℝ) * 23)) + (b : ℝ) * (3 / (((a + b + c : ℕ) : ℝ) * 19)))
       + (c : ℝ) * (1 / (3 * ((a + b + c : ℕ) : ℝ))))

theorem hub_Aobj_factored (a b c : ℕ) (hpos : 0 < a + b + c) :
    Aobj (backboneU (hubState a b c))
      = (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c * hubQ a b c := by
  rw [hub_Aobj_eq a b c hpos, hubQ]

/-- **Bulk-swap comparison (the t-axis atom)**: one bulk swap replaces 9 load-5 arms by 11 load-4
    arms (size-preserving), multiplying the power product by exactly `F = (513/80)^11/(621/64)^9`.
    So the objective comparison collapses to the `hubQ` comparison — the exact analog of
    `tie_trade_le` for the second (arm-count) axis of the joint single-hub optimum. -/
theorem hub_bulk_le (a b c : ℕ) (ha : 9 ≤ a) (hpos : 0 < a + b + c) :
    Aobj (backboneU (hubState (a - 9) (b + 11) c)) ≤ Aobj (backboneU (hubState a b c))
      ↔ ((513 / 80 : ℝ) ^ 11 / (621 / 64) ^ 9) * hubQ (a - 9) (b + 11) c ≤ hubQ a b c := by
  have hpos' : 0 < (a - 9) + (b + 11) + c := by omega
  have hprod : (621 / 64 : ℝ) ^ (a - 9) * (513 / 80) ^ (b + 11) * (3 / 2) ^ c
      = ((513 / 80 : ℝ) ^ 11 / (621 / 64) ^ 9)
        * ((621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c) := by
    have hae : (621 / 64 : ℝ) ^ a = (621 / 64) ^ (a - 9) * (621 / 64) ^ 9 := by
      rw [← pow_add, Nat.sub_add_cancel ha]
    have hbe : (513 / 80 : ℝ) ^ (b + 11) = (513 / 80) ^ b * (513 / 80) ^ 11 := pow_add _ _ _
    have h9 : (621 / 64 : ℝ) ^ 9 ≠ 0 := by positivity
    rw [hae, hbe]
    field_simp
  rw [hub_Aobj_factored a b c hpos, hub_Aobj_factored (a - 9) (b + 11) c hpos', hprod]
  set P := (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  set F := (513 / 80 : ℝ) ^ 11 / (621 / 64) ^ 9 with hF
  constructor
  · intro h
    have h2 : P * (F * hubQ (a - 9) (b + 11) c) ≤ P * hubQ a b c := by
      have e : P * (F * hubQ (a - 9) (b + 11) c) = F * P * hubQ (a - 9) (b + 11) c := by ring
      rw [e]; exact h
    exact le_of_mul_le_mul_left h2 hPpos
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h hPpos.le
    have e : F * P * hubQ (a - 9) (b + 11) c = P * (F * hubQ (a - 9) (b + 11) c) := by ring
    rw [e]; exact h2

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

/-- The polynomial "trade doesn't help" predicate `203376(K+m) ≤ (1482K+1784m)(K+m+115)`. -/
def tradeStop (K m : ℕ) : Prop :=
  (203376 : ℝ) * ((K : ℝ) + m) ≤ (1482 * (K : ℝ) + 1784 * m) * ((K : ℝ) + m + 115)

/-- **Upward closure of `tradeStop`**: once trading a load-5 arm for a load-4 arm + cherry stops
    helping, it stays stopped (`RHS` grows by `3266K+3568m+206944 > 203376 = LHS` growth).  Hence
    `V(K,·)` is UNIMODAL in `m` (increasing while `¬tradeStop`, non-increasing while `tradeStop`),
    so its argmax is the least `m` with `tradeStop K m`. -/
theorem tradeStop_persists (K m : ℕ) (h : tradeStop K m) : tradeStop K (m + 1) := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  simp only [tradeStop] at h ⊢
  push_cast
  nlinarith [h, hK, hm, mul_nonneg hK hm]

/-- If the trade still helps at `j` (`¬tradeStop`), the objective strictly increases: `V(j) ≤ V(j+1)`. -/
theorem tie_step_up (K j : ℕ) (hjK : j + 1 ≤ K) (hpos : 0 < K + j) (h : ¬ tradeStop K j) :
    Aobj (backboneU (tieState K j)) ≤ Aobj (backboneU (tieState K (j + 1))) := by
  have hiff := tie_trade_le_poly K j hjK hpos
  have hnot : ¬ (Aobj (backboneU (tieState K (j + 1))) ≤ Aobj (backboneU (tieState K j))) :=
    fun hle => h (hiff.mp hle)
  linarith [not_le.mp hnot]

/-- Once the trade stops helping (`tradeStop`), the objective is non-increasing: `V(j+1) ≤ V(j)`. -/
theorem tie_step_down (K j : ℕ) (hjK : j + 1 ≤ K) (hpos : 0 < K + j) (h : tradeStop K j) :
    Aobj (backboneU (tieState K (j + 1))) ≤ Aobj (backboneU (tieState K j)) :=
  (tie_trade_le_poly K j hjK hpos).mpr h

/-- **Increasing chain** on the trade-helps region: if the trade helps at every `i ∈ [a, b)`, then
    `V(a) ≤ V(b)`. -/
theorem tie_up_chain (K a : ℕ) (hK : 0 < K) :
    ∀ b, a ≤ b → b ≤ K → (∀ i, a ≤ i → i < b → ¬ tradeStop K i) →
      Aobj (backboneU (tieState K a)) ≤ Aobj (backboneU (tieState K b)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _ _; exact le_refl _
  | succ b hab ih =>
      intro hbK hlt
      have h1 := ih (by omega) (fun i hi hib => hlt i hi (by omega))
      have h2 := tie_step_up K b (by omega) (by omega) (hlt b hab (by omega))
      linarith

/-- **Non-increasing chain** past the trade-stop threshold: if the trade has stopped at `mstar`, then
    for every `b ≥ mstar` (with `b ≤ K`), `V(b) ≤ V(mstar)`. -/
theorem tie_down_chain (K mstar : ℕ) (hstop : tradeStop K mstar) :
    ∀ b, mstar ≤ b → b ≤ K → Aobj (backboneU (tieState K b)) ≤ Aobj (backboneU (tieState K mstar)) := by
  intro b hmb
  induction b, hmb using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ b hmb ih =>
      intro hbK
      have hstopb : tradeStop K b := by
        clear ih hbK
        induction b, hmb using Nat.le_induction with
        | base => exact hstop
        | succ b hmb ih2 => exact tradeStop_persists K b ih2
      have h2 := tie_step_down K b (by omega) (by omega) hstopb
      have h1 := ih (by omega)
      linarith

/-- **The m-argmax / unimodal maximum** (the M3 precursor): given `mstar` is the least trade-count
    where the trade stops helping (`tradeStop K mstar`, and `¬tradeStop` below it), the tie value at
    `mstar` dominates every trade count `m ≤ K`.  So `tieState K mstar` is the maximizer over the
    trade family. -/
theorem tie_maximal_over_trades (K mstar : ℕ) (hK : 0 < K) (hmstarK : mstar ≤ K)
    (hstop : tradeStop K mstar) (hlt : ∀ i, i < mstar → ¬ tradeStop K i) :
    ∀ m, m ≤ K → Aobj (backboneU (tieState K m)) ≤ Aobj (backboneU (tieState K mstar)) := by
  intro m hmK
  by_cases hle : m ≤ mstar
  · exact tie_up_chain K m hK mstar hle hmstarK (fun i hi hib => hlt i hib)
  · exact tie_down_chain K mstar hstop m (by omega) hmK

end Step3
end R3Cert
