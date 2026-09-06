/-
  R3Cert.R47SingleHub2D -- M3 of the BG closure plan: the single-hub 2-D envelope.

  A general Balanced single hub `hubState a b c` (a load-5 arms, b load-4 arms, c cherries) at aligned
  size `11a+9b+2c = 11K` is, along the size-preserving BULK swap (9 load-5 -> 11 load-4, `hub_bulk_le`),
  the column `colState K c t = hubState (K-c-9t) (c+11t) c`, t >= 0, whose t=0 edge is the tie/trade
  family `tieState K c`.  This file proves the T-AXIS half: each column is unimodal in `t` (the
  `hub_bulk_le` analog of the proven `tie_*` trade machinery), so its maximum is at the least `t` where
  the bulk swap stops helping (`bulkStop`).  Combined (elsewhere) with the c-envelope + finite interior
  patch (5 <= K < 22) this gives `singleHub_le_tie`.

  The `bulkStop` polynomial (22-digit coefficients, factor F = (513/80)^11/(621/64)^9) and its upward
  persistence are cross-checked exactly in proof/verification/broadened_tie_2d_envelope.py.

  `conjecture1_proved = False`.  Self-contained leaf: imported by nothing; built as an explicit CI target.
-/
import Mathlib
import R3Cert.R47TieBroadened

namespace R3Cert
namespace Step3

open RTree

/-- The bulk column at aligned size `11K`, fixed cherry count `c`: `t` bulk swaps applied to the tie
    edge.  `colState K c 0 = tieState K c` (the trade edge). -/
def colState (K c t : ℕ) : List Hub := hubState (K - c - 9 * t) (c + 11 * t) c

/-- The polynomial "bulk swap no longer helps" predicate in `(a,b,c)` form: `0 ≤ P(a,b,c)`, the
    integer-cleared numerator of `hubQ(a,b,c) − F·hubQ(a−9,b+11,c)` (`F = (513/80)^11/(621/64)^9`). -/
def bulkStopABC (a b c : ℕ) : Prop :=
  (0 : ℝ) ≤ 1463319377422497563982 * (a : ℝ) ^ 2 + 2962184974539468753000 * (a : ℝ) * b
    + 3189285822587494690730 * (a : ℝ) * c - 31509328118523021559140 * (a : ℝ)
    + 1498865597116971189018 * (b : ℝ) ^ 2 + 3224832042281968315766 * (b : ℝ) * c
    - 25177150793067162184140 * (b : ℝ) + 1725966445164997126748 * (c : ℝ) ^ 2
    + 15278426564011939378360 * (c : ℝ)

/-- **The bulk-swap comparison in polynomial form** (analog of `tie_trade_le_poly`): one bulk swap is
    `Aobj`-non-increasing iff the `bulkStopABC` polynomial inequality holds.  Reduces `hub_bulk_le`'s
    `hubQ` condition by clearing the two degrees `d = a+b+c`, `d' = a+b+c+2` and the factor `F`. -/
theorem hub_bulk_stop_iff (a b c : ℕ) (ha : 9 ≤ a) (hpos : 0 < a + b + c) :
    ((513 / 80 : ℝ) ^ 11 / (621 / 64) ^ 9) * hubQ (a - 9) (b + 11) c ≤ hubQ a b c
      ↔ bulkStopABC a b c := by
  have hd : (0 : ℝ) < (a : ℝ) + b + c := by exact_mod_cast hpos
  have hd2 : (0 : ℝ) < (a : ℝ) + b + c + 2 := by linarith
  simp only [hubQ, bulkStopABC]
  push_cast [Nat.cast_sub ha]
  rw [show ((a : ℝ) - 9 + (b + 11) + c) = (a : ℝ) + b + c + 2 by ring]
  constructor
  · intro h; field_simp at h; nlinarith [h, hd, hd2, mul_pos hd hd2]
  · intro h; field_simp; nlinarith [h, hd, hd2, mul_pos hd hd2]

/-- **Upward persistence of `bulkStopABC`** (analog of `tradeStop_persists`): once the bulk swap stops
    helping, applying one more swap (`a → a−9`, `b → b+11`) keeps it stopped, so each column is unimodal
    in `t`. -/
theorem bulkStopABC_persists (a b c : ℕ) (ha : 9 ≤ a) (h : bulkStopABC a b c) :
    bulkStopABC (a - 9) (b + 11) c := by
  have hA : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hB : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hC : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have h9 : (9 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  simp only [bulkStopABC] at h ⊢
  push_cast [Nat.cast_sub ha]
  nlinarith [h, hA, hB, hC, h9, mul_nonneg hA hB, mul_nonneg hA hC, mul_nonneg hB hC]

/-- The `t`-level "bulk stops helping" predicate on the column `colState K c ·`. -/
def colStop (K c t : ℕ) : Prop := bulkStopABC (K - c - 9 * t) (c + 11 * t) c

/-- **Column bulk-step comparison**: one more bulk swap at position `t` (requiring `9 ≤ K−c−9t`) is
    `Aobj`-non-increasing iff `colStop K c t`. -/
theorem col_step_le (K c t : ℕ) (ha : 9 ≤ K - c - 9 * t)
    (hpos : 0 < (K - c - 9 * t) + (c + 11 * t) + c) :
    Aobj (backboneU (colState K c (t + 1))) ≤ Aobj (backboneU (colState K c t))
      ↔ colStop K c t := by
  have hst1 : colState K c (t + 1) = hubState ((K - c - 9 * t) - 9) ((c + 11 * t) + 11) c := by
    unfold colState
    rw [show K - c - 9 * (t + 1) = (K - c - 9 * t) - 9 by omega,
      show c + 11 * (t + 1) = (c + 11 * t) + 11 by omega]
  rw [hst1, colState, hub_bulk_le _ _ _ ha hpos, hub_bulk_stop_iff _ _ _ ha hpos, colStop]

/-- **Upward persistence of `colStop`** (from `bulkStopABC_persists`): once the bulk swap stops helping
    at `t`, it stays stopped at `t+1`, so `Aobj(colState K c ·)` is unimodal in `t`. -/
theorem colStop_persists (K c t : ℕ) (ha : 9 ≤ K - c - 9 * t) (h : colStop K c t) :
    colStop K c (t + 1) := by
  have := bulkStopABC_persists (K - c - 9 * t) (c + 11 * t) c ha h
  rw [colStop, show K - c - 9 * (t + 1) = (K - c - 9 * t) - 9 by omega,
    show c + 11 * (t + 1) = (c + 11 * t) + 11 by omega]
  exact this

/-- If the bulk swap still helps at `t` (`¬colStop`), the objective strictly increases. -/
theorem col_step_up (K c t : ℕ) (ha : 9 ≤ K - c - 9 * t)
    (hpos : 0 < (K - c - 9 * t) + (c + 11 * t) + c) (h : ¬ colStop K c t) :
    Aobj (backboneU (colState K c t)) ≤ Aobj (backboneU (colState K c (t + 1))) := by
  have hiff := col_step_le K c t ha hpos
  have hnot : ¬ (Aobj (backboneU (colState K c (t + 1))) ≤ Aobj (backboneU (colState K c t))) :=
    fun hle => h (hiff.mp hle)
  linarith [not_le.mp hnot]

/-- Once the bulk swap stops helping (`colStop`), the objective is non-increasing. -/
theorem col_step_down (K c t : ℕ) (ha : 9 ≤ K - c - 9 * t)
    (hpos : 0 < (K - c - 9 * t) + (c + 11 * t) + c) (h : colStop K c t) :
    Aobj (backboneU (colState K c (t + 1))) ≤ Aobj (backboneU (colState K c t)) :=
  (col_step_le K c t ha hpos).mpr h

/-- **Increasing chain** on the bulk-helps region: if the swap helps at every `i ∈ [t0, t)` (and stays
    in range), `V(t0) ≤ V(t)`. -/
theorem col_up_chain (K c t0 : ℕ) :
    ∀ t, t0 ≤ t → 9 * t ≤ K - c → (∀ i, t0 ≤ i → i < t → ¬ colStop K c i) →
      Aobj (backboneU (colState K c t0)) ≤ Aobj (backboneU (colState K c t)) := by
  intro t ht0
  induction t, ht0 using Nat.le_induction with
  | base => intro _ _; exact le_refl _
  | succ t ht0 ih =>
      intro htK hlt
      have h1 := ih (by omega) (fun i hi hit => hlt i hi (by omega))
      have h2 := col_step_up K c t (by omega) (by omega) (hlt t ht0 (by omega))
      linarith

/-- Persistence up the column: `colStop` at `tstar` implies `colStop` at every in-range `t ≥ tstar`. -/
theorem colStop_up (K c tstar : ℕ) (hstop : colStop K c tstar) :
    ∀ t, tstar ≤ t → 9 * t ≤ K - c → colStop K c t := by
  intro t hts
  induction t, hts using Nat.le_induction with
  | base => intro _; exact hstop
  | succ t hts ih => intro htK; exact colStop_persists K c t (by omega) (ih (by omega))

/-- **Non-increasing chain** past the bulk-stop threshold: if the swap has stopped at `tstar`, then for
    every in-range `t ≥ tstar`, `V(t) ≤ V(tstar)`. -/
theorem col_down_chain (K c tstar : ℕ) (hstar : 9 * tstar ≤ K - c) (hstop : colStop K c tstar) :
    ∀ t, tstar ≤ t → 9 * t ≤ K - c →
      Aobj (backboneU (colState K c t)) ≤ Aobj (backboneU (colState K c tstar)) := by
  intro t hts
  induction t, hts using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ t hts ih =>
      intro htK
      have hstopt : colStop K c t := colStop_up K c tstar hstop t hts (by omega)
      have h2 := col_step_down K c t (by omega) (by omega) hstopt
      have h1 := ih (by omega)
      linarith

/-- **The t-argmax / column maximum**: given `tstar` is the least bulk count where the swap stops
    helping, the column value at `tstar` dominates every in-range `t`.  (The t-axis half of the M3
    single-hub 2-D envelope; combined with the c-envelope it gives `singleHub_le_tie`.) -/
theorem col_maximal_over_bulk (K c tstar : ℕ) (hstarR : 9 * tstar ≤ K - c)
    (hstop : colStop K c tstar) (hlt : ∀ i, i < tstar → ¬ colStop K c i) :
    ∀ t, 9 * t ≤ K - c →
      Aobj (backboneU (colState K c t)) ≤ Aobj (backboneU (colState K c tstar)) := by
  intro t htK
  by_cases hle : t ≤ tstar
  · exact col_up_chain K c t tstar hle hstarR (fun i hi hib => hlt i hib)
  · exact col_down_chain K c tstar hstarR hstop t (by omega) htK

/-! ### The c-envelope, clean regime `K ≥ 22`: each column collapses to its `t = 0` tie edge. -/

/-- `colState K c 0 = tieState K c` (the trade edge). -/
theorem colState_zero (K c : ℕ) : colState K c 0 = tieState K c := by
  simp only [colState, tieState, hubState, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]

/-- **At `K ≥ 22` the bulk swap does not help at the tie edge** (`colStop K c 0` for every `c ≤ 5`):
    the `bulkStopABC(K−c, c, c)` quadratic in `K` is nonnegative there (threshold `K = 22`, binding at
    `c = 0`).  Matches `broadened_tie_2d_envelope.py`'s `t*(c) = 0 ⟺ K ≥ 22`. -/
theorem colStop_zero_large (K c : ℕ) (hK : 22 ≤ K) (hc : c ≤ 5) : colStop K c 0 := by
  have hKc : c ≤ K := by omega
  have hKR : (22 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  simp only [colStop, Nat.mul_zero, Nat.sub_zero, Nat.add_zero, bulkStopABC]
  push_cast [Nat.cast_sub hKc]
  interval_cases c <;>
    nlinarith [hKR, sq_nonneg ((K : ℝ) - 22), (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))]

/-- **Column collapse at `K ≥ 22`**: every in-range bulk position `colState K c t` is dominated by its
    `t = 0` tie edge `tieState K c`.  (The per-column half of the c-envelope; combined with
    `tie_maximal_over_trades` across `c` it yields the full single-hub envelope for `K ≥ 22`.) -/
theorem col_le_edge_large (K c t : ℕ) (hK : 22 ≤ K) (hc : c ≤ 5) (htK : 9 * t ≤ K - c) :
    Aobj (backboneU (colState K c t)) ≤ Aobj (backboneU (tieState K c)) := by
  have h := col_maximal_over_bulk K c 0 (by omega) (colStop_zero_large K c hK hc)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) t htK
  rwa [colState_zero] at h

/-- The trade stops helping at `m = 0` for `K ≥ 23` (near-star optimal; threshold `K = 23`, matching
    `tie_trade_le_poly` and `broadened_tie_family.py`). -/
theorem tradeStop_zero_large (K : ℕ) (hK : 23 ≤ K) : tradeStop K 0 := by
  have hKR : (23 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  simp only [tradeStop, Nat.cast_zero, add_zero, mul_zero]
  nlinarith [hKR]

/-- **Single-hub envelope, clean regime `K ≥ 23`**: every in-range bulk column `colState K c t`
    (any Balanced single hub at aligned size `11K` with cherry count `c ≤ 5`) is dominated by the
    NEAR-STAR tie `tieState K 0` (K load-5 arms).  The 2-D envelope collapses:  t-axis via
    `col_le_edge_large`, then the c-axis via `tie_maximal_over_trades` at `mstar = 0`.  (For `K = 22`
    the argmax is `mstar = 1`; for `5 ≤ K < 22` low-c columns peak at `t = 1` -- the finite patch --
    both left to the c-envelope completion.) -/
theorem col_le_nearStar_large (K c t : ℕ) (hK : 23 ≤ K) (hc : c ≤ 5) (htK : 9 * t ≤ K - c) :
    Aobj (backboneU (colState K c t)) ≤ Aobj (backboneU (tieState K 0)) := by
  have h1 := col_le_edge_large K c t (by omega) hc htK
  have h2 := tie_maximal_over_trades K 0 (by omega) (Nat.zero_le K) (tradeStop_zero_large K hK)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) c (by omega)
  linarith

/-! ### The general single-hub decomposition and the `K ≥ 23` envelope in `(a,b,c)` form. -/

/-- **Size-decomposition**: a Balanced single hub `hubState a b c` at aligned size `11a+9b+2c = 11K`
    with `c ≤ 5` is exactly the bulk column `colState K c (b/11)`.  (The size relation forces
    `b ≡ c mod 11` and `b ≥ c`, so `b = c + 11·(b/11)` and `a = K − c − 9·(b/11)`.) -/
theorem hubState_eq_colState (a b c K : ℕ) (hc : c ≤ 5) (hsize : 11 * a + 9 * b + 2 * c = 11 * K) :
    hubState a b c = colState K c (b / 11) ∧ 9 * (b / 11) ≤ K - c := by
  have hb : b = c + 11 * (b / 11) := by omega
  have ha : a = K - c - 9 * (b / 11) := by omega
  refine ⟨?_, by omega⟩
  rw [colState]; congr 1 <;> omega

/-- **The single-hub envelope in `(a,b,c)` form, clean regime `K ≥ 23`**: every Balanced single hub at
    aligned size `11K` (`c ≤ 5`) is dominated by the near-star `tieState K 0`.  This is the length-1
    input to `sharpRate_of_tieDomination` for `K ≥ 23`. -/
theorem singleHub_le_tie_large (a b c K : ℕ) (hc : c ≤ 5) (hK : 23 ≤ K)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * K) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (tieState K 0)) := by
  obtain ⟨heq, htK⟩ := hubState_eq_colState a b c K hc hsize
  rw [heq]
  exact col_le_nearStar_large K c (b / 11) hK hc htK

/-! ### The tie-edge argmax `mOf K` for ALL K (interior least-`tradeStop`, else the boundary `m = K`). -/

open Classical

/-- The trade always stops helping at some (large) `m`: `tradeStop K 115` holds for every `K`. -/
theorem tradeStop_exists (K : ℕ) : ∃ m, tradeStop K m := by
  refine ⟨115, ?_⟩
  simp only [tradeStop]
  push_cast
  nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ)), sq_nonneg ((K : ℝ))]

/-- The least trade count at which the trade stops helping. -/
noncomputable def leastTradeStop (K : ℕ) : ℕ := Nat.find (tradeStop_exists K)

theorem leastTradeStop_spec (K : ℕ) : tradeStop K (leastTradeStop K) :=
  Nat.find_spec (tradeStop_exists K)

theorem leastTradeStop_min (K : ℕ) {i : ℕ} (hi : i < leastTradeStop K) : ¬ tradeStop K i :=
  Nat.find_min (tradeStop_exists K) hi

/-- **The tie-edge argmax.**  For `K ≥ 5` this is the least `tradeStop` count (`≤ K`); for `K ≤ 4`,
    where no `m ≤ K` has `tradeStop`, it is the boundary `m = K`.  So `mOf K = min K (leastTradeStop K)`
    (matches `m(K)`: 1..5→K, 6..11→5, …, ≥23→0). -/
noncomputable def mOf (K : ℕ) : ℕ := min K (leastTradeStop K)

theorem mOf_le (K : ℕ) : mOf K ≤ K := min_le_left _ _

/-- **The tie edge is maximized at `mOf K`, for every `K`.**  Interior: `tie_maximal_over_trades` at the
    least `tradeStop`.  Boundary (`K ≤ 4`, no in-range `tradeStop`): `tie_up_chain` to `m = K`. -/
theorem tie_maximal_general (K : ℕ) (hK : 0 < K) :
    ∀ m, m ≤ K → Aobj (backboneU (tieState K m)) ≤ Aobj (backboneU (tieState K (mOf K))) := by
  intro m hm
  by_cases hle : leastTradeStop K ≤ K
  · have hmOf : mOf K = leastTradeStop K := min_eq_right hle
    rw [hmOf]
    exact tie_maximal_over_trades K (leastTradeStop K) hK hle (leastTradeStop_spec K)
      (fun i hi => leastTradeStop_min K hi) m hm
  · have hgt : K < leastTradeStop K := by omega
    have hmOf : mOf K = K := min_eq_left (le_of_lt hgt)
    rw [hmOf]
    exact tie_up_chain K m hK K hm (le_refl K)
      (fun i _ hiK => leastTradeStop_min K (by omega))

/-- **The single-hub envelope for `K ≥ 22`** (targeting the true tie argmax `mOf K`): every Balanced
    single hub at aligned size `11K`, `K ≥ 22`, is dominated by the broadened tie `tieState K (mOf K)`.
    t-axis collapse (`col_le_edge_large`) then c-axis (`tie_maximal_general`).  This is the length-1
    input to `sharpRate_of_tieDomination` for all `K ≥ 22` (the remaining `5 ≤ K < 22` low-c columns
    that peak at `t = 1` are the finite interior patch). -/
theorem singleHub_le_tie_ge22 (a b c K : ℕ) (hc : c ≤ 5) (hK : 22 ≤ K)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * K) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (tieState K (mOf K))) := by
  obtain ⟨heq, htK⟩ := hubState_eq_colState a b c K hc hsize
  rw [heq]
  have h1 := col_le_edge_large K c (b / 11) hK hc htK
  have h2 := tie_maximal_general K (by omega) c (by omega)
  linarith

end Step3
end R3Cert
