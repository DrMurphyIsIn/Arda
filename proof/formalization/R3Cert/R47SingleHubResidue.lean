/-
  R3Cert.R47SingleHubResidue -- M3 extended across the 11 size residue classes (the non-aligned-n layer).

  The aligned single-hub envelope (`R47SingleHub2D`) covers sizes `n ≡ 1 mod 11` (the `b = c` tie edge).
  A general single hub at size `n` has `b - c ≡ r mod 11` for `r = 5(n-1) mod 11`, and (verified in
  proof/verification -- global max on the `t=0` edge for every residue `r` and `M ≥ 5`) the per-size
  maximizer is the SHIFTED tie edge `rtieState M r c* = hubState (M-c*) (c*+r) c*`.

  This file builds the residue-general atoms.  The bulk atoms (`hub_bulk_le`, `bulkStopABC*`) are already
  `(a,b,c)`-general (they never used `b = c`); the missing atom is the general TRADE step `hub_trade_le`
  (one `load-5 -> load-4 + cherry` trade, factor `114/115`), the `hub_bulk_le` analog on the `c`-axis of
  the shifted edge.  `conjecture1_proved = False`.  Self-contained leaf.
-/
import Mathlib
import R3Cert.R47TieBroadened
import R3Cert.R47SingleHub2D

namespace R3Cert
namespace Step3

open RTree

/-- **The general cherry-trade step** (the `hub_bulk_le` analog on the `c`-axis): trading one load-5 arm
    for a load-4 arm + a cherry (`a→a-1, b→b+1, c→c+1`, size-preserving) multiplies the power product by
    exactly `114/115`, so the objective comparison collapses to the `hubQ` comparison.  Holds for ANY
    `(a,b,c)` (no `b = c` assumption) -- the residue-general trade atom. -/
theorem hub_trade_le (a b c : ℕ) (ha : 1 ≤ a) (hpos : 0 < a + b + c) :
    Aobj (backboneU (hubState (a - 1) (b + 1) (c + 1))) ≤ Aobj (backboneU (hubState a b c))
      ↔ (114 / 115 : ℝ) * hubQ (a - 1) (b + 1) (c + 1) ≤ hubQ a b c := by
  have hpos' : 0 < (a - 1) + (b + 1) + (c + 1) := by omega
  have hprod : (621 / 64 : ℝ) ^ (a - 1) * (513 / 80) ^ (b + 1) * (3 / 2) ^ (c + 1)
      = (114 / 115 : ℝ) * ((621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c) := by
    have hae : (621 / 64 : ℝ) ^ a = (621 / 64) ^ (a - 1) * (621 / 64) ^ 1 := by
      rw [← pow_add, Nat.sub_add_cancel ha]
    have hbe : (513 / 80 : ℝ) ^ (b + 1) = (513 / 80) ^ b * (513 / 80) ^ 1 := pow_add _ _ _
    have hce : (3 / 2 : ℝ) ^ (c + 1) = (3 / 2) ^ c * (3 / 2) ^ 1 := pow_add _ _ _
    rw [hae, hbe, hce]
    ring
  rw [hub_Aobj_factored a b c hpos, hub_Aobj_factored (a - 1) (b + 1) (c + 1) hpos', hprod]
  set P := (621 / 64 : ℝ) ^ a * (513 / 80) ^ b * (3 / 2) ^ c with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  constructor
  · intro h
    have h2 : P * ((114 / 115 : ℝ) * hubQ (a - 1) (b + 1) (c + 1)) ≤ P * hubQ a b c := by
      have e : P * ((114 / 115 : ℝ) * hubQ (a - 1) (b + 1) (c + 1))
          = 114 / 115 * P * hubQ (a - 1) (b + 1) (c + 1) := by ring
      rw [e]; exact h
    exact le_of_mul_le_mul_left h2 hPpos
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h hPpos.le
    have e : 114 / 115 * P * hubQ (a - 1) (b + 1) (c + 1)
        = P * ((114 / 115 : ℝ) * hubQ (a - 1) (b + 1) (c + 1)) := by ring
    rw [e]; exact h2

/-- The polynomial "cherry trade no longer helps" predicate in general `(a,b,c)` form (analog of
    `tie_trade_le_poly`'s `tradeStop`, but not assuming `b = c`). -/
def hubTradeStop (a b c : ℕ) : Prop :=
  (0 : ℝ) ≤ 1482 * (a : ℝ) ^ 2 + 3000 * (a : ℝ) * b + 3230 * (a : ℝ) * c - 32946 * (a : ℝ)
    + 1518 * (b : ℝ) ^ 2 + 3266 * (b : ℝ) * c - 28806 * (b : ℝ)
    + 1748 * (c : ℝ) ^ 2 - 2356 * (c : ℝ)

/-- **The general cherry-trade comparison in polynomial form** (analog of `tie_trade_le_poly`): the trade
    is `Aobj`-non-increasing iff `hubTradeStop`.  Clears the two degrees `d = a+b+c`, `d' = a+b+c+1`. -/
theorem hub_trade_stop_iff (a b c : ℕ) (ha : 1 ≤ a) (hpos : 0 < a + b + c) :
    (114 / 115 : ℝ) * hubQ (a - 1) (b + 1) (c + 1) ≤ hubQ a b c ↔ hubTradeStop a b c := by
  have hd : (0 : ℝ) < (a : ℝ) + b + c := by exact_mod_cast hpos
  have hd2 : (0 : ℝ) < (a : ℝ) + b + c + 1 := by linarith
  simp only [hubQ, hubTradeStop]
  push_cast [Nat.cast_sub ha]
  rw [show ((a : ℝ) - 1 + (b + 1) + (c + 1)) = (a : ℝ) + b + c + 1 by ring]
  constructor
  · intro h; field_simp at h; nlinarith [h, hd, hd2, mul_pos hd hd2]
  · intro h; field_simp; nlinarith [h, hd, hd2, mul_pos hd hd2]

/-- **Upward persistence of `hubTradeStop`** along a trade (`a→a-1, b→b+1, c→c+1`): once the trade stops
    helping it stays stopped, so the shifted trade edge is unimodal in the cherry count. -/
theorem hubTradeStop_persists (a b c : ℕ) (ha : 1 ≤ a) (h : hubTradeStop a b c) :
    hubTradeStop (a - 1) (b + 1) (c + 1) := by
  have hA : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hB : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hC : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  simp only [hubTradeStop] at h ⊢
  push_cast [Nat.cast_sub ha]
  nlinarith [h, hA, hB, hC, h1, mul_nonneg hA hB, mul_nonneg hA hC, mul_nonneg hB hC]

/-- The SHIFTED tie edge for residue `r`: `M-c` load-5 arms, `c+r` load-4 arms, `c` cherries.  At
    `r = 0` this is the aligned `tieState M c`; the per-size maximizer (`t = 0` edge) at residue `r`. -/
def rtieState (M r c : ℕ) : List Hub := hubState (M - c) (c + r) c

/-- **Shifted-edge trade step**: one more trade at cherry count `c` (requiring `c + 1 ≤ M`) is
    `Aobj`-non-increasing iff `hubTradeStop (M-c) (c+r) c`. -/
theorem rtie_trade_le (M r c : ℕ) (hc : c + 1 ≤ M) (hpos : 0 < (M - c) + (c + r) + c) :
    Aobj (backboneU (rtieState M r (c + 1))) ≤ Aobj (backboneU (rtieState M r c))
      ↔ hubTradeStop (M - c) (c + r) c := by
  have hst : rtieState M r (c + 1) = hubState ((M - c) - 1) ((c + r) + 1) (c + 1) := by
    unfold rtieState
    rw [show M - (c + 1) = (M - c) - 1 by omega, show (c + 1) + r = (c + r) + 1 by omega]
  rw [hst, rtieState, hub_trade_le _ _ _ (by omega) hpos, hub_trade_stop_iff _ _ _ (by omega) hpos]

/-- If the trade still helps at `c` (`¬hubTradeStop`), the shifted-edge objective strictly increases. -/
theorem rtie_step_up (M r c : ℕ) (hc : c + 1 ≤ M) (hpos : 0 < (M - c) + (c + r) + c)
    (h : ¬ hubTradeStop (M - c) (c + r) c) :
    Aobj (backboneU (rtieState M r c)) ≤ Aobj (backboneU (rtieState M r (c + 1))) := by
  have hiff := rtie_trade_le M r c hc hpos
  have hnot : ¬ (Aobj (backboneU (rtieState M r (c + 1))) ≤ Aobj (backboneU (rtieState M r c))) :=
    fun hle => h (hiff.mp hle)
  linarith [not_le.mp hnot]

/-- Once the trade stops helping, the shifted-edge objective is non-increasing. -/
theorem rtie_step_down (M r c : ℕ) (hc : c + 1 ≤ M) (hpos : 0 < (M - c) + (c + r) + c)
    (h : hubTradeStop (M - c) (c + r) c) :
    Aobj (backboneU (rtieState M r (c + 1))) ≤ Aobj (backboneU (rtieState M r c)) :=
  (rtie_trade_le M r c hc hpos).mpr h

/-- Persistence up the shifted edge: `hubTradeStop` at `c` implies it at every reachable `c' ≥ c`. -/
theorem hubTradeStop_up (M r cstar : ℕ) (hstop : hubTradeStop (M - cstar) (cstar + r) cstar) :
    ∀ c, cstar ≤ c → c ≤ M → hubTradeStop (M - c) (c + r) c := by
  intro c hcs
  induction c, hcs using Nat.le_induction with
  | base => intro _; exact hstop
  | succ c hcs ih =>
      intro hcM
      have := hubTradeStop_persists (M - c) (c + r) c (by omega) (ih (by omega))
      rwa [show M - c - 1 = M - (c + 1) by omega, show c + r + 1 = (c + 1) + r by omega] at this

/-- **Increasing chain** on the trade-helps region of the shifted edge. -/
theorem rtie_up_chain (M r c0 : ℕ) :
    ∀ c, c0 ≤ c → c ≤ M → (∀ i, c0 ≤ i → i < c → ¬ hubTradeStop (M - i) (i + r) i) →
      Aobj (backboneU (rtieState M r c0)) ≤ Aobj (backboneU (rtieState M r c)) := by
  intro c hc0
  induction c, hc0 using Nat.le_induction with
  | base => intro _ _; exact le_refl _
  | succ c hc0 ih =>
      intro hcM hlt
      have h1 := ih (by omega) (fun i hi hic => hlt i hi (by omega))
      have h2 := rtie_step_up M r c (by omega) (by omega) (hlt c hc0 (by omega))
      linarith

/-- **Non-increasing chain** past the trade-stop threshold on the shifted edge. -/
theorem rtie_down_chain (M r cstar : ℕ) (hcsM : cstar ≤ M)
    (hstop : hubTradeStop (M - cstar) (cstar + r) cstar) :
    ∀ c, cstar ≤ c → c ≤ M →
      Aobj (backboneU (rtieState M r c)) ≤ Aobj (backboneU (rtieState M r cstar)) := by
  intro c hcs
  induction c, hcs using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ c hcs ih =>
      intro hcM
      have hstopc : hubTradeStop (M - c) (c + r) c := hubTradeStop_up M r cstar hstop c hcs (by omega)
      have h2 := rtie_step_down M r c (by omega) (by omega) hstopc
      have h1 := ih (by omega)
      linarith

/-- **The shifted-edge trade argmax**: given `cstar` is the least trade count where the trade stops
    helping, `rtieState M r cstar` dominates every `c ≤ M` on the shifted edge.  The residue-general
    analog of `tie_maximal_over_trades`. -/
theorem rtie_maximal_over_trades (M r cstar : ℕ) (hcsM : cstar ≤ M)
    (hstop : hubTradeStop (M - cstar) (cstar + r) cstar)
    (hlt : ∀ i, i < cstar → ¬ hubTradeStop (M - i) (i + r) i) :
    ∀ c, c ≤ M → Aobj (backboneU (rtieState M r c)) ≤ Aobj (backboneU (rtieState M r cstar)) := by
  intro c hcM
  by_cases hle : c ≤ cstar
  · exact rtie_up_chain M r c cstar hle hcsM (fun i hi hic => hlt i hic)
  · exact rtie_down_chain M r cstar hcsM hstop c (by omega) hcM

/-! ### The shifted bulk column (t-axis) for residue `r`, reusing the general `bulkStopABC` atoms. -/

/-- The shifted bulk column at residue `r`, cherry count `c`: `t` bulk swaps on the shifted edge.
    `colStateR M r c 0 = rtieState M r c`. -/
def colStateR (M r c t : ℕ) : List Hub := hubState (M - c - 9 * t) (c + r + 11 * t) c

/-- The `t`-level bulk-stop predicate on the shifted column. -/
def colStopR (M r c t : ℕ) : Prop := bulkStopABC (M - c - 9 * t) (c + r + 11 * t) c

theorem colStateR_zero (M r c : ℕ) : colStateR M r c 0 = rtieState M r c := by
  simp only [colStateR, rtieState, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]

/-- **Shifted-column bulk-step comparison** (via the general `hub_bulk_le`/`hub_bulk_stop_iff`). -/
theorem col_step_leR (M r c t : ℕ) (ha : 9 ≤ M - c - 9 * t)
    (hpos : 0 < (M - c - 9 * t) + (c + r + 11 * t) + c) :
    Aobj (backboneU (colStateR M r c (t + 1))) ≤ Aobj (backboneU (colStateR M r c t))
      ↔ colStopR M r c t := by
  have hst1 : colStateR M r c (t + 1)
      = hubState ((M - c - 9 * t) - 9) ((c + r + 11 * t) + 11) c := by
    unfold colStateR
    rw [show M - c - 9 * (t + 1) = (M - c - 9 * t) - 9 by omega,
      show c + r + 11 * (t + 1) = (c + r + 11 * t) + 11 by omega]
  rw [hst1, colStateR, hub_bulk_le _ _ _ ha hpos, hub_bulk_stop_iff _ _ _ ha hpos, colStopR]

theorem colStopR_persists (M r c t : ℕ) (ha : 9 ≤ M - c - 9 * t) (h : colStopR M r c t) :
    colStopR M r c (t + 1) := by
  have := bulkStopABC_persists (M - c - 9 * t) (c + r + 11 * t) c ha h
  rw [colStopR, show M - c - 9 * (t + 1) = (M - c - 9 * t) - 9 by omega,
    show c + r + 11 * (t + 1) = (c + r + 11 * t) + 11 by omega]
  exact this

theorem col_step_upR (M r c t : ℕ) (ha : 9 ≤ M - c - 9 * t)
    (hpos : 0 < (M - c - 9 * t) + (c + r + 11 * t) + c) (h : ¬ colStopR M r c t) :
    Aobj (backboneU (colStateR M r c t)) ≤ Aobj (backboneU (colStateR M r c (t + 1))) := by
  have hiff := col_step_leR M r c t ha hpos
  have hnot : ¬ (Aobj (backboneU (colStateR M r c (t + 1))) ≤ Aobj (backboneU (colStateR M r c t))) :=
    fun hle => h (hiff.mp hle)
  linarith [not_le.mp hnot]

theorem col_step_downR (M r c t : ℕ) (ha : 9 ≤ M - c - 9 * t)
    (hpos : 0 < (M - c - 9 * t) + (c + r + 11 * t) + c) (h : colStopR M r c t) :
    Aobj (backboneU (colStateR M r c (t + 1))) ≤ Aobj (backboneU (colStateR M r c t)) :=
  (col_step_leR M r c t ha hpos).mpr h

theorem col_up_chainR (M r c t0 : ℕ) :
    ∀ t, t0 ≤ t → 9 * t ≤ M - c → (∀ i, t0 ≤ i → i < t → ¬ colStopR M r c i) →
      Aobj (backboneU (colStateR M r c t0)) ≤ Aobj (backboneU (colStateR M r c t)) := by
  intro t ht0
  induction t, ht0 using Nat.le_induction with
  | base => intro _ _; exact le_refl _
  | succ t ht0 ih =>
      intro htK hlt
      have h1 := ih (by omega) (fun i hi hit => hlt i hi (by omega))
      have h2 := col_step_upR M r c t (by omega) (by omega) (hlt t ht0 (by omega))
      linarith

theorem colStopR_up (M r c tstar : ℕ) (hstop : colStopR M r c tstar) :
    ∀ t, tstar ≤ t → 9 * t ≤ M - c → colStopR M r c t := by
  intro t hts
  induction t, hts using Nat.le_induction with
  | base => intro _; exact hstop
  | succ t hts ih => intro htK; exact colStopR_persists M r c t (by omega) (ih (by omega))

theorem col_down_chainR (M r c tstar : ℕ) (hstar : 9 * tstar ≤ M - c) (hstop : colStopR M r c tstar) :
    ∀ t, tstar ≤ t → 9 * t ≤ M - c →
      Aobj (backboneU (colStateR M r c t)) ≤ Aobj (backboneU (colStateR M r c tstar)) := by
  intro t hts
  induction t, hts using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ t hts ih =>
      intro htK
      have hstopt : colStopR M r c t := colStopR_up M r c tstar hstop t hts (by omega)
      have h2 := col_step_downR M r c t (by omega) (by omega) hstopt
      have h1 := ih (by omega)
      linarith

/-- **Shifted-column t-argmax**: the residue-general analog of `col_maximal_over_bulk`. -/
theorem col_maximal_over_bulkR (M r c tstar : ℕ) (hstarR : 9 * tstar ≤ M - c)
    (hstop : colStopR M r c tstar) (hlt : ∀ i, i < tstar → ¬ colStopR M r c i) :
    ∀ t, 9 * t ≤ M - c →
      Aobj (backboneU (colStateR M r c t)) ≤ Aobj (backboneU (colStateR M r c tstar)) := by
  intro t htK
  by_cases hle : t ≤ tstar
  · exact col_up_chainR M r c t tstar hle hstarR (fun i hi hib => hlt i hib)
  · exact col_down_chainR M r c tstar hstarR hstop t (by omega) htK

/-! ### The clean regime `M ≥ 22` (all residues): the shifted column collapses to its `t = 0` edge. -/

/-- **At `M ≥ 22` the bulk swap does not help at the shifted edge** (`colStopR M r c 0`), for every
    residue `r ≤ 10` and `c ≤ 5`.  Uniform threshold `M = 22` (the binding `r = 0` case). -/
theorem colStopR_zero_large (M r c : ℕ) (hM : 22 ≤ M) (hr : r ≤ 10) (hc : c ≤ 5) :
    colStopR M r c 0 := by
  have hcM : c ≤ M := by omega
  have hMR : (22 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hrR : (r : ℝ) ≤ 10 := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  simp only [colStopR, Nat.mul_zero, Nat.sub_zero, Nat.add_zero, bulkStopABC]
  push_cast [Nat.cast_sub hcM]
  interval_cases c <;>
    nlinarith [hMR, hrR, hr0, sq_nonneg ((M : ℝ) - 22), sq_nonneg ((r : ℝ)),
      mul_nonneg hr0 (by linarith : (0:ℝ) ≤ (M:ℝ) - 22), (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]

/-- **Shifted-column collapse at `M ≥ 22`**: every in-range bulk position `colStateR M r c t` is
    dominated by its `t = 0` shifted edge `rtieState M r c`. -/
theorem col_le_edgeR (M r c t : ℕ) (hM : 22 ≤ M) (hr : r ≤ 10) (hc : c ≤ 5) (htK : 9 * t ≤ M - c) :
    Aobj (backboneU (colStateR M r c t)) ≤ Aobj (backboneU (rtieState M r c)) := by
  have h := col_maximal_over_bulkR M r c 0 (by omega) (colStopR_zero_large M r c hM hr hc)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) t htK
  rwa [colStateR_zero] at h

/-! ### The shifted-edge argmax `rMOf M r` (all M) and the clean-regime residue envelope. -/

open Classical

/-- The trade always stops helping at some cherry count (`c = M + 20`, where `a = 0`). -/
theorem hubTradeStop_exists (M r : ℕ) : ∃ c, hubTradeStop (M - c) (c + r) c := by
  refine ⟨M + 20, ?_⟩
  simp only [hubTradeStop, show M - (M + 20) = 0 by omega, Nat.cast_zero]
  push_cast
  nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ)), (Nat.cast_nonneg r : (0:ℝ) ≤ (r:ℝ)),
    mul_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ)) (Nat.cast_nonneg r : (0:ℝ) ≤ (r:ℝ))]

/-- The least cherry count at which the trade stops helping on the shifted edge. -/
noncomputable def leastHubTradeStop (M r : ℕ) : ℕ := Nat.find (hubTradeStop_exists M r)

theorem leastHubTradeStop_spec (M r : ℕ) :
    hubTradeStop (M - leastHubTradeStop M r) (leastHubTradeStop M r + r) (leastHubTradeStop M r) :=
  Nat.find_spec (hubTradeStop_exists M r)

theorem leastHubTradeStop_min (M r : ℕ) {i : ℕ} (hi : i < leastHubTradeStop M r) :
    ¬ hubTradeStop (M - i) (i + r) i :=
  Nat.find_min (hubTradeStop_exists M r) hi

/-- **The shifted-edge trade argmax** for residue `r` at "budget" `M`: the least trade count where the
    trade stops, capped at the boundary `M` (analog of `mOf`). -/
noncomputable def rMOf (M r : ℕ) : ℕ := min M (leastHubTradeStop M r)

theorem rMOf_le (M r : ℕ) : rMOf M r ≤ M := min_le_left _ _

/-- **The shifted edge is maximized at `rMOf M r`, for every `M`** (analog of `tie_maximal_general`). -/
theorem rtie_maximal_general (M r : ℕ) (hM : 0 < M) :
    ∀ c, c ≤ M → Aobj (backboneU (rtieState M r c)) ≤ Aobj (backboneU (rtieState M r (rMOf M r))) := by
  intro c hc
  by_cases hle : leastHubTradeStop M r ≤ M
  · have hmOf : rMOf M r = leastHubTradeStop M r := min_eq_right hle
    rw [hmOf]
    exact rtie_maximal_over_trades M r (leastHubTradeStop M r) hle (leastHubTradeStop_spec M r)
      (fun i hi => leastHubTradeStop_min M r hi) c hc
  · have hgt : M < leastHubTradeStop M r := by omega
    have hmOf : rMOf M r = M := min_eq_left (le_of_lt hgt)
    rw [hmOf]
    exact rtie_up_chain M r c M hc (le_refl M)
      (fun i _ hiM => leastHubTradeStop_min M r (by omega))

/-! ### Decomposition + the clean-regime residue envelope (`M ≥ 22`). -/

/-- **Size-decomposition (residue form)**: a Balanced single hub `hubState a b c` at size
    `11a+9b+2c = 11M+9r` with `b ≥ c + r` (no `t<0` -- automatic for `r ≤ 5`) is exactly the shifted
    bulk column `colStateR M r c ((b-c-r)/11)`.  (The size relation forces `b - c - r ≡ 0 mod 11`.) -/
theorem hubState_eq_colStateR (a b c M r : ℕ) (hbge : c + r ≤ b)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * r) :
    hubState a b c = colStateR M r c ((b - c - r) / 11) ∧ 9 * ((b - c - r) / 11) ≤ M - c := by
  have ht : b = c + r + 11 * ((b - c - r) / 11) := by omega
  have ha : a = M - c - 9 * ((b - c - r) / 11) := by omega
  refine ⟨?_, by omega⟩
  rw [colStateR]; congr 1 <;> omega

/-- **The residue single-hub envelope, clean regime (`r ≤ 5`, `M ≥ 22`)**: every Balanced single hub at
    size `11M + 9r` is dominated by the shifted tie `rtieState M r (rMOf M r)`.  For `r ≤ 5` there are no
    sub-edge (`b < c+r`) configs, so every hub is a shifted column `colStateR`; the t-axis collapses
    (`col_le_edgeR`) then the c-axis (`rtie_maximal_general`).  This closes the non-aligned-n single-hub
    envelope for residues 0..5 at all large sizes. -/
theorem singleHubR_le_tie_large (a b c M r : ℕ) (hr : r ≤ 5) (hc : c ≤ 5) (hM : 22 ≤ M)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * r) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M r (rMOf M r))) := by
  have hbge : c + r ≤ b := by omega
  obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M r hbge hsize
  rw [heq]
  have h1 := col_le_edgeR M r c ((b - c - r) / 11) hM (by omega) hc htK
  have h2 := rtie_maximal_general M r (by omega) c (by omega)
  linarith

/-- The edge (`b ≥ c+r`) single-hub envelope for any residue `r ≤ 10` (`M ≥ 22`).  Generalizes
    `singleHubR_le_tie_large` (which additionally derives `b ≥ c+r` automatically for `r ≤ 5`). -/
theorem singleHubR_le_tie_edge (a b c M r : ℕ) (hr : r ≤ 10) (hc : c ≤ 5) (hM : 22 ≤ M)
    (hbge : c + r ≤ b) (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * r) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M r (rMOf M r))) := by
  obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M r hbge hsize
  rw [heq]
  have h1 := col_le_edgeR M r c ((b - c - r) / 11) hM hr hc htK
  have h2 := rtie_maximal_general M r (by omega) c (by omega)
  linarith

/-- Sub-edge (`t = -1`) config for `r = 6`: `hubState (M+4) 0 5 ≤ rtieState M 6 0 = hubState M 6 0`
    (symbolic-`M`, `M ≥ 22`).  Reduces (via `hub_Aobj_eq` + factoring `V^M`) to a rational inequality
    in `M` closed by `nlinarith`. -/
theorem rNeg_r6 (M : ℕ) (hM : 22 ≤ M) :
    Aobj (backboneU (hubState (M + 4) 0 5)) ≤ Aobj (backboneU (rtieState M 6 0)) := by
  have hMR : (22 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hP : (0 : ℝ) < (621 / 64 : ℝ) ^ M := by positivity
  have key : (621 / 64 : ℝ) ^ 4 * ((513 / 80) ^ (0:ℕ) * (3 / 2) ^ (5:ℕ)
        * (1 + (((M : ℝ) + 4) * (3 / (((M : ℝ) + 9) * 23))
            + (5:ℝ) * (1 / (3 * ((M : ℝ) + 9))))))
      ≤ (513 / 80) ^ (6:ℕ) * (3 / 2) ^ (0:ℕ)
        * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 6) * 23)) + (6:ℝ) * (3 / (((M : ℝ) + 6) * 19)))) := by
    have h9 : (0 : ℝ) < (M : ℝ) + 9 := by linarith
    have h6 : (0 : ℝ) < (M : ℝ) + 6 := by linarith
    rw [← sub_nonneg]; field_simp; nlinarith [hMR, sq_nonneg ((M : ℝ) - 22)]
  rw [rtieState, show M - 0 = M by omega,
    hub_Aobj_eq (M + 4) 0 5 (by omega), hub_Aobj_eq M 6 0 (by omega),
    show (621 / 64 : ℝ) ^ (M + 4) = (621 / 64) ^ M * (621 / 64) ^ 4 from pow_add _ _ _]
  calc (621 / 64 : ℝ) ^ M * (621 / 64) ^ 4 * (513 / 80) ^ 0 * (3 / 2) ^ 5
          * (1 + (((M + 4 : ℕ) : ℝ) * (3 / (((M + 4 + 0 + 5 : ℕ) : ℝ) * 23))
              + ((0:ℕ) : ℝ) * (3 / (((M + 4 + 0 + 5 : ℕ) : ℝ) * 19))
              + ((5:ℕ) : ℝ) * (1 / (3 * ((M + 4 + 0 + 5 : ℕ) : ℝ)))))
        = (621 / 64 : ℝ) ^ M * ((621 / 64) ^ 4 * ((513 / 80) ^ (0:ℕ) * (3 / 2) ^ (5:ℕ)
            * (1 + (((M : ℝ) + 4) * (3 / (((M : ℝ) + 9) * 23))
                + (5:ℝ) * (1 / (3 * ((M : ℝ) + 9))))))) := by push_cast; ring
      _ ≤ (621 / 64 : ℝ) ^ M * ((513 / 80) ^ (6:ℕ) * (3 / 2) ^ (0:ℕ)
            * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 6) * 23)) + (6:ℝ) * (3 / (((M : ℝ) + 6) * 19))))) :=
          mul_le_mul_of_nonneg_left key hP.le
      _ = (621 / 64 : ℝ) ^ M * (513 / 80) ^ 6 * (3 / 2) ^ 0
            * (1 + (((M : ℕ) : ℝ) * (3 / (((M + 6 + 0 : ℕ) : ℝ) * 23))
                + ((6:ℕ) : ℝ) * (3 / (((M + 6 + 0 : ℕ) : ℝ) * 19))
                + ((0:ℕ) : ℝ) * (1 / (3 * ((M + 6 + 0 : ℕ) : ℝ))))) := by push_cast; ring

/-- Sub-edge (`t = -1`) config for `r = 7` (first): `hubState (M+5) 0 4 ≤ rtieState M 7 0`. -/
theorem rNeg_r7a (M : ℕ) (hM : 22 ≤ M) :
    Aobj (backboneU (hubState (M + 5) 0 4)) ≤ Aobj (backboneU (rtieState M 7 0)) := by
  have hMR : (22 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hP : (0 : ℝ) < (621 / 64 : ℝ) ^ M := by positivity
  have key : (621 / 64 : ℝ) ^ 5 * ((513 / 80) ^ (0:ℕ) * (3 / 2) ^ (4:ℕ)
        * (1 + (((M : ℝ) + 5) * (3 / (((M : ℝ) + 9) * 23))
            + (4:ℝ) * (1 / (3 * ((M : ℝ) + 9))))))
      ≤ (513 / 80) ^ (7:ℕ) * (3 / 2) ^ (0:ℕ)
        * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 7) * 23)) + (7:ℝ) * (3 / (((M : ℝ) + 7) * 19)))) := by
    have h9 : (0 : ℝ) < (M : ℝ) + 9 := by linarith
    have h7 : (0 : ℝ) < (M : ℝ) + 7 := by linarith
    rw [← sub_nonneg]; field_simp; nlinarith [hMR, sq_nonneg ((M : ℝ) - 22)]
  rw [rtieState, show M - 0 = M by omega,
    hub_Aobj_eq (M + 5) 0 4 (by omega), hub_Aobj_eq M 7 0 (by omega),
    show (621 / 64 : ℝ) ^ (M + 5) = (621 / 64) ^ M * (621 / 64) ^ 5 from pow_add _ _ _]
  calc (621 / 64 : ℝ) ^ M * (621 / 64) ^ 5 * (513 / 80) ^ 0 * (3 / 2) ^ 4
          * (1 + (((M + 5 : ℕ) : ℝ) * (3 / (((M + 5 + 0 + 4 : ℕ) : ℝ) * 23))
              + ((0:ℕ) : ℝ) * (3 / (((M + 5 + 0 + 4 : ℕ) : ℝ) * 19))
              + ((4:ℕ) : ℝ) * (1 / (3 * ((M + 5 + 0 + 4 : ℕ) : ℝ)))))
        = (621 / 64 : ℝ) ^ M * ((621 / 64) ^ 5 * ((513 / 80) ^ (0:ℕ) * (3 / 2) ^ (4:ℕ)
            * (1 + (((M : ℝ) + 5) * (3 / (((M : ℝ) + 9) * 23))
                + (4:ℝ) * (1 / (3 * ((M : ℝ) + 9))))))) := by push_cast; ring
      _ ≤ (621 / 64 : ℝ) ^ M * ((513 / 80) ^ (7:ℕ) * (3 / 2) ^ (0:ℕ)
            * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 7) * 23)) + (7:ℝ) * (3 / (((M : ℝ) + 7) * 19))))) :=
          mul_le_mul_of_nonneg_left key hP.le
      _ = (621 / 64 : ℝ) ^ M * (513 / 80) ^ 7 * (3 / 2) ^ 0
            * (1 + (((M : ℕ) : ℝ) * (3 / (((M + 7 + 0 : ℕ) : ℝ) * 23))
                + ((7:ℕ) : ℝ) * (3 / (((M + 7 + 0 : ℕ) : ℝ) * 19))
                + ((0:ℕ) : ℝ) * (1 / (3 * ((M + 7 + 0 : ℕ) : ℝ))))) := by push_cast; ring

/-- Sub-edge (`t = -1`) config for `r = 7` (second): `hubState (M+4) 1 5 ≤ rtieState M 7 0`. -/
theorem rNeg_r7b (M : ℕ) (hM : 22 ≤ M) :
    Aobj (backboneU (hubState (M + 4) 1 5)) ≤ Aobj (backboneU (rtieState M 7 0)) := by
  have hMR : (22 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hP : (0 : ℝ) < (621 / 64 : ℝ) ^ M := by positivity
  have key : (621 / 64 : ℝ) ^ 4 * ((513 / 80) ^ (1:ℕ) * (3 / 2) ^ (5:ℕ)
        * (1 + (((M : ℝ) + 4) * (3 / (((M : ℝ) + 10) * 23))
            + (1:ℝ) * (3 / (((M : ℝ) + 10) * 19)) + (5:ℝ) * (1 / (3 * ((M : ℝ) + 10))))))
      ≤ (513 / 80) ^ (7:ℕ) * (3 / 2) ^ (0:ℕ)
        * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 7) * 23)) + (7:ℝ) * (3 / (((M : ℝ) + 7) * 19)))) := by
    have h10 : (0 : ℝ) < (M : ℝ) + 10 := by linarith
    have h7 : (0 : ℝ) < (M : ℝ) + 7 := by linarith
    rw [← sub_nonneg]; field_simp; nlinarith [hMR, sq_nonneg ((M : ℝ) - 22)]
  rw [rtieState, show M - 0 = M by omega,
    hub_Aobj_eq (M + 4) 1 5 (by omega), hub_Aobj_eq M 7 0 (by omega),
    show (621 / 64 : ℝ) ^ (M + 4) = (621 / 64) ^ M * (621 / 64) ^ 4 from pow_add _ _ _]
  calc (621 / 64 : ℝ) ^ M * (621 / 64) ^ 4 * (513 / 80) ^ 1 * (3 / 2) ^ 5
          * (1 + (((M + 4 : ℕ) : ℝ) * (3 / (((M + 4 + 1 + 5 : ℕ) : ℝ) * 23))
              + ((1:ℕ) : ℝ) * (3 / (((M + 4 + 1 + 5 : ℕ) : ℝ) * 19))
              + ((5:ℕ) : ℝ) * (1 / (3 * ((M + 4 + 1 + 5 : ℕ) : ℝ)))))
        = (621 / 64 : ℝ) ^ M * ((621 / 64) ^ 4 * ((513 / 80) ^ (1:ℕ) * (3 / 2) ^ (5:ℕ)
            * (1 + (((M : ℝ) + 4) * (3 / (((M : ℝ) + 10) * 23))
                + (1:ℝ) * (3 / (((M : ℝ) + 10) * 19)) + (5:ℝ) * (1 / (3 * ((M : ℝ) + 10))))))) := by
          push_cast; ring
      _ ≤ (621 / 64 : ℝ) ^ M * ((513 / 80) ^ (7:ℕ) * (3 / 2) ^ (0:ℕ)
            * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 7) * 23)) + (7:ℝ) * (3 / (((M : ℝ) + 7) * 19))))) :=
          mul_le_mul_of_nonneg_left key hP.le
      _ = (621 / 64 : ℝ) ^ M * (513 / 80) ^ 7 * (3 / 2) ^ 0
            * (1 + (((M : ℕ) : ℝ) * (3 / (((M + 7 + 0 : ℕ) : ℝ) * 23))
                + ((7:ℕ) : ℝ) * (3 / (((M + 7 + 0 : ℕ) : ℝ) * 19))
                + ((0:ℕ) : ℝ) * (1 / (3 * ((M + 7 + 0 : ℕ) : ℝ))))) := by push_cast; ring

/-- **The non-aligned-n single-hub envelope for residues 0..7 (`M ≥ 22`).**  Every Balanced single hub
    `hubState a b c` (`c ≤ 5`) at size `11M + 9r`, `r ≤ 7`, `M ≥ 22`, is dominated by the shifted tie
    `rtieState M r (rMOf M r)`.  The `b ≥ c+r` (edge, `t ≥ 0`) configs go through `singleHubR_le_tie_edge`;
    the finitely many sub-edge (`t = -1`) configs -- `(M+4,0,5)` at `r=6`, `(M+5,0,4)`/`(M+4,1,5)` at
    `r=7` -- through `rNeg_r6`/`rNeg_r7a`/`rNeg_r7b` then `rtie_maximal_general`.  Closes 8 of the 11
    residue classes at large sizes; `r ∈ {8,9,10}` (oscillating optimal δ) is the open core. -/
theorem singleHubR_le_tie_07 (a b c M r : ℕ) (hr : r ≤ 7) (hc : c ≤ 5) (hM : 22 ≤ M)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * r) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M r (rMOf M r))) := by
  by_cases hbge : c + r ≤ b
  · exact singleHubR_le_tie_edge a b c M r (by omega) hc hM hbge hsize
  · have hcase : (r = 6 ∧ c = 5 ∧ b = 0 ∧ a = M + 4)
        ∨ (r = 7 ∧ c = 4 ∧ b = 0 ∧ a = M + 5)
        ∨ (r = 7 ∧ c = 5 ∧ b = 1 ∧ a = M + 4) := by omega
    rcases hcase with ⟨hr', hc', hb', ha'⟩ | ⟨hr', hc', hb', ha'⟩ | ⟨hr', hc', hb', ha'⟩
    · subst hr'; subst hc'; subst hb'; subst ha'
      exact le_trans (rNeg_r6 M hM) (rtie_maximal_general M 6 (by omega) 0 (by omega))
    · subst hr'; subst hc'; subst hb'; subst ha'
      exact le_trans (rNeg_r7a M hM) (rtie_maximal_general M 7 (by omega) 0 (by omega))
    · subst hr'; subst hc'; subst hb'; subst ha'
      exact le_trans (rNeg_r7b M hM) (rtie_maximal_general M 7 (by omega) 0 (by omega))

end Step3
end R3Cert
