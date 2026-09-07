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

/-! ### Residue 10: the δ = −1 edge `negEdge` (the single fixed maximizer edge) and its trade argmax. -/

/-- The `δ = b - c = -1` edge (`b = c - 1`, `c ≥ 1`): the fixed maximizer edge for residue 10. -/
def negEdge (M c : ℕ) : List Hub := hubState (M - c) (c - 1) c

/-- `negEdge` trade step (`c ≥ 1`, `c + 1 ≤ M`): one trade is `Aobj`-non-increasing iff
    `hubTradeStop (M-c) (c-1) c`.  Uses the general `hub_trade_le`/`hub_trade_stop_iff`. -/
theorem neg_trade_le (M c : ℕ) (hc1 : 1 ≤ c) (hcM : c + 1 ≤ M)
    (hpos : 0 < (M - c) + (c - 1) + c) :
    Aobj (backboneU (negEdge M (c + 1))) ≤ Aobj (backboneU (negEdge M c))
      ↔ hubTradeStop (M - c) (c - 1) c := by
  have hst : negEdge M (c + 1) = hubState ((M - c) - 1) ((c - 1) + 1) (c + 1) := by
    unfold negEdge
    rw [show M - (c + 1) = (M - c) - 1 by omega, show (c + 1) - 1 = (c - 1) + 1 by omega]
  rw [hst, negEdge, hub_trade_le _ _ _ (by omega) hpos, hub_trade_stop_iff _ _ _ (by omega) hpos]

theorem neg_step_up (M c : ℕ) (hc1 : 1 ≤ c) (hcM : c + 1 ≤ M) (hpos : 0 < (M - c) + (c - 1) + c)
    (h : ¬ hubTradeStop (M - c) (c - 1) c) :
    Aobj (backboneU (negEdge M c)) ≤ Aobj (backboneU (negEdge M (c + 1))) := by
  have hiff := neg_trade_le M c hc1 hcM hpos
  have hnot : ¬ (Aobj (backboneU (negEdge M (c + 1))) ≤ Aobj (backboneU (negEdge M c))) :=
    fun hle => h (hiff.mp hle)
  linarith [not_le.mp hnot]

theorem neg_step_down (M c : ℕ) (hc1 : 1 ≤ c) (hcM : c + 1 ≤ M) (hpos : 0 < (M - c) + (c - 1) + c)
    (h : hubTradeStop (M - c) (c - 1) c) :
    Aobj (backboneU (negEdge M (c + 1))) ≤ Aobj (backboneU (negEdge M c)) :=
  (neg_trade_le M c hc1 hcM hpos).mpr h

/-- Persistence up the `negEdge` edge: `hubTradeStop` at `c` implies it at every reachable `c' ≥ c`. -/
theorem neg_hubTradeStop_up (M cstar : ℕ) (hcs1 : 1 ≤ cstar)
    (hstop : hubTradeStop (M - cstar) (cstar - 1) cstar) :
    ∀ c, cstar ≤ c → c ≤ M → hubTradeStop (M - c) (c - 1) c := by
  intro c hcs
  induction c, hcs using Nat.le_induction with
  | base => intro _; exact hstop
  | succ c hcs ih =>
      intro hcM
      have := hubTradeStop_persists (M - c) (c - 1) c (by omega) (ih (by omega))
      rwa [show M - c - 1 = M - (c + 1) by omega, show c - 1 + 1 = (c + 1) - 1 by omega] at this

theorem neg_up_chain (M c0 : ℕ) (hc01 : 1 ≤ c0) :
    ∀ c, c0 ≤ c → c ≤ M → (∀ i, c0 ≤ i → i < c → ¬ hubTradeStop (M - i) (i - 1) i) →
      Aobj (backboneU (negEdge M c0)) ≤ Aobj (backboneU (negEdge M c)) := by
  intro c hc0
  induction c, hc0 using Nat.le_induction with
  | base => intro _ _; exact le_refl _
  | succ c hc0 ih =>
      intro hcM hlt
      have h1 := ih (by omega) (fun i hi hic => hlt i hi (by omega))
      have h2 := neg_step_up M c (by omega) (by omega) (by omega) (hlt c hc0 (by omega))
      linarith

theorem neg_down_chain (M cstar : ℕ) (hcs1 : 1 ≤ cstar) (hcsM : cstar ≤ M)
    (hstop : hubTradeStop (M - cstar) (cstar - 1) cstar) :
    ∀ c, cstar ≤ c → c ≤ M →
      Aobj (backboneU (negEdge M c)) ≤ Aobj (backboneU (negEdge M cstar)) := by
  intro c hcs
  induction c, hcs using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ c hcs ih =>
      intro hcM
      have hstopc : hubTradeStop (M - c) (c - 1) c := neg_hubTradeStop_up M cstar hcs1 hstop c hcs (by omega)
      have h2 := neg_step_down M c (by omega) (by omega) (by omega) hstopc
      have h1 := ih (by omega)
      linarith

/-- **The `negEdge` trade argmax**: given `cstar` (`≥ 1`) is the least trade count where the trade stops,
    `negEdge M cstar` dominates every `negEdge M c` with `1 ≤ c ≤ M`. -/
theorem neg_maximal (M cstar : ℕ) (hcs1 : 1 ≤ cstar) (hcsM : cstar ≤ M)
    (hstop : hubTradeStop (M - cstar) (cstar - 1) cstar)
    (hlt : ∀ i, 1 ≤ i → i < cstar → ¬ hubTradeStop (M - i) (i - 1) i) :
    ∀ c, 1 ≤ c → c ≤ M → Aobj (backboneU (negEdge M c)) ≤ Aobj (backboneU (negEdge M cstar)) := by
  intro c hc1 hcM
  by_cases hle : c ≤ cstar
  · exact neg_up_chain M c hc1 cstar hle hcsM (fun i hi hic => hlt i (by omega) hic)
  · exact neg_down_chain M cstar hcs1 hcsM hstop c (by omega) hcM

/-- The trade always stops on the `negEdge` edge at some `c ≥ 1` (`c = M + 20`, where `a = 0`). -/
theorem neg_hubTradeStop_exists (M : ℕ) : ∃ c, 1 ≤ c ∧ hubTradeStop (M - c) (c - 1) c := by
  refine ⟨M + 20, by omega, ?_⟩
  simp only [hubTradeStop, show M - (M + 20) = 0 by omega, Nat.cast_zero]
  push_cast
  nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]

/-- The least `c` at which the trade stops on the `negEdge` edge (`≥ 1` by `neg_hubTradeStop_exists`). -/
noncomputable def negLeastStop (M : ℕ) : ℕ := Nat.find (neg_hubTradeStop_exists M)

theorem negLeastStop_one (M : ℕ) : 1 ≤ negLeastStop M := (Nat.find_spec (neg_hubTradeStop_exists M)).1

theorem negLeastStop_spec (M : ℕ) :
    hubTradeStop (M - negLeastStop M) (negLeastStop M - 1) (negLeastStop M) :=
  (Nat.find_spec (neg_hubTradeStop_exists M)).2

theorem negLeastStop_min (M : ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < negLeastStop M) :
    ¬ hubTradeStop (M - i) (i - 1) i :=
  fun h => Nat.find_min (neg_hubTradeStop_exists M) hi ⟨hi1, h⟩

/-- The `negEdge` trade argmax (least stop, capped at `M`). -/
noncomputable def negMOf (M : ℕ) : ℕ := min M (negLeastStop M)

theorem negMOf_le (M : ℕ) : negMOf M ≤ M := min_le_left _ _

theorem negMOf_one (M : ℕ) (hM : 1 ≤ M) : 1 ≤ negMOf M :=
  le_min hM (negLeastStop_one M)

/-- **The `negEdge` edge is maximized at `negMOf M`** (all `M ≥ 1`).  Interior: `neg_maximal` at the least
    stop; boundary: `neg_up_chain` to `c = M`. -/
theorem neg_maximal_general (M : ℕ) (hM : 1 ≤ M) :
    ∀ c, 1 ≤ c → c ≤ M → Aobj (backboneU (negEdge M c)) ≤ Aobj (backboneU (negEdge M (negMOf M))) := by
  intro c hc1 hcM
  by_cases hle : negLeastStop M ≤ M
  · have hmOf : negMOf M = negLeastStop M := min_eq_right hle
    rw [hmOf]
    exact neg_maximal M (negLeastStop M) (negLeastStop_one M) hle (negLeastStop_spec M)
      (fun i hi1 hiL => negLeastStop_min M hi1 hiL) c hc1 hcM
  · have hmOf : negMOf M = M := min_eq_left (by omega)
    rw [hmOf]
    exact neg_up_chain M c hc1 M hcM (le_refl M)
      (fun i hi hiM => negLeastStop_min M (by omega) (by omega))

/-! ### The bulk-link, the `c = 0` edge case, and the residue-10 envelope. -/

/-- **Bulk-link**: the `δ = 10` edge `rtieState M 10 c` is dominated by the `δ = -1` edge
    `negEdge (M+9) c` (one reverse bulk swap; the swap does not help at `M ≥ 22`, `1 ≤ c ≤ 5`). -/
theorem neg_bulk_link (M c : ℕ) (hM : 22 ≤ M) (hc1 : 1 ≤ c) (hc5 : c ≤ 5) :
    Aobj (backboneU (rtieState M 10 c)) ≤ Aobj (backboneU (negEdge (M + 9) c)) := by
  have hbulk : bulkStopABC (M + 9 - c) (c - 1) c := by
    have hMR : (22 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hcm : c ≤ M + 9 := by omega
    simp only [bulkStopABC]
    push_cast [Nat.cast_sub hcm, Nat.cast_sub hc1]
    interval_cases c <;> nlinarith [hMR, sq_nonneg ((M : ℝ) - 22)]
  have hrt : rtieState M 10 c = hubState ((M + 9 - c) - 9) ((c - 1) + 11) c := by
    unfold rtieState
    rw [show M - c = (M + 9 - c) - 9 by omega, show c + 10 = (c - 1) + 11 by omega]
  rw [hrt, negEdge]
  exact (hub_bulk_le (M + 9 - c) (c - 1) c (by omega) (by omega)).mpr
    ((hub_bulk_stop_iff (M + 9 - c) (c - 1) c (by omega) (by omega)).mpr hbulk)

/-- The `c = 0` edge case for residue 10: `hubState M 10 0 = rtieState M 10 0 ≤ negEdge (M+9) 1`
    (`= hubState (M+8) 0 1`), a symbolic-`M` comparison (`M ≥ 22`). -/
theorem rNeg_c0 (M : ℕ) (hM : 22 ≤ M) :
    Aobj (backboneU (rtieState M 10 0)) ≤ Aobj (backboneU (negEdge (M + 9) 1)) := by
  have hMR : (22 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hP : (0 : ℝ) < (621 / 64 : ℝ) ^ M := by positivity
  have key : (513 / 80 : ℝ) ^ (10:ℕ) * (3 / 2) ^ (0:ℕ)
        * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 10) * 23)) + (10:ℝ) * (3 / (((M : ℝ) + 10) * 19))))
      ≤ (621 / 64) ^ 8 * ((513 / 80) ^ (0:ℕ) * (3 / 2) ^ (1:ℕ)
        * (1 + (((M : ℝ) + 8) * (3 / (((M : ℝ) + 9) * 23))
            + (1:ℝ) * (1 / (3 * ((M : ℝ) + 9)))))) := by
    have h9 : (0 : ℝ) < (M : ℝ) + 9 := by linarith
    have h10 : (0 : ℝ) < (M : ℝ) + 10 := by linarith
    rw [← sub_nonneg]; field_simp; nlinarith [hMR, sq_nonneg ((M : ℝ) - 22)]
  rw [rtieState, negEdge, show M - 0 = M by omega, show M + 9 - 1 = M + 8 by omega,
    show (1:ℕ) - 1 = 0 by omega,
    hub_Aobj_eq M 10 0 (by omega), hub_Aobj_eq (M + 8) 0 1 (by omega),
    show (621 / 64 : ℝ) ^ (M + 8) = (621 / 64) ^ M * (621 / 64) ^ 8 from pow_add _ _ _]
  calc (621 / 64 : ℝ) ^ M * (513 / 80) ^ 10 * (3 / 2) ^ 0
          * (1 + (((M : ℕ) : ℝ) * (3 / (((M + 10 + 0 : ℕ) : ℝ) * 23))
              + ((10:ℕ) : ℝ) * (3 / (((M + 10 + 0 : ℕ) : ℝ) * 19))
              + ((0:ℕ) : ℝ) * (1 / (3 * ((M + 10 + 0 : ℕ) : ℝ)))))
        = (621 / 64 : ℝ) ^ M * ((513 / 80) ^ (10:ℕ) * (3 / 2) ^ (0:ℕ)
            * (1 + ((M : ℝ) * (3 / (((M : ℝ) + 10) * 23))
                + (10:ℝ) * (3 / (((M : ℝ) + 10) * 19))))) := by push_cast; ring
      _ ≤ (621 / 64 : ℝ) ^ M * ((621 / 64) ^ 8 * ((513 / 80) ^ (0:ℕ) * (3 / 2) ^ (1:ℕ)
            * (1 + (((M : ℝ) + 8) * (3 / (((M : ℝ) + 9) * 23))
                + (1:ℝ) * (1 / (3 * ((M : ℝ) + 9))))))) :=
          mul_le_mul_of_nonneg_left key hP.le
      _ = (621 / 64 : ℝ) ^ M * (621 / 64) ^ 8 * (513 / 80) ^ 0 * (3 / 2) ^ 1
            * (1 + (((M + 8 : ℕ) : ℝ) * (3 / (((M + 8 + 0 + 1 : ℕ) : ℝ) * 23))
                + ((0:ℕ) : ℝ) * (3 / (((M + 8 + 0 + 1 : ℕ) : ℝ) * 19))
                + ((1:ℕ) : ℝ) * (1 / (3 * ((M + 8 + 0 + 1 : ℕ) : ℝ))))) := by push_cast; ring

/-- **The residue-10 single-hub envelope (`Mn ≥ 31`).**  Every Balanced single hub at size `11·Mn - 8`
    (residue 10) is dominated by the `δ = -1` tie `negEdge Mn (negMOf Mn)`.  Case `δ = -1` (`b = c-1`) →
    `neg_maximal_general`; case `δ ≥ 10` (`b ≥ c+10`) → `col_le_edgeR` to the `δ=10` edge, then the
    bulk-link (`c ≥ 1`) or `rNeg_c0` (`c = 0`), then `neg_maximal_general`. -/
theorem singleHubR_le_tie_10 (a b c Mn : ℕ) (hc : c ≤ 5) (hMn : 31 ≤ Mn)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * Mn - 9) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (negEdge Mn (negMOf Mn))) := by
  by_cases hd : b + 1 = c
  · have hc1 : 1 ≤ c := by omega
    have heq : hubState a b c = negEdge Mn c := by
      unfold negEdge; congr 1 <;> omega
    rw [heq]
    exact neg_maximal_general Mn (by omega) c hc1 (by omega)
  · have hbge : c + 10 ≤ b := by omega
    obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c (Mn - 9) 10 hbge (by omega)
    rw [heq]
    have h1 := col_le_edgeR (Mn - 9) 10 c ((b - c - 10) / 11) (by omega) (by omega) hc htK
    by_cases hc0 : c = 0
    · subst hc0
      have hbl := rNeg_c0 (Mn - 9) (by omega)
      rw [show Mn - 9 + 9 = Mn by omega] at hbl
      have h3 := neg_maximal_general Mn (by omega) 1 (by omega) (by omega)
      linarith
    · have hc1 : 1 ≤ c := by omega
      have hbl := neg_bulk_link (Mn - 9) c (by omega) hc1 hc
      rw [show Mn - 9 + 9 = Mn by omega] at hbl
      have h3 := neg_maximal_general Mn (by omega) c hc1 (by omega)
      linarith

/-! ### The generalized offset edge `offEdge` (δ = −off) and its trade argmax, for residues 8, 9. -/

/-- The `δ = b - c = -off` edge (`b = c - off`, `c ≥ off`).  `off = 1` is `negEdge`; the low edge for
    residue `r` is `off = 11 - r` (off = 3 for r = 8, off = 2 for r = 9). -/
def offEdge (M off c : ℕ) : List Hub := hubState (M - c) (c - off) c

theorem off_trade_le (M off c : ℕ) (hco : off ≤ c) (hcM : c + 1 ≤ M)
    (hpos : 0 < (M - c) + (c - off) + c) :
    Aobj (backboneU (offEdge M off (c + 1))) ≤ Aobj (backboneU (offEdge M off c))
      ↔ hubTradeStop (M - c) (c - off) c := by
  have hst : offEdge M off (c + 1) = hubState ((M - c) - 1) ((c - off) + 1) (c + 1) := by
    unfold offEdge
    rw [show M - (c + 1) = (M - c) - 1 by omega, show (c + 1) - off = (c - off) + 1 by omega]
  rw [hst, offEdge, hub_trade_le _ _ _ (by omega) hpos, hub_trade_stop_iff _ _ _ (by omega) hpos]

theorem off_step_up (M off c : ℕ) (hco : off ≤ c) (hcM : c + 1 ≤ M) (hpos : 0 < (M - c) + (c - off) + c)
    (h : ¬ hubTradeStop (M - c) (c - off) c) :
    Aobj (backboneU (offEdge M off c)) ≤ Aobj (backboneU (offEdge M off (c + 1))) := by
  have hiff := off_trade_le M off c hco hcM hpos
  have hnot : ¬ (Aobj (backboneU (offEdge M off (c + 1))) ≤ Aobj (backboneU (offEdge M off c))) :=
    fun hle => h (hiff.mp hle)
  linarith [not_le.mp hnot]

theorem off_step_down (M off c : ℕ) (hco : off ≤ c) (hcM : c + 1 ≤ M) (hpos : 0 < (M - c) + (c - off) + c)
    (h : hubTradeStop (M - c) (c - off) c) :
    Aobj (backboneU (offEdge M off (c + 1))) ≤ Aobj (backboneU (offEdge M off c)) :=
  (off_trade_le M off c hco hcM hpos).mpr h

theorem off_hubTradeStop_up (M off cstar : ℕ) (hcso : off ≤ cstar)
    (hstop : hubTradeStop (M - cstar) (cstar - off) cstar) :
    ∀ c, cstar ≤ c → c ≤ M → hubTradeStop (M - c) (c - off) c := by
  intro c hcs
  induction c, hcs using Nat.le_induction with
  | base => intro _; exact hstop
  | succ c hcs ih =>
      intro hcM
      have := hubTradeStop_persists (M - c) (c - off) c (by omega) (ih (by omega))
      rwa [show M - c - 1 = M - (c + 1) by omega, show c - off + 1 = (c + 1) - off by omega] at this

theorem off_up_chain (M off c0 : ℕ) (hc0o : off ≤ c0) :
    ∀ c, c0 ≤ c → c ≤ M → (∀ i, c0 ≤ i → i < c → ¬ hubTradeStop (M - i) (i - off) i) →
      Aobj (backboneU (offEdge M off c0)) ≤ Aobj (backboneU (offEdge M off c)) := by
  intro c hc0
  induction c, hc0 using Nat.le_induction with
  | base => intro _ _; exact le_refl _
  | succ c hc0 ih =>
      intro hcM hlt
      have h1 := ih (by omega) (fun i hi hic => hlt i hi (by omega))
      have h2 := off_step_up M off c (by omega) (by omega) (by omega) (hlt c hc0 (by omega))
      linarith

theorem off_down_chain (M off cstar : ℕ) (hcso : off ≤ cstar) (hcsM : cstar ≤ M)
    (hstop : hubTradeStop (M - cstar) (cstar - off) cstar) :
    ∀ c, cstar ≤ c → c ≤ M →
      Aobj (backboneU (offEdge M off c)) ≤ Aobj (backboneU (offEdge M off cstar)) := by
  intro c hcs
  induction c, hcs using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ c hcs ih =>
      intro hcM
      have hstopc : hubTradeStop (M - c) (c - off) c := off_hubTradeStop_up M off cstar hcso hstop c hcs (by omega)
      have h2 := off_step_down M off c (by omega) (by omega) (by omega) hstopc
      have h1 := ih (by omega)
      linarith

theorem off_maximal (M off cstar : ℕ) (hcso : off ≤ cstar) (hcsM : cstar ≤ M)
    (hstop : hubTradeStop (M - cstar) (cstar - off) cstar)
    (hlt : ∀ i, off ≤ i → i < cstar → ¬ hubTradeStop (M - i) (i - off) i) :
    ∀ c, off ≤ c → c ≤ M → Aobj (backboneU (offEdge M off c)) ≤ Aobj (backboneU (offEdge M off cstar)) := by
  intro c hco hcM
  by_cases hle : c ≤ cstar
  · exact off_up_chain M off c hco cstar hle hcsM (fun i hi hic => hlt i (by omega) hic)
  · exact off_down_chain M off cstar hcso hcsM hstop c (by omega) hcM

theorem off_hubTradeStop_exists (M off : ℕ) : ∃ c, off ≤ c ∧ hubTradeStop (M - c) (c - off) c := by
  refine ⟨M + off + 20, by omega, ?_⟩
  have h1 : M - (M + off + 20) = 0 := by omega
  have h2 : (M + off + 20) - off = M + 20 := by omega
  simp only [hubTradeStop, h1, h2, Nat.cast_zero]
  push_cast
  nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ)), (Nat.cast_nonneg off : (0:ℝ) ≤ (off:ℝ)),
    mul_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ)) (Nat.cast_nonneg off : (0:ℝ) ≤ (off:ℝ))]

noncomputable def offLeastStop (M off : ℕ) : ℕ := Nat.find (off_hubTradeStop_exists M off)

theorem offLeastStop_ge (M off : ℕ) : off ≤ offLeastStop M off :=
  (Nat.find_spec (off_hubTradeStop_exists M off)).1

theorem offLeastStop_spec (M off : ℕ) :
    hubTradeStop (M - offLeastStop M off) (offLeastStop M off - off) (offLeastStop M off) :=
  (Nat.find_spec (off_hubTradeStop_exists M off)).2

theorem offLeastStop_min (M off : ℕ) {i : ℕ} (hio : off ≤ i) (hi : i < offLeastStop M off) :
    ¬ hubTradeStop (M - i) (i - off) i :=
  fun h => Nat.find_min (off_hubTradeStop_exists M off) hi ⟨hio, h⟩

/-- The `offEdge` trade argmax (least stop, capped at `M`). -/
noncomputable def offMOf (M off : ℕ) : ℕ := min M (offLeastStop M off)

theorem offMOf_le (M off : ℕ) : offMOf M off ≤ M := min_le_left _ _

theorem offMOf_ge (M off : ℕ) (hoM : off ≤ M) : off ≤ offMOf M off :=
  le_min hoM (offLeastStop_ge M off)

/-- **The `offEdge` edge is maximized at `offMOf M off`** (all `off ≤ M`). -/
theorem off_maximal_general (M off : ℕ) (hoM : off ≤ M) :
    ∀ c, off ≤ c → c ≤ M →
      Aobj (backboneU (offEdge M off c)) ≤ Aobj (backboneU (offEdge M off (offMOf M off))) := by
  intro c hco hcM
  by_cases hle : offLeastStop M off ≤ M
  · have hmOf : offMOf M off = offLeastStop M off := min_eq_right hle
    rw [hmOf]
    exact off_maximal M off (offLeastStop M off) (offLeastStop_ge M off) hle (offLeastStop_spec M off)
      (fun i hio hiL => offLeastStop_min M off hio hiL) c hco hcM
  · have hmOf : offMOf M off = M := min_eq_left (by omega)
    rw [hmOf]
    exact off_up_chain M off c hco M hcM (le_refl M)
      (fun i hi hiM => offLeastStop_min M off (by omega) (by omega))

/-- **The residue-8/9 single-hub envelope (`Mn ≥ 40`).**  For `r ∈ {8, 9}` the per-size maximizer is the
    MAX of two edges: the low edge `offEdge Mn (11-r) (offMOf ..)` (`δ = r-11`) and the high edge
    `rtieState (Mn-9) r (rMOf ..)` (`δ = r`).  Every Balanced single hub at size `11·Mn - 9·(11-r)` is
    dominated by that max: the `δ = r-11` configs by the low-edge argmax, the `δ ≥ r` configs by the
    high-edge argmax (`col_le_edgeR` + `rtie_maximal_general`).  Mechanically closable -- the "oscillation"
    is just this two-edge max, NOT Pant-open. -/
theorem singleHubR_le_tie_89 (a b c Mn r : ℕ) (hr8 : 8 ≤ r) (hr9 : r ≤ 9) (hc : c ≤ 5) (hMn : 40 ≤ Mn)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * Mn - 9 * (11 - r)) :
    Aobj (backboneU (hubState a b c))
      ≤ max (Aobj (backboneU (offEdge Mn (11 - r) (offMOf Mn (11 - r)))))
            (Aobj (backboneU (rtieState (Mn - 9) r (rMOf (Mn - 9) r)))) := by
  by_cases hlow : b + (11 - r) = c
  · have hco : 11 - r ≤ c := by omega
    have heq : hubState a b c = offEdge Mn (11 - r) c := by
      unfold offEdge; congr 1 <;> omega
    rw [heq]
    exact le_max_of_le_left (off_maximal_general Mn (11 - r) (by omega) c hco (by omega))
  · have hbge : c + r ≤ b := by omega
    obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c (Mn - 9) r hbge (by omega)
    rw [heq]
    have h1 := col_le_edgeR (Mn - 9) r c ((b - c - r) / 11) (by omega) (by omega) hc htK
    have h2 := rtie_maximal_general (Mn - 9) r (by omega) c (by omega)
    exact le_max_of_le_right (le_trans h1 h2)

/-! ### The tie cherry counts are valid Balanced loads (`≤ 5`), so every tie state is Balanced. -/

/-- The shifted-edge argmax `rMOf M r ≤ 5` (`M ≥ 5`): the trade stops by `c = 5` on `rtieState`. -/
theorem rMOf_le_five (M r : ℕ) (hM : 5 ≤ M) : rMOf M r ≤ 5 := by
  have h : hubTradeStop (M - 5) (5 + r) 5 := by
    have hMR : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hrR : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    simp only [hubTradeStop]
    push_cast [Nat.cast_sub hM]
    nlinarith [hMR, hrR, sq_nonneg ((M : ℝ) - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ (M : ℝ) - 5) hrR]
  exact le_trans (min_le_right _ _) (Nat.find_le h)

/-- The `negEdge` argmax `negMOf M ≤ 5` (`M ≥ 5`). -/
theorem negMOf_le_five (M : ℕ) (hM : 5 ≤ M) : negMOf M ≤ 5 := by
  have h : hubTradeStop (M - 5) (5 - 1) 5 := by
    have hMR : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    simp only [hubTradeStop, show (5:ℕ) - 1 = 4 by omega]
    push_cast [Nat.cast_sub hM]
    nlinarith [hMR, sq_nonneg (2964 * ((M : ℝ) - 5) - 4796), sq_nonneg ((M : ℝ) - 5)]
  exact le_trans (min_le_right _ _) (Nat.find_le ⟨by omega, h⟩)

/-- The `offEdge` argmax `offMOf M off ≤ 5` (`M ≥ 11`, `off ≤ 3` -- the residue-8/9 usage, `off = 11-r`). -/
theorem offMOf_le_five (M off : ℕ) (hM : 11 ≤ M) (hoff : off ≤ 3) : offMOf M off ≤ 5 := by
  have hMR : (11 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h : hubTradeStop (M - 5) (5 - off) 5 := by
    interval_cases off <;>
      · simp only [hubTradeStop]
        push_cast [Nat.cast_sub (show 5 ≤ M by omega)]
        nlinarith [hMR, sq_nonneg ((M : ℝ) - 11)]
  exact le_trans (min_le_right _ _) (Nat.find_le ⟨by omega, h⟩)

set_option maxHeartbeats 4000000 in
/-- Small-M finite patch, residue 1 (`1 ≤ M ≤ 21`, no sub-edge). -/
theorem singleHubR_le_tie_small_r1 (a b c M : ℕ) (hc : c ≤ 5) (hM1 : 1 ≤ M) (hM : M ≤ 21)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * 1) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M 1 (rMOf M 1))) := by
  have hbge : c + 1 ≤ b := by omega
  obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M 1 hbge (by omega)
  rw [heq]
  set t := (b - c - 1) / 11 with htdef
  have ht2 : t ≤ 2 := by omega
  clear_value t
  interval_cases M
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 1 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 1 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)

set_option maxHeartbeats 4000000 in
/-- Small-M finite patch, residue 2 (`1 ≤ M ≤ 21`, no sub-edge). -/
theorem singleHubR_le_tie_small_r2 (a b c M : ℕ) (hc : c ≤ 5) (hM1 : 1 ≤ M) (hM : M ≤ 21)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * 2) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M 2 (rMOf M 2))) := by
  have hbge : c + 2 ≤ b := by omega
  obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M 2 hbge (by omega)
  rw [heq]
  set t := (b - c - 2) / 11 with htdef
  have ht2 : t ≤ 2 := by omega
  clear_value t
  interval_cases M
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 2 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 2 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)

set_option maxHeartbeats 4000000 in
/-- Small-M finite patch, residue 3 (`1 ≤ M ≤ 21`, no sub-edge). -/
theorem singleHubR_le_tie_small_r3 (a b c M : ℕ) (hc : c ≤ 5) (hM1 : 1 ≤ M) (hM : M ≤ 21)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * 3) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M 3 (rMOf M 3))) := by
  have hbge : c + 3 ≤ b := by omega
  obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M 3 hbge (by omega)
  rw [heq]
  set t := (b - c - 3) / 11 with htdef
  have ht2 : t ≤ 2 := by omega
  clear_value t
  interval_cases M
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 3 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 3 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)

set_option maxHeartbeats 4000000 in
/-- Small-M finite patch, residue 4 (`1 ≤ M ≤ 21`, no sub-edge). -/
theorem singleHubR_le_tie_small_r4 (a b c M : ℕ) (hc : c ≤ 5) (hM1 : 1 ≤ M) (hM : M ≤ 21)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * 4) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M 4 (rMOf M 4))) := by
  have hbge : c + 4 ≤ b := by omega
  obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M 4 hbge (by omega)
  rw [heq]
  set t := (b - c - 4) / 11 with htdef
  have ht2 : t ≤ 2 := by omega
  clear_value t
  interval_cases M
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 5 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 4 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 4 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)

set_option maxHeartbeats 4000000 in
/-- Small-M finite patch, residue 5 (`1 ≤ M ≤ 21`, no sub-edge). -/
theorem singleHubR_le_tie_small_r5 (a b c M : ℕ) (hc : c ≤ 5) (hM1 : 1 ≤ M) (hM : M ≤ 21)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * 5) :
    Aobj (backboneU (hubState a b c)) ≤ Aobj (backboneU (rtieState M 5 (rMOf M 5))) := by
  have hbge : c + 5 ≤ b := by omega
  obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M 5 hbge (by omega)
  rw [heq]
  set t := (b - c - 5) / 11 with htdef
  have ht2 : t ≤ 2 := by omega
  clear_value t
  interval_cases M
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 4 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 3 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 2 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 1 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
  · interval_cases c <;> interval_cases t <;>
      first
      | omega
      | (rw [colStateR_zero]; exact rtie_maximal_general _ 5 (by norm_num) _ (by norm_num))
      | (refine le_trans ?_ (rtie_maximal_general _ 5 (by norm_num) 0 (by norm_num));
         rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)

set_option maxHeartbeats 4000000 in
/-- Small-M finite patch, residue 6 (two-edge: sub-edge δ=-5 + high edge δ≥6), `1 ≤ M ≤ 21`. -/
theorem singleHubR_le_tie_small_r6 (a b c M : ℕ) (hc : c ≤ 5) (hM1 : 1 ≤ M) (hM : M ≤ 21)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * 6) :
    Aobj (backboneU (hubState a b c))
      ≤ max (Aobj (backboneU (offEdge (M + 9) 5 (offMOf (M + 9) 5))))
            (Aobj (backboneU (rtieState M 6 (rMOf M 6)))) := by
  by_cases hlow : b + 5 = c
  · obtain ⟨hc5, hb0, ha⟩ : c = 5 ∧ b = 0 ∧ a = M + 4 := by omega
    subst hc5; subst hb0; subst ha
    rw [show hubState (M + 4) 0 5 = offEdge (M + 9) 5 5 from by unfold offEdge; congr 1 <;> omega]
    exact le_max_of_le_left (off_maximal_general (M + 9) 5 (by omega) 5 (by omega) (by omega))
  · have hbge : c + 6 ≤ b := by omega
    obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M 6 hbge (by omega)
    rw [heq]; apply le_max_of_le_right
    set t := (b - c - 6) / 11 with htdef
    have ht2 : t ≤ 2 := by omega
    clear_value t
    interval_cases M
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 2 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 4 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 4 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 4 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 4 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 2 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 2 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 6 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 6 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)

set_option maxHeartbeats 4000000 in
/-- Small-M finite patch, residue 7 (two-edge: sub-edge δ=-4 + high edge δ≥7), `1 ≤ M ≤ 21`. -/
theorem singleHubR_le_tie_small_r7 (a b c M : ℕ) (hc : c ≤ 5) (hM1 : 1 ≤ M) (hM : M ≤ 21)
    (hsize : 11 * a + 9 * b + 2 * c = 11 * M + 9 * 7) :
    Aobj (backboneU (hubState a b c))
      ≤ max (Aobj (backboneU (offEdge (M + 9) 4 (offMOf (M + 9) 4))))
            (Aobj (backboneU (rtieState M 7 (rMOf M 7)))) := by
  by_cases hlow : b + 4 = c
  · obtain hcase : (c = 4 ∧ b = 0 ∧ a = M + 5) ∨ (c = 5 ∧ b = 1 ∧ a = M + 4) := by omega
    rcases hcase with ⟨hc', hb', ha'⟩ | ⟨hc', hb', ha'⟩
    · subst hc'; subst hb'; subst ha'
      rw [show hubState (M + 5) 0 4 = offEdge (M + 9) 4 4 from by unfold offEdge; congr 1 <;> omega]
      exact le_max_of_le_left (off_maximal_general (M + 9) 4 (by omega) 4 (by omega) (by omega))
    · subst hc'; subst hb'; subst ha'
      rw [show hubState (M + 4) 1 5 = offEdge (M + 9) 4 5 from by unfold offEdge; congr 1 <;> omega]
      exact le_max_of_le_left (off_maximal_general (M + 9) 4 (by omega) 5 (by omega) (by omega))
  · have hbge : c + 7 ≤ b := by omega
    obtain ⟨heq, htK⟩ := hubState_eq_colStateR a b c M 7 hbge (by omega)
    rw [heq]; apply le_max_of_le_right
    set t := (b - c - 7) / 11 with htdef
    have ht2 : t ≤ 2 := by omega
    clear_value t
    interval_cases M
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 2 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 4 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 4 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 3 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 2 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 2 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 2 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 1 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)
    · interval_cases c <;> interval_cases t <;>
        first
        | omega
        | (rw [colStateR_zero]; exact rtie_maximal_general _ 7 (by norm_num) _ (by norm_num))
        | (refine le_trans ?_ (rtie_maximal_general _ 7 (by norm_num) 0 (by norm_num));
           rw [colStateR, rtieState, hub_Aobj_eq _ _ _ (by norm_num), hub_Aobj_eq _ _ _ (by norm_num)]; norm_num)

end Step3
end R3Cert
