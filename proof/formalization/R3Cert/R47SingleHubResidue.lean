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

end Step3
end R3Cert
