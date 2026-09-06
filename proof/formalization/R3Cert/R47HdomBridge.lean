/-
  R3Cert.R47HdomBridge -- the Hdom sharp-domination layer, REDUCED to a crisp rate obligation (2026-09-04).

  MISSION (Part 2).  The Hdom layer of the fixed-n capstone (`R47TopCapstoneFixedN.conjecture1_of_layers_fixedN`)
  is
    Hdom : ∀ s, Balanced s → Capped s → (∀ u, ¬OrderedStep s u) →
             Aobj (backboneU s) ≤ Aobj (tie (stateSize s)).
  The rooting bound (`R47RootRate.Aobj_backbone_le_rate`) gives only `Aobj (backboneU s) ≤ (6/5)·rhoB^n`
  (`n = usize = stateSize s`), which sits ABOVE the near-star tie value `(26/23)/rhoB · rhoB^n ≈ 0.919·rhoB^n`
  (`R47NearStarValue.nearstar_Aobj_rate`).  Closing the gap is the ROOTING/Ztot TRADE-OFF — a bad-rooting
  backbone pays with a low `Ztot` — the irreducible seam a size-normalized rate bound cannot see (the
  `R47RootRate` honesty note; and the amplitude bridge `BridgeStep4l.Ztot_litRealize_le_tie` only delivers the
  WEAK `≤ rhoB^n` from `logPhi ≤ 0`, NOT the sharp `≤ (26/23)/rhoB · rhoB^n`).

  This file does NOT close that trade-off (it is genuinely open, per-size, and — since `Aobj/rhoB^n` OSCILLATES,
  the true maximizer being an `n`-dependent caterpillar family — not reducible to a single rate constant).  What
  it DOES: it isolates the EXACT residual obligation as one clean, size-normalized hypothesis and proves Hdom
  MODULO it, with the near-star tie value computed EXACTLY.  Concretely:

    * `SharpRateNF tie` — the residual: for every merge-normal Balanced+Capped `s`,
        `Aobj (backboneU s) ≤ Aobj (tie (stateSize s))`.
      (Stated directly against the tie family, so the bridge is tie-agnostic; the CONTENT this abbreviates is
       the sharp rate bound `Aobj (backboneU s) ≤ (26/23)/rhoB · rhoB^(stateSize s)` composed with the tie-value
       identity — see `sharpRate_of_rateBound` for that decomposition against the near-star tie.)
    * `Hdom_of_sharpRate` — Hdom is EXACTLY `SharpRateNF` (a definitional repackaging making the obligation
       explicit and feeding `conjecture1_of_layers_fixedN`).
    * `nearStarTie`, `nearStarTie_value` — the near-star tie family `K ↦ backboneU [(replicate K 5, 0)]` and its
       EXACT objective `(26/23)·(621/64)^K = (26/23)/rhoB · rhoB^(1+11K)`.
    * `sharpRate_of_rateBound` — the decomposition: against the near-star tie, `SharpRateNF nearStarTie` follows
       from (a) the sharp rate bound `Aobj (backboneU s) ≤ (26/23)/rhoB · rhoB^(stateSize s)` (the OPEN rooting/
       Ztot obligation) and (b) a size-fit `stateSize s = 1 + 11·(tieK (stateSize s))` witnessing that the tie
       AT THAT SIZE is a genuine near-star (the `n ≡ 1 mod 11` caterpillar-alignment subtlety).

  So the deliverable is: Hdom PROVED modulo the single crisp hypothesis `SharpRateNF`, with the tie side fully
  discharged (exact value), and the residual `SharpRateNF` pinned to the sharp rate bound + the caterpillar
  size-fit — precisely the two inputs a Gap-1 (strict-off-tie amplitude) × Gap-2 (Branch↔Aobj) closure supplies.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47TopCapstoneFixedN
import R3Cert.R47RootRate
import R3Cert.R47NearStarValue
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

/-! ### The residual Hdom obligation, isolated. -/

/-- **The sharp-rate normal-form obligation.**  For every merge-normal Balanced+Capped state `s`, the backbone
    objective is dominated by the tie AT ITS OWN SIZE.  This is exactly `Hdom` — repackaged as a named `Prop` so
    the capstone's open layer becomes an explicit, quantified obligation. -/
def SharpRateNF (tie : ℕ → UTree) : Prop :=
  ∀ s : List Hub, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) →
    Aobj (backboneU s) ≤ Aobj (tie (stateSize s))

/-- **Hdom modulo `SharpRateNF`.**  The Hdom hypothesis of `conjecture1_of_layers_fixedN` is DEFINITIONALLY
    `SharpRateNF tie`.  This lemma makes that identification explicit (and lets a downstream discharge of
    `SharpRateNF` feed the capstone directly). -/
theorem Hdom_of_sharpRate (tie : ℕ → UTree) (h : SharpRateNF tie) :
    ∀ s : List Hub, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) →
      Aobj (backboneU s) ≤ Aobj (tie (stateSize s)) := h

/-- **Conjecture 1 modulo `Hnorm` and the sharp-rate residual.**  Feeding `SharpRateNF` into the fixed-n
    capstone gives `∀ t, Aobj t ≤ Aobj (tie (usize t))` — the maximizer statement — modulo the (separate) open
    normalization layer `Hnorm`.  This is the exact conditional shape of Part 2: Hdom is discharged down to
    `SharpRateNF`. -/
theorem conjecture1_of_Hnorm_sharpRate (tie : ℕ → UTree)
    (Hnorm : ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧
        stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s))
    (Hsharp : SharpRateNF tie) :
    ∀ t : UTree, Aobj t ≤ Aobj (tie (usize t)) :=
  conjecture1_of_layers_fixedN tie Hnorm (Hdom_of_sharpRate tie Hsharp)

/-! ### The near-star tie family and its exact value. -/

/-- The near-star tie family: `K` load-5 arms on a single hub.  `usize = 1 + 11K`, `Aobj = (26/23)·(621/64)^K`. -/
noncomputable def nearStarTie (K : ℕ) : UTree := backboneU [(List.replicate K 5, 0)]

/-- **The near-star tie objective, exact and in rate form.**  `Aobj (nearStarTie K) = (26/23)/rhoB · rhoB^(1+11K)`
    for `K ≥ 1` — the asymptotic tie constant `(26/23)/rhoB ≈ 0.919` times the size rate.  (Re-export of
    `nearstar_Aobj_rate`, with `usize (nearStarTie K) = 1 + 11K`.) -/
theorem nearStarTie_value (K : ℕ) (hK : 0 < K) :
    Aobj (nearStarTie K) = (26 / 23) / rhoB * rhoB ^ usize (nearStarTie K) := by
  rw [nearStarTie]; exact nearstar_Aobj_rate K hK

/-- `usize (nearStarTie K) = 1 + 11K`. -/
theorem usize_nearStarTie (K : ℕ) : usize (nearStarTie K) = 1 + 11 * K := by
  rw [nearStarTie, usize_backbone]
  simp only [stateSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hubSize, List.length_replicate, List.sum_replicate, smul_eq_mul]
  ring

/-! ### The decomposition of the residual: sharp rate bound × caterpillar size-fit. -/

/-- **`SharpRateNF nearStarTie` from the sharp rate bound + a size-fit.**  Against the near-star tie family
    (routed by `tieK : ℕ → ℕ`, `s ↦` the near-star with `tieK (stateSize s)` arms), `SharpRateNF` reduces to two
    inputs:

      (a) `hrate` — the SHARP rate bound `Aobj (backboneU s) ≤ (26/23)/rhoB · rhoB^(stateSize s)` for every
          normal-form Balanced+Capped `s`.  This is the OPEN rooting/Ztot trade-off (the `(6/5)` rooting bound
          `Aobj_backbone_le_rate` is not tight enough; closing to `(26/23)/rhoB` needs the strict-off-tie
          amplitude margin — Gap-1 — transported to `Aobj` — Gap-2).

      (b) `hfit` — the caterpillar SIZE-FIT: at size `n = stateSize s`, the near-star with `tieK n` arms has the
          SAME size, `stateSize s = 1 + 11·(tieK (stateSize s))` and `0 < tieK (stateSize s)`.  (This is the
          `n ≡ 1 mod 11` alignment; where it fails the true maximizer is a non-near-star caterpillar, and the tie
          family must be broadened — the honest per-size subtlety.)

    Given both, the tie value is exactly `(26/23)/rhoB · rhoB^(stateSize s)`, matching the rate bound. -/
theorem sharpRate_of_rateBound (tieK : ℕ → ℕ)
    (hrate : ∀ s : List Hub, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) →
        Aobj (backboneU s) ≤ (26 / 23) / rhoB * rhoB ^ stateSize s)
    (hfit : ∀ s : List Hub, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) →
        stateSize s = 1 + 11 * (tieK (stateSize s)) ∧ 0 < tieK (stateSize s)) :
    SharpRateNF (fun n => nearStarTie (tieK n)) := by
  intro s hbal hcap hnf
  have hr := hrate s hbal hcap hnf
  obtain ⟨hsize, hKpos⟩ := hfit s hbal hcap hnf
  -- tie value at size stateSize s
  have hval := nearStarTie_value (tieK (stateSize s)) hKpos
  rw [usize_nearStarTie] at hval
  -- rhoB^(1 + 11·K) = rhoB^(stateSize s) by the size-fit
  have hpow : rhoB ^ (1 + 11 * (tieK (stateSize s))) = rhoB ^ stateSize s := by
    rw [← hsize]
  show Aobj (backboneU s) ≤ Aobj (nearStarTie (tieK (stateSize s)))
  rw [hval, hpow]
  exact hr

end Step3
end R3Cert
