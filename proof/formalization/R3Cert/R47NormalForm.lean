/-
  R3Cert.R47NormalForm -- structural theory of OrderedStep normal forms (Hdom infrastructure).

  The top capstone (R47TopCapstone.conjecture1_of_layers) reduces conjecture1 to two open layers, one of
  which (`Hdom`) quantifies over merge-NORMAL Balanced+Capped states.  Reasoning about `Hdom` needs the
  structural theory of when `OrderedStep` is stuck.  This file provides the base facts:

    * `orderedStep_nil`   -- the empty state admits no `OrderedStep` (every constructor produces a
      non-empty left side);
    * `singleHub_isNormal` -- a single-hub state `[h]` is a normal form (merge/mergeRev need two adjacent
      hubs; `tail` would need an `OrderedStep` on the empty tail).

  These are the base cases of the normal-form characterization that the eventual `Hdom` discharge (R5
  single-hub tiebreak + R6 arms/de-load + R1 rate) will build on.  It does NOT discharge `Hdom` -- that
  needs the multi-hub value bounds.  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47OrderedStep

namespace R3Cert
namespace Step3

/-- The empty hub-state admits no ordered step. -/
theorem orderedStep_nil (u : List Hub) : ¬ OrderedStep [] u := by
  intro h
  cases h

/-- A single-hub state is an `OrderedStep` normal form. -/
theorem singleHub_isNormal (h : Hub) (u : List Hub) : ¬ OrderedStep [h] u := by
  intro hst
  cases hst with
  | tail hs => exact orderedStep_nil _ hs

end Step3
end R3Cert
