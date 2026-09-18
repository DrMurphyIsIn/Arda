/-  BraggSupport.lean -- generic list→zero-support sum bridge for the Bragg completeness step.

    The completeness theorem (`BraggH100.bragg_amplitude_h100_complete`) needs to rewrite a sum
    over the INTRINSIC zero-support Finset `s` (all zeta zeros in the T=100 box) into a sum over
    the concrete witness ordinate list.  Doing that inline for 29 witnesses blows the per-decl
    heartbeat budget (the `List.toFinset` / `DecidableEq ℂ` `whnf`s scale badly).  This file
    isolates the ENTIRE Finset/list argument into ONE generic lemma, proven once, list-length
    agnostic — so the caller only supplies the list and never pays the Finset cost again.

    Bridge: from the winding-count exhaustion data (`d ≥ 1`, `∑_{s} d = xs.length`, each on-line
    witness in `s`) plus a strictly-increasing witness list `xs`, `BoxLocalization.exhaustion_by_count`
    forces `s = (xs.map lineEmbed).toFinset`; then `List.sum_toFinset` (nodup) collapses the sum
    over `s` to the plain list sum `∑ cos(x_k · u)`.  conjecture1_proved = False. -/
import Mathlib
import RHInBox            -- lineEmbed helpers: line_toFinset_card / line_map_nodup / line_toFinset_forall
import BoxLocalization    -- exhaustion_by_count

open Complex

namespace BraggSupport

/-- **Generic Bragg sum bridge.**  Let `s` be the support of the box zeros with divisor `d`,
    `xs` a strictly-increasing list of real ordinates whose on-line points `1/2 + x·I` all lie
    in `s`, with `d ≥ 1` on `s` and the winding count `∑_{ρ∈s} d = xs.length`.  Then for any
    `u : ℝ`, the diffraction sum over EVERY box zero collapses to the witness list sum:

      `∑_{ρ ∈ s} cos(ρ.im · u) = (xs.map (fun t => cos (t·u))).sum`.

    All the Finset exhaustion / `toFinset` cost is discharged HERE, once, independent of `xs.length`.
    conjecture1_proved = False. -/
theorem sum_cos_over_zero_support_eq
    (u : ℝ) (s : Finset ℂ) (d : ℂ → ℤ) (xs : List ℝ)
    (hchain : xs.IsChain (· < ·))
    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)
    (hsum : (∑ ρ ∈ s, d ρ) = (xs.length : ℤ))
    (hmem : ∀ t ∈ xs, ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈ s) :
    (∑ ρ ∈ s, Real.cos (ρ.im * u)) = (xs.map (fun t : ℝ => Real.cos (t * u))).sum := by
  -- the on-line witness Finset
  set T : Finset ℂ := (xs.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTsub : T ⊆ s := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xs hmem
  have hTcard : T.card = xs.length := by
    rw [hTdef]; exact RHInBox.line_toFinset_card xs hchain
  -- exhaustion: s = T
  obtain ⟨hsT, _⟩ := BoxLocalization.exhaustion_by_count hTsub hTcard hd1 hsum
  -- collapse the sum over s to the list sum
  rw [hsT, hTdef]
  have hnd : (xs.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).Nodup :=
    RHInBox.line_map_nodup xs hchain
  rw [List.sum_toFinset _ hnd, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  have him : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  simp only [Function.comp_apply, him]

end BraggSupport
