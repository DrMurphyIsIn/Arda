# Audit testimony: AND_height_floor_kernel (anduril), blind auditor A2, 2026-09-23

- pass: true
- axioms_clean: true
- statement_byte_identical: true (modulo whitespace; canonical gate `V.statement_matches` = True)
- conjecture1_proved = False

A2 audited blind: it did not read the author's notes or the A1 testimony before fixing this verdict.

## 1. Read-back of the registry statement (written before reading the artifact)

`theorem height_floor (H : ℝ) : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55 / 16 ≤ |ρ.im|`

For every real H and every complex ρ anywhere in ℂ (not just the critical strip): if Mathlib's
`riemannZeta` vanishes at ρ and 0 < Im ρ ≤ H, then Im ρ ≥ 55/16 = 3.4375. H plays no part in the
conclusion. Once the range is restricted to Im > 0, the content is: Mathlib's `riemannZeta` has no
zero with 0 < Im ρ < 55/16. The trivial zeros are real (Im = 0), so they are excluded.

## 2. Statement gate (canonical path)

- `R.load_campaign(Path('telperion/missions/anduril')).nodes['AND_height_floor_kernel']`, status draft.
- `V._normalized_statement(node, root)` =
  `theorem height_floor (H : ℝ) : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55 / 16 ≤ |ρ.im|`
- `V.statement_matches(HeightFloor.lean text, normalized)` = **True**. A separate comparison of the
  declaration heads, with whitespace collapsed, also matches.
- The artifact declares the theorem as `HeightFloor.height_floor`, inside `namespace HeightFloor`
  with `open Complex`. A probe restated the registry statement at the root namespace with no `open`,
  in the style of the Mathlib-only statement file, and closed it with `HeightFloor.height_floor H`.
  It elaborated, so the elaborated types coincide. `riemannZeta : ℂ → ℂ` is Mathlib's, not shadowed.
- `V.artifact_incompleteness_markers`: [] for the artifact and for **all 75 local modules** in its
  import closure. The walk covered the zeta_reflection, zeta_zero_localization and zero_free_bridge
  trees and left no import unresolved.

## 3. Build and axioms

- `leanlock.sh lake build HeightFloor`: exit 0, "Build completed successfully (8732 jobs)". The only
  warnings are deprecations (`push_neg`). No `sorry` warnings, no errors.
- Probe `#print axioms`, for each of `HeightFloor.height_floor`, the root-namespace restatement,
  `strip_clear_low`, `Boxes.G2_norm_gt` and `G2_norm_le_of_zero`: `[propext, Classical.choice, Quot.sound]`.
- The probe file was deleted after the run.

## 4. Hidden hypotheses and escape hatches

- `height_floor` takes only H. It is `ZetaZeroConfinement.no_low_zeros_of_strip_clear H strip_clear_low`,
  and `strip_clear_low` is a closed theorem.
- The only `hγ` binder found is in `ZetaZeroConfinement.zero_in_band`, which is not on the proof
  path. No hmem, hArb or hLine binders were found.
- A grep of the 75-module closure (comments stripped) for `axiom`, `opaque`, `unsafe`,
  `native_decide`, `ofReduceBool`, `implemented_by`, `@[extern]`, `sorry`, `admit` and `sorryAx`
  found **no hits**. The per-box `decide` is kernel `decide` on Int literals.

## 5. Mathematics and coverage

The proof chain:

1. Suppose Im ρ < 55/16.
2. `zeta_zero_re_mem_strip` gives 0 < Re ρ < 1. The case Re ≥ 1 falls to Mathlib's
   `riemannZeta_ne_zero_of_one_le_re`. The case Re ≤ 0 is handled by the functional-equation
   reflection ρ ↦ 1−ρ (valid because Im ≠ 0 makes Gammaℝ nonzero), which lands in Re ≥ 1.
3. Inside the strip:
   - If 1/2 ≤ Re < 1, the order-3 Euler-Maclaurin bound at N = 2 applies. A zero would force
     ‖G2‖ ≤ 23/100; the tail constant evaluates to 0.2277.
   - If 0 < Re < 1/2, the Im-preserving reflection ρ ↦ 1 − conj ρ maps the zero into the right half.
4. `G2_norm_gt` shows ‖G2‖ > 1/4 on the closed rectangle [1/2,1]×[0,55/16]. It rests on two
   σ-slabs, [1/2,3/4] and [3/4,1], times sixteen t-slabs [55j/256, 55(j+1)/256] for j = 0..15:
   **32 closed boxes**. The cover is proved in Lean by `le_total` case splits, so adjacent boxes
   share their edges and there is no gap.
5. The endpoints t = 0 and t = 55/16 are included. The input Im ≤ 55/16 comes from the strict
   Im < 55/16, and Re = 1 is excluded upstream.

mpmath (dps 20):

- The first zero is 0.5 + 14.134725141734693i, and 14.13 > 55/16.
- min |(s−1)ζ(s)| on [1/2,1]×[0,55/16] is **0.7302**, at s = 1/2, on a 121×241 grid.
- min |G2| is 0.7301.
- max |G2 − (s−1)ζ| is 0.0227, well under the proved 0.23.
- min |(s−1)ζ| on the left half [0,1/2]×[0,55/16] is 0.5, at s = 0.

The claim is true and the margins are wide.

## 6. What this establishes

It establishes, hypothesis-free and kernel-checked, that `riemannZeta` has no zero with
0 < |Im ρ| < 55/16 (the height floor), for every H. It is a finite, low-height verification. It
does **not** establish RH or anything about zeros above 55/16. conjecture1_proved = False.
