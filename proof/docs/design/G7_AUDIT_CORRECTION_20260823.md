# G7 audit correction: the merge layer is DONE (2026-08-23)

`conjecture1_proved = False`. **This corrects `G7_FORMALIZATION_FRONTIER_20260823.md` (PR #91).** That
audit made two errors, both from trusting `R47Cert.lean`'s *Phase-4a* honest-scope comment as current
status instead of reading the *Phase-5* capstone files that supersede it. Correcting the record — and it
moves the frontier **closer**, not further.

## What the audit got wrong

The audit claimed:
- *"R47 merge cells: 1 of 36"* and
- *"the per-step monotonicity SEAM is not started — nothing asserts per-step monotonicity."*

Both are **stale**. `R47Cert.lean` is Phase 4a; Phases 5–5e supersede it. Verified by reading the source
on `main` (all "no sorry" confirmed — the only `sorry` tokens are the docstring "no `sorry`" notes):

- **`R47VeeDispatch.vee_merge_le` is GENERAL and unconditional.** It takes only the certified-family
  hypotheses (`BalancedArms armsA/othersD`, `Capped dn/upc`, the ordering `hord`) — *not* a specific
  cell — and proves the merge inequality
  `AobjV upc (armsA,cA) ((armsB,cb)::dn) ≤ AobjV upc (armsA ++ 4^{k} ++ othersD ++ [5], cA) dn`
  via environment-box bounds (`sigmaArms + qSum ≤ (d−1)·3/16`, the `3/16` cap from `Capped`). This is the
  *"superseded at rational rigor, all cells"* proof the 36-cell table was replaced by — **not** 1 of 36.
- **`R47StepMono.step_mono` (Phase 5e) is proven, unconditional on the family:**
  `OrderedStep s s' → Balanced s → Capped s → Aobj (backboneU s) ≤ Aobj (backboneU s')`. The per-step
  monotonicity seam the audit called "not started" **is closed.**
- **`chain_mono` / `chain_to_normalForm`** extend it: every Balanced+Capped state rewrites *monotonically
  in `per L/∏deg`* (via `pi_utree`) to an ordered-merge normal form. The **merge-layer capstone is done.**

## The corrected G7 frontier

The bulk of the mountain I described (merge cells + per-step seam + merge assembly) is **DONE**. Per
`R47StepMono.lean`'s own honest scope, the genuinely-remaining open layers are:

1. **(L)/(B) normalization** — bringing an *arbitrary* tree INTO the Balanced+Capped family (the merge
   capstone assumes family membership; getting there is open). **This is now the highest-leverage gap.**
2. **R5/R6** — Lean-ization (single-hub tiebreak; cherry distribution/de-loading).
3. **Stratum-(i) rate port** — R1 (branching beats spiders) into Lean.
4. **R7' top assembly** — compose the merge capstone (`chain_to_normalForm`) + normalization + R5/R6 +
   rate + the bridge (`pi_utree`) + `phi_le_one` into a **top-level `conjecture1` theorem**. Verified:
   **no Lean theorem currently uses `chain_mono` toward a capstone** — the top composition is unwritten.

## Corrected verdict

G7 is **substantially more complete** than PR #91 stated. The hard mechanical core — the merge
monotonicity, unconditional on the certified family, superseding the cell table — is a genuine no-`sorry`
Lean theorem. The remaining formal work is: **normalization-into-family + R5/R6 + rate port + the
top-level composition** (which would wire the done pieces — `chain_to_normalForm`, `pi_utree`,
`phi_le_one`, LPRSC — plus the open layers into `conjecture1`).

**Process lesson (recorded):** in a multi-phase Lean campaign, a file's honest-scope comment states the
status *at its phase*; later-phase files supersede it. Audit the *capstone* files (highest phase number),
and defer "what's open" to them — not to an earlier phase's caveat. The prior audit under-credited done
work by reading Phase 4a as current. `conjecture1_proved = False`.
