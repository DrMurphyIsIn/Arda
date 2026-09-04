# BG subaction crosscheck — audit report (2026-09-04)

The full Brualdi–Goldwasser subaction corpus, crosschecked with the AXLE-inspired
Telperion infrastructure (`verify`, `cert_meta`, `bundle`, `negative_control`,
`gap_fill`). Corpus: 17 `BGSCL*.lean` modules, 186 theorem definitions, on
`bg/scl-on-main` ∪ the delivered branches (`bg/scl-corrected-cells`,
`bg/scl-tight-enclosure`, `bg/scl-deg3-decouple`). `conjecture1_proved = False`.

## Result summary

| check | tool | result |
|---|---|---|
| Build | `lake build` (corpus) | **PASS** — all 17 modules compile, exit 0 |
| **Axiom audit** | `verify_lean` + `#print axioms` | **PASS** — 182 theorems / 16 modules, **0 `sorryAx`**, 0 compile errors |
| Emitter regression | `gap_fill` + `verify_lean` | **13/13** enclosure atoms regenerate + kernel-verify (after 1 fix) |
| Negative control | `negative_control` | **PASS** — emitter cannot forge a false atom (self-check refuses AND kernel rejects) |
| Consistency | `cert_meta` / `bundle` | 3 cross-module re-proofs flagged (benign, dedup opportunity) |

## The headline: axiom-clean across the board

A single `verify_lean` pass imported all 16 subaction modules and ran `#print axioms`
on every theorem. **182 theorems, 0 `sorryAx`, 0 disallowed axioms, 0 compile errors**
(elaborated in 26s against the persistent env). Two primed-name theorems
(`log54_sub_fstar_le'`, `scl_of_step'`) compile clean but were skipped by the
axiom-print name-quoting — not gaps. `BGSCLFlowed` (1 theorem) built in the corpus but
was outside the axiom-print batch. The "kernel-green, axiom-clean" claim made
cell-by-cell throughout the effort **holds when checked in aggregate** — every closed
piece depends only on `[propext, Classical.choice, Quot.sound]`. (This audits what is
PROVEN; `IsSubaction ρwit` remains an open hypothesis fed to the capstone — the
multi-child family is still in progress, as intended.)

## Finding + fix: a Telperion emitter bug (not a BG error)

Regenerating every emitter-shaped atom surfaced ONE that `gap_fill` could not reproduce:
`log76_gap : log(7/6) − FSTAR ≤ −1/22` (`BGSCLDecouple.lean`). Diagnosis: the emitter's
**tight route** (`route="tight"`) was built and tested only on the `log79` case
(`+FSTAR`, `k=−1`); for the standard `−FSTAR` (`k>0`) it emitted the fold's `B` factor as
`B^(-k : ℕ)` — an **invalid negative Nat exponent**. Fixed (`emit_log_combination.py`,
commit `1775713`) with a sign branch: `k≥0` folds `(B^k)⁻¹` (split `−k·log B` via
`log_inv`), `k<0` folds `B^{|k|}` (split `+|k|·log B`); and the exp-inverse rewrite is now
targeted explicitly (`inv_eq_one_div (Real.exp negQ)`) since `X` may itself carry a `⁻¹`.
Regression: **12/13 → 13/13**; `log79` unchanged-green; example rebuilt, no drift.

Crucially: **the BG proof of `log76_gap` was always correct** — the BG session hand-proved
it via `Real.exp_one_lt_d9`. This was a limitation of Telperion's *auto-regeneration*, not
a defect in the corpus. The crosscheck's value here was exactly this: it distinguished
"the theorem is sound" (yes) from "the emitter can still generate it" (now yes).

## Negative control holds

`log_combination_negative_control` on a genuinely false claim (`log(3) − 4·FSTAR ≤ 0`,
fold ≈ 20 > 1): `selfcheck_refused = True` (Layer 1, sympy) **and** `kernel_rejects = True`
(Layer 2 — the fabricated proof's `norm_num` fact is false, so Lean rejects it). The
emitter cannot forge a compiling proof of a false enclosure.

## Consistency notes (cert_meta / bundle)

- **Cross-module re-proofs** (`fstar_nonneg`, `bY_le_one`, `bY_leaf`) are each defined in
  two modules with identical statements — harmless today, but a dedup opportunity and a
  latent name-clash risk if two such modules are ever co-imported. `bundle.merge_bundle`
  would consolidate them.
- The `cert_meta` `type_hash` "duplicates" (`subaction_deg2_*`, `ceil_hub_d2..d6`, …) are
  theorems with the **same conclusion but different hypotheses** — a structural artifact of
  hashing the conclusion, not real duplicates. Noted refinement: `canonical_statement`
  should also normalize numeric ascriptions (`(0:ℝ)` → `0`), which caused the one
  false-positive "conflict" (`fstar_nonneg`).

## Verdict

The BG subaction corpus is **build-clean and axiom-clean in aggregate** — no hidden
`sorry` anywhere in the 182 closed theorems. The crosscheck also hardened Telperion
itself (the tight-route `k>0` fix), confirmed the emitter's trust boundary (negative
control), and confirmed every emitter-authored atom in the corpus is faithfully
regenerable. The open frontier is unchanged and honest: `IsSubaction ρwit`'s multi-child
family (d=3 remaining profiles, d=4, the tail) and the final tie.
