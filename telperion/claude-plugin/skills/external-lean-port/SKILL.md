---
name: external-lean-port
description: Use when a residual/blocker in your Lean corpus is already PROVED unconditionally in an EXTERNAL Lean 4 repo (a different Mathlib pin) and you want to discharge yours by porting it — safely and with a real cost estimate before committing weeks. Covers the probe → sizing → drift-bellwether → full-port → wire-and-verify pipeline, with disk discipline. Use for "can we discharge X by porting repo Y?" and for de-risking a large Mathlib-version port.
---

# External-Lean-port — discharge a residual by porting proven external Lean

When a corpus residual (a `by sorry` you cannot close natively) is already an
unconditional, kernel-clean theorem in someone else's Lean 4 repo, porting can turn a
multi-quarter native proof into a days-scale mechanical port — **if** you de-risk it in
the right order. Skipping the order burns weeks on a port that hits a structural wall.

**Standing invariant: `conjecture1_proved = False`** (or your campaign's analog). A port
discharges ONE residual; it is not the headline theorem. Verify, never assert.

## The pipeline (each stage gates the next — do NOT skip ahead)

1. **PROBE (go/no-go, hours).** Find the exact source theorem. Read the ACTUAL Lean
   statement, not the README/abstract (READMEs lie — a skeptic already caught one). Check:
   is it unconditional (no RH/GRH hyp, no `sorry`, no custom axioms — read `#print axioms`
   or the repo's CI axiom-allowlist)? Does its predicate/def match yours *verbatim or
   defeq*? Is it strictly stronger than your target? Output GO/NO-GO.
2. **BRIDGE (solve the conceptual crux first, cheaply).** Prove your target *from* the
   source theorem *as a hypothesis* — a small kernel-clean reduction. This isolates the
   real mathematical subtlety (for RvM it was multiplicity-weighted → distinct-count) and
   proves it before you spend a day on the mechanical port. If the bridge won't close, the
   port is pointless.
3. **SIZE the closure.** Compute the transitive import closure of the source theorem
   (its OWN modules, Mathlib-excluded). A handful → extract; hundreds → real but bounded;
   thousands → reconsider. Report the number, not a vibe.
4. **DRIFT-BELLWETHER (the make-or-break, before the full grind).** Port the 1–2 highest-
   risk modules (the biggest/most-API-dependent, e.g. a complex-analysis core) to your pin.
   Measure drift: fixes/KLOC + taxonomy (renames vs signature changes vs REMOVED API). Flag
   any STRUCTURAL gap (a Mathlib theorem absent at your pin = a real wall, not mechanical).
   Zero structural gaps + low drift ⇒ GO on the full port with a refined estimate.
5. **FULL PORT + WIRE.** Topo-build the closure, fix drift bottom-up. Wire the bridge to
   the ported theorem; retarget the `by sorry`. Cite source module + commit for every ported
   file (zero-drift provenance).
6. **VERIFY (the only thing that counts).** The MAIN session (not the porting agent)
   re-runs `#print axioms` on the sorry-free target — over YOUR canonical statement (import
   your real defs; confirm byte-identity to the registry). Must be `[propext,
   Classical.choice, Quot.sound]`, 0 sorryAx. Leave the oleans; don't clean them before the
   independent check. Two independent sessions agreeing is the bar for a headline residual.

## Disk & agent discipline (see the .lake IR footgun)

- Porting agents CoW-clone big `.lake`s and build → IR bloats fast. Prune
  `.lake/build/ir` **between batches**, monitor `df`, floor ~40G. But: pruning ir removes
  lake's trace → the next `lake build` is a FULL rebuild. Budget for that.
- Port DOWN to your pin; do NOT bump your whole corpus's Mathlib pin for one theorem.

## Precedent (RvM, 2026-09-16)

`RvMUnboundedMeanDensity` ("no unconditional proof anywhere") discharged by porting
cc-chen-tech/riemann-pnt-lean4's Selberg superlinear-distinct bound (v4.33-rc2 → v4.32):
probe GO (defs matched verbatim) → distinct-count bridge proved kernel-clean → closure 255
modules → bellwether 0.00 hard-fixes/KLOC, no structural gaps → full port 255/255 green →
double-confirmed 3-axiom by two sessions' own `#print axioms`. Estimate went weeks→days
because the pipeline was followed in order. `conjecture1_proved = False`.
