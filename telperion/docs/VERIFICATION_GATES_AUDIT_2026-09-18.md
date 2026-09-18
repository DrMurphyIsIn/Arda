# Verification-gates audit — 2026-09-18

*`conjecture1_proved = False`. Nothing here is mathematics. This is an audit of what the
project's **gates** actually enforce, prompted by a review of the 2026-09-17/18 RH critical-path
work. The mathematics of that work held up under adversarial audit; the machinery around it was
weaker than the documents claimed. This file records every finding, what this change fixes, and
what is deliberately left open.*

## 0. The headline

Two rh nodes carried `status = "proved"` against Lean modules that **no build has ever
compiled**. `ZeroFreePolylog.lean` and `ZeroFreeElementary.lean` are terminal on the
li_positivity island: nothing imports them, they are not in `defaultTargets`, and they were
outside the axiom guard's import closure. Checking three independently built worktrees
(`arda-li-ladder`, `arda-gw-finite`, `arda-main-refreeze`), `ZeroFreePolylog.olean` and
`ZeroFreeElementary.olean` are absent from all of them while their neighbours are present.

Those nodes are `RH_zero_free_gamma5` and `RH_zero_free_polylog`. Fixed here by importing
`ZeroFreePolylog` into `AxiomGuardLiPositivity.lean`, which is a `lean_lib` in `defaultTargets`,
so `lake build` now compiles both modules and the guard prints their axioms.

**If those two files do not in fact compile, this change will turn the `li-positivity-compiles`
job red. That is the correct outcome and is the whole point: it converts an unverified claim into
a verified one or an honest failure.**

## 1. What was verified and found sound

Stated first so the rest is read in proportion.

- The three critical-path theorems (`RvMBridge2.rvm_unconditional`, `RvMBridge3.corridor_bound`,
  `RvMBridge4.limit_explicit_formula`) plus `RvMBridge.rvm_unbounded_mean_density` are closed,
  non-vacuous statements with no undischarged hypotheses. Trivial-close probes close none of them.
- The `rvm_bridge` island's CI job passed on main HEAD with all four steps green: registry drift
  check, `lake build` against the pinned zeta-23-lean, and the axiom guard.
- zeta-23-lean at pin `fbdc36bb` declares **no** Lean axioms. Its `sorry`s live in `Challenge.lean`
  and `Challenge/XiPrime.lean`, and nothing under `Zeta23/` imports them. The bridges import
  `Zeta23.Unconditional` only.
- The dependency's `PaperInputs` pattern — unproved classical inputs as fields of a Prop-valued
  structure, which keeps `#print axioms` clean while leaving theorems conditional — **is
  discharged**: `Zeta23/Final.lean` proves `paperInputs_zeta` outright, and the bridges consume the
  hypothesis-free forms. This is the check to repeat at every pin bump, because a clean
  `#print axioms` does not by itself rule it out.
- No `conjecture1_proved = True` anywhere. The goal node is a draft whose body is `sorry`.

## 2. Findings and their disposition

| # | Finding | Status |
|---|---|---|
| 1 | Two proved nodes' artifacts were never compiled by any build (§0) | **FIXED** |
| 2 | Axiom guards failed only on `sorryAx`, so a new `axiom` upstream would pass | **FIXED** |
| 3 | Guard steps ran `lake env lean ... \| tee` with no `pipefail`, masking a crash | **FIXED** |
| 4 | Nothing in CI ran the missions invariant battery | **FIXED** |
| 5 | The grant gate never asked whether an artifact PROVES its statement | **FIXED** |
| 6 | `proof-lean` daily verification dead since 2026-09-12, self-perpetuating | **FIXED** |
| 7 | mirrormere manifest fidelity note described the pre-reconcile state | **FIXED** |
| 8 | Island CI jobs are not required checks; `enforce_admins` is false | **LEFT OPEN** (§4) |
| 9 | The registry DAG's dependency edges are documentary, not mechanical | **RECORDED** (§3) |
| 10 | `proved` covers conditional and bookkeeping nodes without distinction | **RECORDED** (§3) |

### Detail on the fixes

**(2) and (3) — axiom guards.** `telperion-production.yml` already had the right idiom; the
rvm_bridge and li_positivity jobs did not. Both now assert that *every* printed `depends on axioms`
line is exactly `[propext, Classical.choice, Quot.sound]`, run under `set -euo pipefail`, and fail
if the guard printed fewer lines than it has anchors (45 for rvm_bridge, 165 for li_positivity).
That last check is the one that catches a guard which silently did not run.

**(4) — the battery never ran.** `mission verify` now runs inside the **required** `unit` job in
`telperion-test.yml`. It is pure Python and takes seconds. It covers schema and acyclicity,
artifact existence, statement containment for every proved node, closure-flag coherence, and regen
drift, across rh, mirrormere, anduril and bg.

**(5) — the gate proved nothing.** `grant_status` checked that the artifact *contains* the node's
statement, never that it *proves* it. `normalize_lean` strips a trailing `:= by sorry` before
comparing, so a stub matched **more** easily, not less. Both `grant_status` and `verify_campaign`
now reject an artifact carrying `sorry`, `admit` or `native_decide` in Lean code, with comments and
string literals stripped first so docstring prose such as "no `sorry`" is not a false positive.
Three tests cover it. Every existing campaign still verifies clean, so nothing currently proved was
resting on a stub.

**(6) — the dead daily loop.** `proof-lean.yml` re-verifies every R3Cert module with no `sorry`.
It failed on main every day from 2026-09-12. Cause, confirmed rather than guessed: the build-cache
restore step completed in **0 seconds**, a miss, so `lake build` rebuilt ~2575 theorems cold, was
killed around 104 minutes, and because the build step failed the cache **post** step was skipped,
so nothing was saved and the next run started cold again. Fixed by splitting restore from save and
saving with `if: always()`, so a partial build is always kept and consecutive runs make forward
progress. This is the Laplacian/BG layer, not RH.

## 3. Recorded, not fixed

**(9) The critical path is three independent theorems, not a chain.** `E6Bridge2` imports only
`Zeta23.Unconditional`; `E6Bridge3` four `Zeta23.*` modules; `E6Bridge4` two. **No bridge imports
another.** The E8 node sets `depends_on = [RH_rvm_unconditional, RH_corridor_bound]` and its
generated header says it consumes them, but the delivered proof does not: the upstream's own
good-height lemma and local count play those roles inside `EF_lit_zetaZeroConfig`. This costs
nothing in soundness, since each theorem is unconditional standalone, and `via = "direct"` means
`depends_on` is not load-bearing for the gate. It is left as-is because the statement file is
hash-locked and generated, and rewriting it by hand is worse than recording the fact here.
**Do not cite the registry DAG as evidence of a verified chain.**

**(10) `proved` is one word for several things.** Of the 17 proved rh nodes, four are
research-grade and unconditional (the three above plus `RH_dlvp_zero_free_region`); three carry
load-bearing hypotheses (`RH_backlund_s_log`, `RH_dlvp_region_effective`,
`RH_companion_bragg_reduction`); three are bookkeeping restatements of the Li criterion; two are
zero-free regions weaker than the 1899 de la Vallée Poussin result already in the same registry.
The node titles are individually honest. The aggregate count is not, and no doc should quote "17
proved" without this breakdown.

## 4. Deliberately left open: branch protection

Required contexts on `main` are only the six `unit` matrix cells plus `toy-compiles`,
`tangent-compiles` and `primality-compiles`. `enforce_admins` is false. So every island job,
including `rvm-bridge-compiles`, is voluntary evidence rather than a gate.

This was **not** changed, for a concrete reason: the lean workflow is path-filtered on
`telperion/**`, so a docs-only PR can never satisfy a lean-job context. Adding island jobs as
required contexts would make every docs-only PR permanently unmergeable without an admin override,
which is the footgun this repo has already hit. Raising the floor properly needs either
`paths-ignore` restructuring or skip-shim jobs, and that is its own change. Adding `mission verify`
to the already-required `unit` job (§2) raises the floor where it can be raised today.

## 5. What this change does not do

It does not run the grant pass. After the #506 merge all 15 linked-but-ungranted artifacts (6
anduril, 9 mirrormere) are present on main, so the pass is unblocked, but granting is the one
operation this project treats ceremonially — blind read-back, testimony, ledger entry — and doing
15 silently would undercut that. It is queued for the owner.
