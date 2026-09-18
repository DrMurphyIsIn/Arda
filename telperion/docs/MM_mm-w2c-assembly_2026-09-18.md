# MM_zeta_ordinates_not_uniformly_discrete — cross-toolchain assembly on the rvm_bridge island

**Date** 2026-09-18 · **Slug** `mm-w2c-assembly` · **Branch** `mm/w2c-assembly` (not pushed)
**Island** `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2 / Mathlib 51e6992e, via zeta-23-lean)
**Base** `origin/rh/e8-proof`

`conjecture1_proved = False`. No RH progress is claimed here, and none of the work below moves
toward RH; see "Honest scope" at the end.

## What was closed

The MIRRORMERE milestone `MM_zeta_ordinates_not_uniformly_discrete` (W2c, unconditional form) is
proved, sorry-free and kernel-clean:

```lean
theorem zeta_ordinates_not_uniformly_discrete :
    ¬ IsUniformlyDiscrete zetaOrdinates :=
  zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density rvm_unbounded_mean_density
```

in `telperion/examples/rvm_bridge/lean/W2cAssembly.lean`, namespace `RvMBridge`. The statement
line is the registry node statement of
`telperion/missions/mirrormere/lean/Statements/MM_zeta_ordinates_not_uniformly_discrete.lean`
verbatim (name + binder-free form), so the normalized-containment grant gate matches.

In words: the set of imaginary parts of the nontrivial zeros of `ζ` is **not uniformly
discrete** — for every `δ > 0` there are two distinct ordinates within `δ` of each other. With
`primeLogSpectrum_dense` (already proved on the quasicrystal island) this completes "ζ escapes
the tame / Lee–Yang crystalline class" on **both** sides, point set and spectrum.

## Why this needed an assembly rather than an import

Both registry dependencies were already proved, but on **different toolchains**:

| dependency | artifact | toolchain |
|---|---|---|
| `MM_nt_brick_conditional` | `zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density`, `quasicrystal/lean/BoundaryLemmas.lean` (branch `rh/million-turing` `@0bac3e608`, blob `b019e8e9167d51504a8775e9006ec8fceb9255bd`) | **v4.32.0** |
| `MM_rvm_unbounded_mean_density` | `RvMBridge.rvm_unbounded_mean_density`, `rvm_bridge/lean/E6Bridge.lean` (from `Zeta23.thmA₀` + the RvM main clause) | **v4.33.0-rc2** |

Two Lean toolchains cannot meet in one environment. The brick is elementary and zeta-free
(pigeonhole packing: bin `x ↦ ⌊(x−a)/δ⌋`, more points than bins), the RvM residual is the one
that consumes an external development — so the assembly happens on the **rvm island**, by
re-proving the brick there.

### HONESTY LINE (for the ledger and any downstream reader)

The registry dependency `MM_nt_brick_conditional` is satisfied by a **verbatim re-proof** of the
v4.32 artifact on the rvm island, **not** by consuming that artifact. The load-bearing analytic
input remains zeta-23-lean **Theorem A** (Alpöge–Furman), via `E6Bridge`; everything added in
`W2cAssembly.lean` is elementary. The re-proof ported six declarations line-for-line
(`IsUniformlyDiscrete`, `not_uniformlyDiscrete_of_gaps_to_zero`, `exists_close_of_card_gt`,
`RvMWindowedDensity`, `windowedDensity_of_unboundedMeanDensity`,
`not_uniformlyDiscrete_of_windowedDensity`,
`zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density`), with source line ranges cited above
each block; **zero Mathlib-name drift was needed** v4.32 → v4.33 (the flagged risk — floor lemma
spellings `Nat.floor_le`, `Nat.lt_floor_add_one`, `Nat.floor_le_floor`,
`Finset.exists_ne_map_eq_of_card_lt_of_maps_to` — did not materialize; the file compiled on the
first attempt).

## The certificate: a new Telperion gate, `telperion.port_match`

The brief said "cert shape: none needed; the generate.py drift check is the certificate". Writing
that check exposed a **missing tool kind**, and the tool was built rather than hand-rolled into
one island's script.

Telperion's existing trust boundary has three gates, and none covers this shape:

* `verify.verify_lean` — the proof compiles and is axiom-clean;
* `negative_control` — a FALSE instance is kernel-rejected;
* `statement_match` — a declaration states its INTENDED proposition, checked by **elaborating**
  `theorem __sigmatch_foo : T := @foo`. This is a defeq check, so both sides must live in **one
  Lean environment**.

A cross-toolchain verbatim port has no such environment, by construction. So
`telperion/src/telperion/port_match.py` (new) gates it at the level the two files do share —
text:

* `port_match_check(source, target, decls)` — for each ported declaration, extract and compare
  the statement. For a **theorem** only the head `theorem NAME <binders> : <type>` up to the
  first top-level `:=` is compared (the **proof may differ** — tactic spellings change across
  Mathlib versions, and forbidding that would forbid porting at all); for a **def** the whole
  block including the **body** is compared (for a definition the body is the content). Either
  side may be a list of files, since a ported block can be split across modules — here
  `RvMUnboundedMeanDensity` lives in `E6Bridge.lean`, the rest in `W2cAssembly.lean`. A decl
  ported as the wrong kind (def ↔ theorem) is reported as drift, not compared in the wrong mode.
* `port_match_pinned(pin, target, decls, live=…)` — the two-sided check for the normal case,
  where the source island is on **another branch** and is not in the checkout: the port is
  checked against a pinned copy of the source statements, and *when the source island is
  present*, the **pin itself** is diffed against the live file, so the pin cannot rot into a
  fiction of the artifact it quotes.

`examples/rvm_bridge/generate.py --check` item (7) now runs that gate over all 8 ported
declarations against `_BRICK_V432_TEXT` (the pinned v4.32 statements, branch + blob recorded in
the comment), plus the node-statement containment, the mirrored `IsUniformlyDiscrete` vs
`MMDefs.lean`, and a no-`sorry` check. The island `generate.py` is already registered in
`telperion.toml` (`[[check]] name = "rvm_bridge"`), so this runs in CI as part of
`rvm-bridge-compiles`.

**Scope of the gate, stated honestly**: it is a *text* gate. It certifies the ported statement is
character-for-character (modulo comments and whitespace) the source statement; it does not
certify that two different Mathlib versions give that text the same meaning. That is exactly the
guarantee needed here — the re-proof cannot silently drift from the artifact it re-proves — and
no more.

Tests: `telperion/tests/test_port_match.py`, 11 cases, all passing, no Lean env needed. They pin
that an exact port with a *different proof* passes; that a weakened theorem binder, a drifted def
body, a missing declaration on either side, and a def↔theorem kind change are all caught; that
comments/whitespace are not drift; that split source/target file lists work; and that a rotten
pin is caught on both halves.

Adversarial checks run against the live island (each restored afterwards):

| mutation | result |
|---|---|
| `⌊L/δ⌋₊ + 1` → `+ 2` in the ported `exists_close_of_card_gt` binder | caught (drift) |
| weakened `RvMWindowedDensity` def body | caught (drift) |
| ported theorem deleted from `W2cAssembly.lean` | caught (`not found in rvm_bridge island`) |
| pin corrupted with the v4.32 island checked out | caught **twice** (target-vs-pin *and* pin-vs-live) |
| unmutated, with and without the v4.32 island in the checkout | passes |

## Files

| file | change |
|---|---|
| `telperion/examples/rvm_bridge/lean/W2cAssembly.lean` | **new** — the ported brick + the node statement |
| `telperion/examples/rvm_bridge/lean/lakefile.toml` | `lean_lib W2cAssembly` + added to `defaultTargets` |
| `telperion/examples/rvm_bridge/lean/AxiomGuardRvMBridge.lean` | `import W2cAssembly` + 7 new `#print axioms` anchors, guard header updated |
| `telperion/examples/rvm_bridge/lean/README.md` | the "W2c assembly" section, file table row, 51-anchor guard block |
| `telperion/examples/rvm_bridge/generate.py` | drift check item (7), through the new gate |
| `telperion/src/telperion/port_match.py` | **new** — the cross-toolchain port-match gate |
| `telperion/tests/test_port_match.py` | **new** — 11 tests |
| `telperion/missions/mirrormere/nodes/MM_zeta_ordinates_not_uniformly_discrete.toml` | `[proof]` link (via mission CLI) |
| `telperion/missions/mirrormere/attempts.jsonl` | one `Stalled` attempt (via mission CLI) |

`telperion/missions/` was touched only through the mission CLI (`mission link`, `mission
attempt`). `mission verify` is OK on all four campaigns.

## Build and guard output

```sh
export PATH=$HOME/.elan/bin:$PATH
cd telperion/examples/rvm_bridge/lean
lake build W2cAssembly AxiomGuardRvMBridge
lake env lean AxiomGuardRvMBridge.lean
```

`lake build` → `Build completed successfully (8822 jobs)`. The eight `RvMBridge` anchors added by
this work, verbatim from `lake env lean AxiomGuardRvMBridge.lean` (the other 45 anchors are
unchanged and also clean; full block in the island README):

```
'RvMBridge.zeta_ordinates_not_uniformly_discrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RvMBridge.exists_close_of_card_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.not_uniformlyDiscrete_of_gaps_to_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.windowedDensity_of_unboundedMeanDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.not_uniformlyDiscrete_of_windowedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`lake env lean` line-wraps the two longest names; the axiom list is the same three in every
case.) No `sorryAx` anywhere, so the CI guard step passes.

## Registry state and what remains

* `MM_zeta_ordinates_not_uniformly_discrete` — **linked**, ledger verdict `Stalled`, status still
  `open`. The **grant is deliberately not taken here**: it is a cross-island grant and waits on CI
  `rvm-bridge-compiles` going green after merge, per the E6 precedent (`MM_rvm_unbounded_mean_
  density`, attempt of 2026-09-17). Nothing is pushed and no PR is opened.
* `MM_nt_brick_conditional` stays linked to its v4.32 artifact; this work does not close it, and
  the honesty line above records why its use here is a re-proof.
* No open Lean obligation remains in this work item: `W2cAssembly.lean` has no `sorry`, and
  nothing was added to a WIP file.

## Honest scope

`N(T)/T → ∞` (windows of unbounded mean density) forces two ordinates arbitrarily close; that is
classical, and the machine-checked route here runs through Theorem A (a positive proportion of
zeros simple and on the critical line), which is itself unconditional but says nothing about
whether *all* zeros are on the line. "The ordinates are not uniformly discrete" is a statement
about *crowding*, not about *location*; it rules out one tame model for the zeta comb and is not
a step toward RH. `conjecture1_proved = False`.
