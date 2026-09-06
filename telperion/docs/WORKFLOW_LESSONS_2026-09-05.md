# Telperion workflow lessons (2026-09-05) — codified for reuse

Process techniques that saved (or would have saved) large effort this session. Read before a
Lean-proof or proof-frontier task. `conjecture1_proved = False`.

## 1. Before building a Lean theorem, grep the installed Mathlib for it

Borel–Carathéodory was flagged in the plan as "the single missing Mathlib theorem" (~500 lines).
It is NOT missing — Mathlib v4.32 ships `Complex.borelCaratheodory` (+ `_zero`, author
M. Radziwill). Found by grepping the cached Mathlib *before* writing the proof. RH-adjacent
analysis is being upstreamed fast; check first.

```bash
MB=<example>/.lake/packages/mathlib/Mathlib
grep -rn 'theorem <name>\|<Concept>' $MB/Analysis/... 2>/dev/null
```

When it IS upstream, the emitter becomes a **wrapper** (see `emit_reexport`, §5), not a rebuild.

## 2. Before adding analysis to a proof AREA, check origin/main for the parallel lane's files

The BG (`Hnorm`/`Hdom` extremality) and RH (zero-free region) frontiers are BOTH actively worked
by parallel sessions. I built a BC *derivative* form; a rebase conflict revealed the `rh-dlvp`
lane had already shipped a cleaner `DlvpBCDeriv.norm_deriv_le_of_re_le`. Dropped mine.

```bash
git fetch origin main -q
git show origin/main:<dir> | grep <topic>      # or: ls the Dlvp*/bg-* files first
```

Collision-safe pattern that DID work all session: pure `R3Cert.+` / self-building **leaf** files
imported by nothing — CI/kernel verify them but they are not dependencies of anyone's capstone.

## 3. Local Lean builds work again (~5 s, cached) — build + axiom-check recipe

The Aug-9 "CI-only / SoC-hazard" rule is lifted (machine serviced). Iterate locally:

```bash
cd telperion/examples/<ex>/lean && export PATH=$HOME/.elan/bin:$PATH
lake exe cache get          # first time only (fetches mathlib oleans; a fresh clone takes minutes)
lake build <LibName>        # ~5–30 s incremental
```

Axiom-check a theorem (a green build ≠ axiom-clean): a throwaway lib with `#print axioms`:

```lean
import <LibName>
#print axioms <Namespace>.<thm>   -- want [propext, Classical.choice, Quot.sound], NO sorryAx
```

Add a new single-file lib as `[[lean_lib]]\nname = "<File>"` in the example `lakefile.toml`; give
it a CI job (`lake build <File>`) in `telperion-lean-e2e.yml` if it should be continuously gated
(out-of-`defaultTargets` libs each get their own `lake build <Lib>` step).

## 4. A bounded empirical scan is NOT a proof — push the parameter far before claiming

I claimed 2 of 5 residual Kelmans cells "certifiable (0 decreases)" from a scan bounded to
`deg_C ≤ 61`. With `python-flint` pushing `deg_C` to the hundreds, ALL 5 fail (thresholds up to
170). The margin GROWS structurally, but the "no decrease in range" was an artifact. Before
asserting monotonicity/certifiability from a scan: identify the parameter that could break it and
push it to the exact-arithmetic limit (flint `fmpq` is ~20× `fractions.Fraction`; validate any
fast re-implementation against the reference — e.g. `pi_flint == pi_loaded`).

## 5. Two codified capabilities from this session

- **`emit_reexport.reexport_cert`** — the wrapper-emitter shape: package an already-proven /
  upstream theorem (`residue_logDeriv`, `Complex.borelCaratheodory`) as a named re-export
  `theorem <name> <binders> <hyps> : <conclusion> := <lemma> <args>`. `emit_order_residue` and
  `emit_borel_caratheodory` are instances (tests reproduce both). Use for ANY "package theorem L".
- **`cert_leaf.positivity_leaf`** (earlier) — a family of per-cell certs → one hazard-safe
  self-building Lean leaf, with `scan_hazards` catching the `-/`-in-prose and `**` bugs.

## 6. Self-verifying probe methodology (empirical structural characterization)

When a proof piece is research-hard or another lane's, an exact-arithmetic **self-verifying
probe** is a legitimate, non-colliding contribution: characterize the structure, `assert` the
finding in `run()`, relay it. Examples this session: `residual_hub_mover_probe` (refuted a
codebase conjecture + found the anti-hubward rescue), `normalform_score_probe` (near-tie normal
forms are single-hub → `Hdom`'s multi-hub case is the easy part), `residual_flint_probe`
(flint-scaled). These sharpened / corrected the frontier without touching the owning lane's Lean.
