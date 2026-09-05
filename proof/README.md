# The proof package

Peer-review materials for the campaign on the Brualdi–Goldwasser (1984)
Laplacian-ratio maximizer. This document maps what is machine-checked, what is
certified at exact-arithmetic rigor in Python, and what is named-open.
`conjecture1_proved = False` throughout — the status ledger is executable
(`verification/conjecture1_status.py` calls the certificates it cites).

## Layout

| Path | Contents |
|---|---|
| `formalization/` | The Lean 4 project (toolchain `lean-toolchain`, Mathlib pinned in `lake-manifest.json`). Library root `R3Cert.lean` transitively imports all 191 modules under `R3Cert/` — a green `lake build` compiles everything; there are no orphaned files. |
| `verification/` | ~130 Python modules: the load-bearing certificate/verification modules (all invoked by `../verify.py`), the certificate generator (`gen_r47cert_cells.py`, frozen for provenance), exploratory probes and honest no-go records of failed proof routes, and unit tests (`tests/`). |
| `verify.py` | One-command verification: runs every load-bearing module's `run_all()`. Every claim is an assert; ~20–40 min. |
| `docs/` | The working documents — start at the reading guide [`docs/README.md`](docs/README.md): the campaign map (`PROOF_STATE_AND_PLAN.md`), the result document (`RESULT_LAPLACIAN_RATIO.md`), the dated frontier analyses (`GSTEP_*`), candidate verdicts, `design/` (formalization design + independent reviews), `notes/` (two technical companion notes). |
| `figures/` | TikZ sources, rendered figures, and generation scripts. |

## What is machine-checked (Lean 4, no `sorry`, no added axioms)

The chain, bottom to top:

1. **Exact cruxes** (`ExactCruxes.lean`, `Sweep.lean`): the integer/rational
   anchor facts, kernel-checked — including `3^317 · 2^81 ≤ 23^129` and the tie
   identity `64 · 243 · 23 = 621 · 576`.
2. **The permanent–matching bridge** (`Matching.lean`, `Involution.lean`,
   `CavityTree.lean`, `BridgeStep2`–`BridgeStep4j`): `per` of an acyclic
   support = matching sum (H1); the cavity recursion; acyclicity of the address
   graph; the unconditional capstones `pi_litHub'` and `amplitude_bridge_real'`
   tying the Branch cavity model to the finite `per L/∏deg` objects.
3. **`Φ ≤ 1`** (`Potential*.lean`, capstone `PotentialFinal.lean:phi_le_one`):
   the central inequality, unconditional over every branch, with equality
   exactly on the six-point tie variety. No smooth certificate can prove this
   (the continuous relaxation exceeds 1); the proof is arithmetic.
4. **The reduction layer (R47 campaign)**: the objective `pi_utree` (= `per
   L/∏deg` for every tree); the hub-state encoding and backbone recursion; the
   unified topped-up merge `Step` relation (termination, fixed-`n`,
   normal-form existence); the **36-cell bilinear certificate table** + 36
   dispatch adapters + 72 vee/mirror branches (all generated, all
   `positivity`-closed); **`step_mono` / `chain_to_normalForm`** — the
   merge-layer capstone; the (L) legs layer (42 certificates + a 726-digit
   bignum crux); the R6 shedding lemmas (55 certificates); the rate-port parse
   (`R47Perm.lean`, `R47Parse.lean`).
5. **The capped-joint g-step layer** (2026-08-20; `GStepCore.lean`,
   `GLemmaConfig.lean` / `GLemmaAssembly.lean`, `CappedJointConfig.lean`,
   `CappedJointAchievable.lean`): the achievability-corrected Case-2 hypothesis
   (the unconstrained form is *false* on `μ ∈ (1/2,1)`; non-leaf cavity
   messages satisfy `μ ≤ 1/2` — the relocated integrality content), the
   kernel-checked single-child (`0<μ≤1/2`) and two-child (unconditional)
   g-step bounds, and the bridge toward the abstract g-lemma `gV_le`
   (kernel-proven in `../telperion/examples/g1_floors/lean/`). Landed via
   PR #20 (merged 2026-08-21): the `gV_le` port (`GArmExtAbstract.lean`,
   `GLemmaAbstract.lean`) plus the full closure
   `CappedJointClosure.lean:gstep_le_one_achievable` — the config g-step
   `≤ 1` at every arity, unconditionally over achievable messages.

Generated files carry provenance headers naming the generator and its
self-checks; regenerate and diff via
`python3 verification/gen_r47cert_cells.py` (see file headers).

## What is certified at exact-arithmetic rigor (Python, not yet Lean)

Run `python3 verify.py` — 15 modules, every claim an assert, exact
`fractions.Fraction` / sympy arithmetic (no floats in certificate paths):
the Kelmans exchange dichotomy and unified merge table, the rate identity
`pi = Z·R`, the slack-ledger dichotomy and amortized hub bound, the G3/G4
domination sweeps (including a 442,800-case exact sweep), the interpolation
lemma, and the G1 floor/endpoint certificates.

## What is named-open

- **The g-step composition**: `gstep_le_one_achievable` landed (PR #20); what
  remains is composing the config-model closure into the rooted-tree master
  induction (the remaining *tight* content is identified with the master
  inequality in `docs/GSTEP_STEP1_IS_THE_CRUX.md`).
- **`R47Rate`** — rate corner **landed** (PR #33, 2026-08-21:
  `R47Rate.lean:pi_rate_leafRooted`, the bound
  `per(L)/∏deg ≤ (4/3)·rhoB^n` on the real permanent ratio for the
  leaf-rooted normal form, kernel-clean). Remaining by design: the
  arbitrary-rooting generalization = graph iso-invariance of `per(L)/∏deg`,
  deferred to assembly (the reduction picks a leaf-rooted normal form).
- **The `R7'` assembly**: the honest-conditional capstone composing all layers
  (`docs/design/R7_ASSEMBLY_DESIGN.md`) — hypotheses are named `Prop`s with
  certificate provenance, never axioms.
- The gap ledger with per-gap status: `docs/design/R7_ARCHITECTURE.md`
  (including the independent review's amendments, kept verbatim).

## Honesty spine

- Two independent exact permanent engines (Ryser vs tree matching DP) must
  agree (`verification/tests/test_lr.py`); the anchor
  `pi(T(3,3,3)) = 19683/256` pins the pipeline.
- Failed proof routes are preserved as `*_nogo*.py` / `*_probe*.py` modules —
  the negative results are part of the record (six-plus smooth-certificate
  routes are refuted by the tie asymptotics).
- The independent-review documents in `docs/design/REVIEW_*.md` are included
  unedited, including the findings that corrected earlier overclaims.
