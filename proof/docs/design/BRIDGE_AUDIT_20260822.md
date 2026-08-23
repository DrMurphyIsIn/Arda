# Bridge / Gap-2 state (2026-08-22) — corrected audit

`conjecture1_proved = False`. **Correction notice:** an earlier draft of this doc (same day) claimed
"no `per(L(T))` is defined or connected; the capstone is not in Lean." **That was wrong** — an
artifact of a `git grep` pathspec (`R3Cert/**/*.lean` silently skips files directly in `R3Cert/`,
which is where the core files live). Re-audited with `proof/formalization/**/*.lean`. Lesson recorded:
use that glob, and defer "what is open" to `proof/verification/conjecture1_status.py` (the R-ladder
aggregator), not ad-hoc greps.

## Verified facts (read directly on `main`, all `no sorry`)

Whole-formalization scan (correct glob): **0** occurrences of `sorry`/`admit`/`axiom`/`native_decide`
and **0** `Prop := True`/`:= trivial` stubs.

The permanent↔matching↔Branch bridge is substantially formalized:

| Piece | Lean (`R3Cert/`) | Content |
|---|---|---|
| **H1** | `Matching.permanent_eq_matching_sum` | `per(lapl G) = Σ_matchings Π_{unmatched} deg` for acyclic `G` — genuine; `acyclicForcesInvolution` really discharged by `Involution.lean` (not a stub) |
| **H2a** | `Matching.pi_eq_weighted_matching_sum` | `per/∏deg = Σ_M Π_{ij∈M} 1/(deg i·deg j)` |
| **H2 cavity** | `Matching.cavity_recursion` | node step `Zopen/Ztot = 1/(1+Σ w r)` |
| **π↔msum** | `BridgeStep3d.pi_eq_msum` | matching partition function ↔ `msum` |
| **realize↔per** | `BridgeStep4j.pi_litHub'` | **unconditional**: `per(lapl(realize(litHub c ch)))/∏deg = Ztot(litHub c ch)` |
| **amplitude bridge** | `BridgeStep4j.amplitude_bridge_real'` | **unconditional**: the real-Laplacian permanent-ratio (`p`-arm hub with `b` vs without) `→ exp(logPhi b)·rhoB^{Vb b}` as `p→∞` |
| Steps 1–4 | `Bridge`/`BridgeStep2`/`BridgeStep3`/`BridgeStep4` | cavity structure, `realize`, `q_realize_eq_rho0`, matching-sum multiplicativity, `hub_rho0_limit` |

So the three type-universes (SimpleGraph permanent / RTree `Ztot` / Branch `logPhi`) **are** connected by
unconditional theorems — `pi_litHub'` and `amplitude_bridge_real'` are exactly the "realization
bridges" the earlier draft wrongly called missing.

## What is actually open (per the authoritative aggregator)

`conjecture1_status.py` keeps `conjecture1_proved = False`. Its prose is not fully in sync with `main`
(it predates some `BridgeStep4i/4j` capstones and the folded-potential `phi_le_one`), so the precise
residual needs a **fresh lemma-level review** rather than a claim from this doc. As of the aggregator's
last text, the named residuals are:

- **R7 global assembly** (the `R47*` campaign — `R47Rate`/`R47Tree`/`R47Head`/`R47Parse`): the
  structural reduction that every tree is dominated by a cherry-bundle star (R1–R6 combine). This is
  the largest clearly-open item.
- **Bridge end-to-end composition / uniform rate**: the aggregator's text still lists the uniform
  per-node / `O(1/p²)` end-to-end as open, but `amplitude_bridge_real'` (a `Tendsto`, unconditional)
  may already discharge the limit transfer — this is exactly what the fresh review must reconcile.

## Honest status

The g-step / R3 crux is closed (`gstep_le_one_achievable` + `phi_le_one`); the bridge is far more
complete than a naive grep shows (table above). The remaining distance to Conjecture 1 is **R7
assembly** and confirming the bridge composes end-to-end — a reconciling review of `main` against
`conjecture1_status.py`, not a fresh open-math claim from greps. `conjecture1_proved = False`.

## ADDENDUM 2026-08-22 — the reconciling review this doc asked for (done)

The lemma-level review of Gap 2 requested above was carried out and `conjecture1_status.py`'s
`R3_bridge_lean` entry has been corrected. Findings (all read directly on `main`, no-`sorry` verified):

- **The aggregator's "uniform O(1/p²) error constant ... the last + hardest bridge gap" was STALE and
  is now struck.** `BridgeStep4b/4d/4j` state explicitly that *no* O(1/p²) (or O(1/p)) envelope is
  needed — the bridge statement is a **limit**, so `Tendsto` algebra on exact rational closed forms
  suffices. The entry predated `BridgeStep4i/4j` and `R47Tree`.
- **The STEP-4 capstones are unconditional.** `BridgeStep4j.aGraph_realize_isAcyclic` discharges the
  last acyclicity hypothesis of the 4i theorems, making `pi_litHub'` (per L / ∏deg = Ztot) and
  `amplitude_bridge_real'` (real-Laplacian hub amplitude ratio → `exp(logPhi b)·rhoB^{Vb b}`, a
  completed `Tendsto`) hypothesis-free.
- **The permanent↔Ztot identity is proven for ALL rooted trees**, not just `litHub`:
  `R47Tree.pi_utree : per(L(realize(dtRealize t)))/∏deg = Aobj t` for every `UTree t`.
- **Re-pointed residual.** The bridge no longer gates the proof. What remains to a *formal* Conjecture 1
  is (a) **R7/G7 assembly** composing `Aobj`-maximization down to the hub-amplitude form where
  `amplitude_bridge_logPhi + phi_le_one` bite, and (b) **root-invariance** (`R47Tree`'s `Aobj` is on
  *rooted* trees; the unrooted objective is deferred to P2). Both are the `R7_global_reduction` / G7
  item — **not** a bridge-limit gap. Gap 1 (the R3 master inequality) is untouched: the bridge assumes
  `phi_le_one`.
- **One cheap missing brick:** the `le_of_tendsto` corollary `exp(logPhi b)·rhoB^{Vb b} ≤ rhoB^{Vb b}`
  (from `amplitude_bridge_logPhi` + `phi_le_one`) is not yet stated — it would make the bridge's payoff
  explicit and CI-checked. `conjecture1_proved = False`.
