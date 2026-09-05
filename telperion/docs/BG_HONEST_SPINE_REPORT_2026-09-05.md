# BG honest-spine report — what is actually proved (2026-09-05)

Kernel-verified audit of the `conjecture1` assembly in `proof/formalization/R3Cert`,
run via `telperion/scratch/bg_honest_audit.py` (kernel `#print axioms` against the
BUILT env + comment-stripped textual scan). Purpose: an honest "what's really proved
vs conditional" map for the BG lane. `conjecture1_proved = False` — BG is NOT proved;
this audits the FORMALIZATION's honesty, and the result is clean.

## Headline (authoritative, kernel truth)

- **Both capstones are kernel-CLEAN** — `#print axioms` = `{Classical.choice,
  Quot.sound, propext}`, **no `sorryAx`**:
  - `R3Cert.Step3.conjecture1_of_layers` (fixed tie — unbounded, unusable)
  - `R3Cert.Step3.conjecture1_of_layers_fixedN` (the WELL-POSED, size-correct capstone)
  Because `sorryAx` propagates through `#print axioms`, a clean capstone
  **transitively certifies its ENTIRE proof-dependency closure is sorry-free**.
- **Zero real proof-body `sorry`** in the whole corpus (3837 theorems / 198 files),
  comment-stripped. The "127 files with sorry" from a raw grep were ALL comment
  mentions (e.g. docstrings saying "no `sorry`"). The prototype's "on-spine sorry"
  `Matched_factor` was one such false positive — it is kernel-clean.

So the formalization is honest: the assembly is a genuine, sorry-free CONDITIONAL.

## The entire remaining frontier: two undischarged hypotheses

`conjecture1_of_layers_fixedN` proves `∀ t, Aobj t ≤ Aobj (tie (usize t))` FROM:

- **Hnorm** (size-preserving normalization): `∀ t, ∃ s, Balanced s ∧ Capped s ∧
  stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)`
- **Hdom** (normal-form domination): `∀ s, Balanced s → Capped s →
  (∀ u, ¬ OrderedStep s u) → Aobj (backboneU s) ≤ Aobj (tie (stateSize s))`

The capstone is **never instantiated** with discharged Hnorm/Hdom (only referenced in
comments) ⇒ discharging these two IS the whole remaining BG proof.

### Discharge status (from the corpus)
- **Hnorm** — heavily worked (~40 files touch normalization/backbone). Single-hub done
  (`R47R6HnormSingleHub`); size-preserving layer in progress (`R47R6HnormSized`,
  `R47R7Sized`, `R47R7TreeToHub`). A trivial `tree_to_hub : ∀ t, ∃ s, Aobj t ≤ Aobj
  (backboneU s)` exists but is UNUSABLE (no Balanced/Capped/size conditions). The full
  multi-hub size-preserving Hnorm is the open core.
- **Hdom** — being assembled from Kelmans two-hub vertex-budget positivity certs
  (`R47R7KelmansTwoHubCert`: `two_hub_gap_pos_c0..c5`, all kernel-clean nonneg
  polynomials). These are NODES; the full Hdom over all normal-form states is not yet
  assembled.

## Statement-identity caveat (the mislabeling risk)

`Aobj t := Ztot (dtRealize t)` (`R47Tree.lean`). Before any "BG resolved" claim, the
capstone's `Aobj` must be pinned as the **classical** BG objective `per(L)/∏deg`, not
the rooted-branch `Φ¹¹` variant (`81/8 ≠ 621/64` at the tie — a documented past
mislabeling). This is a **signature-gate** job (assert `conjecture1_of_layers_fixedN`
states the classical claim); it is NOT covered by the sorry-free check.

## How the Telperion tooling accelerates the frontier

1. **LSP warm-env verify tier** (`telperion.lean_server`, ~0.2s vs ~4-8s cold) — the
   Hnorm/Hdom discharge is a large per-lemma iteration; the warm loop is the biggest
   throughput win. The BG `proof/formalization` env is built, so it works today.
2. **`negative_control`** — kernel-gate candidate Hdom/OrderedStep moves (and Hnorm
   normalization steps) BEFORE investing in a proof: a false candidate's emitted proof
   must fail to compile. Directly applicable to the Kelmans-node and normalization-move
   search.
3. **Signature gate** — pin the classical-BG statement identity of the capstone
   (the mislabeling guard above), and assert each discharged Hnorm/Hdom lemma states
   the EXACT shape the capstone consumes.
4. **This audit as a CI guard** — a job that re-runs `#print axioms` on the two
   capstones keeps "assembly stays a clean conditional" a permanent, machine-enforced
   invariant (catches a regression that reintroduces a `sorryAx` on the spine).

Reproduce: `PATH=$HOME/.elan/bin:$PATH PYTHONPATH=src python3 scratch/bg_honest_audit.py`.
Coordinate with the active BG session before touching shared `R3Cert` files.
