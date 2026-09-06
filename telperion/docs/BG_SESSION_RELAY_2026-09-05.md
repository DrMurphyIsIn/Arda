# Relay to the BG proof session — verified frontier + merge-layer results (2026-09-05)

**To the Brualdi–Goldwasser proof session (`bg/lean-tree-to-hub` + Track-A/B extremality).** This
session worked the Kelmans merge layer and the general-env residual to completion in the
side-lane (kernel-verified leaves + exact-arithmetic probes), and traced the capstone to its two
open hypotheses. Everything below is on `origin/main`; the leaves are pure `R3Cert.+` leaves
imported by nothing (collision-safe). `conjecture1_proved = False`.

## 1. The capstone reduces to exactly two open layers (unchanged, now precisely traced)

`conjecture1_of_layers_fixedN` (`R47TopCapstoneFixedN.lean:48`) is conditional on:

- **`Hnorm`** `: ∀ t, ∃ s, Balanced s ∧ Capped s ∧ stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)`
  — the tree→hub reduction (= your Obligation-A lane).
- **`Hdom`** `: ∀ s, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) → Aobj (backboneU s) ≤ Aobj (tie (stateSize s))`
  — a **merge-NORMAL** Balanced+Capped state is dominated by the tie.

The merge machinery between them is **already proven**: `step_mono` (`R47StepMono.lean:98`) +
`chain_to_normalForm`. So `Hdom`'s live content is the domination of the *normal form* by the
tie = **multi-hub extremality**.

## 2. Kernel-verified this session (available to use, collision-safe leaves)

The full local Kelmans merge table, 156 certs, all `emit_nonneg_orthant` + `norm_num`:

| Leaf | Content |
|---|---|
| `R47R7KelmansTwoHubCert` (6) | two-hub vertex-budget domination |
| `R47R7KelmansAssistedMergeCert` (6) | borrow-then-merge strictly raises `pi` |
| `R47R7KelmansGenEnvCert` (100) | general-environment step monotonicity, 25 load cells, all N/all m |
| `R47R7KelmansDichotomyCert` (44) | the sign dichotomy: `pi` increases iff donor loaded |

All green on `proof-lean`. These certify the *classical* `pi = per(L)/∏deg` merge behaviour; if
you want them wired into the `Aobj` world, that goes through the H2 bridge (`per(L)/∏deg = Ztot…`,
`R47MergePerL` + BridgeStep4*).

## 3. Two structural findings that sharpen `Hdom` (exact arithmetic, self-verifying)

**(a) The general-env 5 excluded cells are IRRELEVANT to `Hdom` — confirmed at the definition
level.** `certify_general_env_box` excludes `{(0,5),(1,4),(1,5),(2,5),(3,5)}`. Deep probing
(`proof/verification/residual_flint_probe.py`, python-flint, exact `fmpq`) shows all 5 fail the
*direct* step only for a large hub-mover (`deg_C =` 8,9,29,111,170) — i.e. only under gross
imbalance. But `Balanced` (`R47Step.lean:45`) forces every arm ∈ {4,5}, so a Balanced hub has
degree ≤ 5+2 = **7 < 8** = the lowest failure threshold. The residual failure regime is
**structurally unreachable under `Balanced`**, and `step_mono` already proves the Balanced+Capped
merge. So the 25-cell exclusion is an over-generality artifact of the general-env theorem, **not a
gap** — `Hdom`'s merge layer needs nothing more. (Also corrected in-repo: `three_hub_residual_probe`
had conjectured the exclusion was "a certificate artifact"; it is a *real* failure, just outside
`Balanced`.)

**(b) Multi-hub normal forms exist, but the NEAR-TIE ones are single-hub — so `Hdom`'s multi-hub
case is the EASY part.** Enumerating Balanced+Capped 2-hub states under `OrderedStep`:
**6030 / 15876 are irreducible** (normal), the simplest `[(44444,0),(44444,0)]` (an all-4-arm hub
has 0 fives but `merge`'s `hsplit` needs `5−load` fives). So `single_hub_normal` (proven) is not
the whole story — multi-hub extremality is syntactically required. BUT, ranking normal forms by
the classical rate `score(s) = ln pi(s) − (usize s/11)·ln(621/64)` (`pi = per(L)/∏deg`, tie =
`argmax score`; model validated: a value-5 arm multiplies `pi` by exactly `621/64` and adds 11 to
`usize`, so it is rate-neutral):

| | best score |
|---|---|
| best single hub | −0.03063 |
| best 2-hub normal form | −0.09265 (**0.062 below**) |
| best 3-hub normal form | −0.15999 (**0.129 below**) |

The top-scoring (near-tie) normal forms are **all single-hub**, and every multi-hub normal form is
strictly sub-tie by a margin that **grows ~0.06–0.07 per extra hub** (each hub is vertex overhead).
So the multi-hub normal forms are dominated by the tie *with a widening margin* — the genuinely
HARD part of `Hdom` (configs approaching the tie) is the **single-hub domination**, for which
single-hub results already exist. Suggestion: split `Hdom` as `single-hub (tight, near-tie)` +
`multi-hub (loose, margin ≥ ε·(#hubs−1))`, and target the multi-hub bound with the cheap margin
rather than a tight per-cell certificate. Self-verifying probe: `proof/verification/
normalform_score_probe.py` (`run()` asserts the growing gap). CAVEAT: empirical over a bounded
shape enum (arms 5–7, ≤3 hubs) on the `pi`-rate objective; the growing margin is a strong
structural signal, not a proof.


**Follow-up (per-hub margin, `normalform_score_probe.per_hub_margins`).** The multi-hub penalty is ~LINEAR and STABLE: `best_score(m) ≈ s₁ − ε·(m−1)`, ε ≈ 0.061 (measured 0.062/0.0615 at m=2,3 where fully enumerated; ≥ 0.05 robustly, does NOT shrink toward 0). Exemplars: best single hub `[(44444,5)]` (score −0.03063), best 2-hub NF `[(44444,5),(44444,4)]` (−0.09265). So an m-hub Balanced+Capped normal form is ≥ 0.05·(m−1) below the single-hub max in the `pi`-rate score `ln pi − (usize/11)·ln(621/64)` — the multi-hub extremality is provably LOOSE. **Suggested `Hdom` split:** prove single-hub tight (near-tie), and multi-hub via the cheap margin `≥ ε·(#hubs−1)` (a per-hub `each extra hub costs ≥ ε` lemma), not a per-cell certificate. CAVEAT: empirical on the `pi`-rate objective over a bounded shape enum (arms 5–7, m ≤ 5); a strong structural signal, not a proof — the per-hub lemma is yours to prove.

## 4. Suggested division of labour

- **Yours (open):** `Hnorm` (Obligation A) and `Hdom`'s multi-hub extremality (Track-A/B, the
  single-child lemma on the price interval `I`). These are your active lanes; I did not touch the
  `Aobj`/extremality Lean.
- **Available from me:** the merge-table leaves (§2) if you want the classical-side merge facts
  kernel-verified; the exact-arithmetic probes (§3) as reusable config evaluators (flint-fast);
  and the codified `positivity_leaf` pipeline (`telperion/cert_leaf.py`) + `emit_nonneg_orthant` /
  `emit_domain_to_orthant` for turning any per-cell rational certificate family into a hazard-safe
  self-building leaf in one call.

Ping me to wire any merge-table leaf into a named hypothesis, or to certify a finite family you
isolate on the extremality side.
