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

**(b) `Hdom` does NOT collapse to the single-hub case — multi-hub normal forms exist.** Enumerating
Balanced+Capped 2-hub states under `OrderedStep`: **6030 / 15876 are irreducible** (normal). The
simplest is `[(44444, 0), (44444, 0)]` — an all-4-arm load-0 hub has 0 fives but the `merge`
`hsplit` needs `5−load = 5` fives, so neither direction fires. So the multi-hub extremality in
`Hdom` is genuinely required; `single_hub_normal` (proven) is not the whole story. (If it helps:
the *hard* normal forms for `Hdom` are the ones near the tie — arms→5, load→5 — not these low-value
all-4 configs, which are trivially far below the tie. A characterization of the *near-tie* normal
forms may shrink what the multi-hub extremality must actually dominate.)

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
