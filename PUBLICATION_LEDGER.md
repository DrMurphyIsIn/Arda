# Publication Ledger

A running, deliberately conservative tally of results from this research program. The point of this
file is to keep us honest: "publication-worthy" here means *a result that could plausibly stand up in a
venue after a literature check and peer review* — not a result we are certain is novel. Novelty
assessments below are **provisional** and made without an exhaustive literature search; several
candidates are very likely already known. Nothing here is peer-reviewed. Update as status changes.

Status legend: **PROVED** (complete argument, machine-verified where noted) · **PARTIAL** (rigorous
sub-result of an open problem) · **OPEN** (conjecture, not proved) · **TOOL** (methodological).
Novelty legend: **likely-known** · **novelty-uncertain (needs lit check)** · **plausibly-novel**.

| # | Result | Status | Scope | Novelty (provisional) | Location |
|---|--------|--------|-------|-----------------------|----------|
| 1 | Permanental dominance `per(L) ≥ imm_λ(L)/χ_λ(1)` for **tree/forest Laplacians**, all λ | PROVED (verified n≤8) | trees/forests only — **not** general PSD | **likely-known** (immanants of trees: Merris–Watkins &c.; normalized-char argument is standard) | `telperion/docs/permanental_dominance_trees.md`, `telperion/src/telperion/perm_dominance.py` |
| 2 | Lieb permanental dominance for **general PSD Hermitian** matrices | **OPEN** | all PSD — famous open conjecture (1966) | n/a | — |
| 3 | Brualdi–Goldwasser `Φ ≤ 1` on the **near-star family** `N(c,k)`, equality iff `c+k=5`, via 23-adic integrality | PARTIAL (rigorous sub-result) | near-star family only; full BG open | **plausibly-novel** as an integrality-based proof of this sub-case — *needs lit check* | `proof/verification/near_star_arithmetic_proof.py` |
| 4 | Brualdi–Goldwasser conjecture (all trees) | **OPEN** | the central open problem | n/a | `proof/` |
| 5 | Gauge-tower / benchmark-factor / product-telescope decomposition localizing the BG crux to one benchmark constant + one integer identity | TOOL + PARTIAL | framing/machinery; BG itself unproved | **plausibly-novel** framing — *needs lit check* | `telperion/src/telperion/{gauge_lift,benchmark_factor,telescope_product}.py` |
| 6 | Telperion: sympy→Lean kernel-checked certificate pipeline (untrusted generator / trusted kernel) | TOOL | methodology | **novelty-uncertain** (proof-producing pipelines exist; specific design may be presentable) | `telperion/` |
| 7 | Spider↔star extremal sweep of immanant ratios of trees; curvature "turn-on" sharp at the bosonic (permanent) vertex | (exploratory, verified n≤8) | trees; interpretive | **likely-known** (immanantal graph theory) | session notes / memory |
| 8 | Capped-joint g-step reduction: achievability correction (unconstrained Case-2 false on `μ∈(1/2,1)`; non-leaf messages `μ≤1/2`) + kernel-checked any-arity reduction of the config g-step to the abstract cavity g-lemma `gV_le` | PARTIAL (kernel-checked sub-result of open BG; ℚ→ℝ cast seam pending) | single-hub wiring of the ≤-half; BG itself unproved | **novelty-uncertain** — *needs lit check* | `proof/formalization/R3Cert/CappedJointAchievable.lean`, `telperion/examples/g1_floors/lean/GLemma.lean` |
| 9 | Chvátal–Gomory integer-rounding certificate emitter (VIPR-style, `omega`-discharged) + the kernel-checked near-star integer-window theorem where every continuous certificate provably fails | TOOL + PARTIAL (window fragment only) | integer linear arithmetic emitter; BG window `s∈[4,6]` | **novelty-uncertain** (VIPR checking is known; a Lean-kernel CG pipeline may be presentable) — *needs lit check* | `telperion/src/telperion/emit_cg_round.py`, `telperion/examples/cg_round/NearStarWindow.lean` |

## Honest notes

- **Entry 1** is real and machine-checked but almost certainly not new; treat as an exposition/verification
  contribution at most, pending a literature check (Merris, Brualdi, Grone, Chan–Lam on immanants of trees).
- **Entry 3** is the strongest genuinely-partial contribution to a named open problem, but it is a *sub-case*
  of Brualdi–Goldwasser, not the conjecture.
- The only items that would be unambiguously significant — **Entry 2** (Lieb, general PSD) and **Entry 4**
  (full BG) — remain **OPEN**. Do not record them as proved unless a complete, independently-checked argument
  exists.
- Before any submission: (a) full literature search per entry, (b) independent proof-checking (Lean CI green
  for the formalized parts), (c) explicit scope statement so a special case is never presented as the general
  conjecture.
