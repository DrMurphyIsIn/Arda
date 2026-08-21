# proof/docs — reading guide

This directory accumulates the campaign's working documents. They fall into
four kinds; this index says which is which and where to start.

## Start here (the load-bearing maps)

| Document | Role |
|---|---|
| [`PROOF_STATE_AND_PLAN.md`](PROOF_STATE_AND_PLAN.md) | The whole-campaign map: the R1–R7 reduction ladder, the four remaining gaps, and a completion plan per gap. Kept synthesized against the executable status ledger (`../verification/conjecture1_status.py`). |
| [`RESULT_LAPLACIAN_RATIO.md`](RESULT_LAPLACIAN_RATIO.md) | The result document — the mathematical content in paper-like form. |
| [`design/R7_ARCHITECTURE.md`](design/R7_ARCHITECTURE.md) | The named-gap ledger for the final assembly, including the independent review's amendments kept verbatim. |

## The current frontier (dated, newest first)

The `GSTEP_*` trio (2026-08-21) is the live analysis of the g-step / master
inequality frontier, written as the work happened:

- [`GSTEP_STEP1_IS_THE_CRUX.md`](GSTEP_STEP1_IS_THE_CRUX.md) — the
  unification: every open thread (R3 branching tail, homogeneous face,
  g-step tight content) is one object, the master inequality.
- [`GSTEP_2TYPE_STEP2_CLOSED.md`](GSTEP_2TYPE_STEP2_CLOSED.md) — the 2-type
  decomposition; STEP 2 machine-closed, STEP 1 identified as the
  non-monotone wall.
- [`GSTEP_HANDELMAN_RECIPE.md`](GSTEP_HANDELMAN_RECIPE.md) — the
  Handelman-certificate recipe for the closable cases (q=2, q=3
  machine-closed).

## Candidate verdicts (honest failure records)

The `CANDIDATE_*` documents record proposed proof steps **and what became of
them** — including the ones that were false as first stated. They are kept
because the corrections carry information (the capped-joint Case-2
correction, for instance, is where the achievability constraint `μ ≤ 1/2`
was discovered to be the relocated integrality content):

- [`CANDIDATE_CAPPED_JOINT_INDUCTION.md`](CANDIDATE_CAPPED_JOINT_INDUCTION.md)
- [`CANDIDATE_CAPPED_JOINT_master_step_proof.md`](CANDIDATE_CAPPED_JOINT_master_step_proof.md)
- [`CANDIDATE_CAPPED_JOINT_glemma_step_verdict.md`](CANDIDATE_CAPPED_JOINT_glemma_step_verdict.md)

## Everything else

- [`design/`](design/) — the formalization campaign's design documents and
  the independent-review records (`REVIEW_*.md`, included unedited), one per
  major arc (bridge, merge layer, (L)/(B) layer, G1, R47, R7 assembly,
  master inequality).
- [`notes/`](notes/) — two technical companion notes with TeX + PDF: the
  permanent/matching bridge (`matching_bridge`) and the merge-system
  confluence (`kelmans_confluence`).
- `SESSION_REPORT_*.md` — dated session snapshots, kept for provenance.

Convention: dated documents (`GSTEP_*`, `SESSION_REPORT_*`, `REVIEW_*`) are
frozen once written — corrections happen in newer documents that cite them,
never by silent edit. The maps at the top are the only living documents here.
