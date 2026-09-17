---
name: wall-sweep
description: Use when mapping why a hard conjecture resists a class of approaches — an adversarial multi-agent sweep that classifies candidate footholds (partial unconditional results) into a strict verdict taxonomy with refutation lenses, primary-source verification, and an honesty ledger. Use for "is there any partial result on axis X", "map the wall", "does any tool reach Y short of the full conjecture" questions. NOT for proving things — it maps obstructions; the kernel proves.
---

# Wall-sweep: adversarial mapping of a conjecture's resistance

## What it is

A three-phase multi-agent workflow (probe → refute → synthesize) that answers, honestly,
"does any unconditional partial foothold exist on axis X, and exactly where does it
stop?" Developed on the RH wall campaign: five sweeps (weight / ordinate / horizontal /
joint ×2 / GL(n)), one independent replication with convergent verdicts, one audit.

## The verdict taxonomy (use verbatim)

- **FOOTHOLD** — a genuine unconditional partial result that does real work; MUST
  self-declare its named wall (where and why it stops short of the conjecture).
- **COLLAPSE_TO_<GOAL>** — the mechanism's decisive sensitivity secretly requires
  goal-strength input (cite the equivalence).
- **COLLAPSE_TO_FREE** — does no work; factors through already-swept material.
- **TRANSFER** — moves the wall intact to another object (state what transfer buys).
- **UNRESOLVED** — anything not settled. A rate-limited, failed, or absent check is
  UNRESOLVED, **never** a refutation (the deep-research false-negative lesson).

## Phase structure (canonical Workflow script shape)

1. **Probe**: one finder per thread (5–7 threads), literature-grounded (WebSearch +
   primary-source fetch; `checked: true` only after actually confirming), corpus-aware
   (name the repo artifacts in the prompt), structured-output schema with
   `{verdict, claim, mechanism, limitation, sources[], kernel_probe, confidence}`.
   Run ONE adjudicator in parallel for any load-bearing lemma the campaign already
   committed — sweeps that can refute their own prior prose are the ones worth trusting.
2. **Refute**: for each claimed FOOTHOLD, three lenses in parallel —
   `collapse_to_goal` (find the smuggled goal-strength step), `single_axis` (show the
   novelty is decorative), `literature` (verify the load-bearing citation says what is
   claimed). Kill only on ≥2 refuted votes among ≥2 succeeded agents; fewer than 2
   succeeded ⇒ UNVERIFIED, not killed.
3. **Synthesize**: verdict table; survivors with their named walls stated as BINDING
   boundaries (the refuters' demotion arguments recorded, not dropped); the meta-verdict;
   recommended kernel probes in priority order; honesty footer listing every UNRESOLVED
   primary source explicitly.

## The honesty invariants (non-negotiable)

- The campaign's falsity flag (e.g. `conjecture1_proved = False`) appears in the prompt
  preamble, the synthesis, and every committed artifact.
- Survivors are INSTRUMENT claims, never progress-toward-proof claims.
- Secondary-source-only citations go on the UNRESOLVED list even when load-bearing —
  named, so the next session primary-verifies before any kernel probe cites them.
- **Replicate-then-reconcile**: a second independent run of the same sweep, followed by
  a reconciliation doc (convergences = evidence; divergences = errata with scope), caught
  a prose overgeneralization three independent instruments agreed on. Budget for it on
  any sweep whose conclusion will be committed as campaign doctrine.
- Fold conclusions as a NEW doc; correct prior docs by scoped errata, never silently.

## Reference run

Canonical script: the session workflow `rh-sweep4-joint-coupling` (probe/refute/
synthesize with the schemas above); reference conclusions:
`telperion/docs/RH_WALL_SWEEP4_REPLICATION_2026-09-16.md` (replication + reconciliation),
`RH_WALL_FIVE_SWEEP_CAPSTONE_2026-09-16.md` (audited capstone). The kernel-probe output
pattern: each sweep ends with buildable Lean probe recommendations — the sweep maps, the
kernel certifies.
