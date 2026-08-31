# Standing order: cross-pollinate BG ↔ RH shapes into Telperion

**Order.** Whenever one proof effort — Brualdi–Goldwasser (BG / Laplacian) or the
Riemann Hypothesis (RH) campaign — produces a *skill or shape* in Telperion (a
new emitter kind, an `InequalityFamily` pattern, a certification discipline) that
would apply to advancing the *other* effort's goals, it MUST be done and
formalized into Telperion as a reusable capability. Cross-pollination is not
optional and not deferred to "when convenient" — a shape that helps the sister
effort is built, certified, and left in the shared emitter set.

This generalizes the existing Telperion build standing order (build any reusable
capability that surfaces in a proof into Telperion as a skill) with an explicit
*bidirectional* obligation: RH→BG and BG→RH are first-class flows.

## Why this is sound (the commensalism)

Both efforts sit on one substrate: the untrusted-generator / trusted-Lean-kernel
split, exact-`Fraction` certify-before-emit, and a shared Mathlib pin under one
CI kernel gate. Their mathematics overlaps at real-rootedness / hyperbolicity
(Turán / Jensen / Hankel PSD), rational-function identities, p-adic/integrality
tie facts, SOS/Pólya positivity, and rigorous rational brackets. A capability
built for one is almost always shaped for the other at zero marginal cost to the
producer — true commensalism, and where the flow is folded back into Telperion,
mutualism.

## Precedents (already fired)

- **RH → BG:** `IntervalBracketEmitter` (`SqrtBracketCertificate`) regenerated the
  BG `e2_two_rhoB` `√2` crux, KERNEL-gated (PR #146).
- **RH → BG:** `IdentityEmitter` (kind=`equation`) discharges BG **RUNG-2**
  (`stardom_rung2_family.py`); 972/972 cells validate offline.
- **BG → RH/Telperion:** the StarDom `DirectPolyaEmitter` family + the dual-engine
  faithfulness discipline (`target` vs `independent_target`) and the `special=`
  first-class-emitter hook are BG-derived shapes now in the shared emitter set.

## The obligation, concretely

1. When a proof introduces a recurring hand-written pattern (an identity family, a
   positivity/PSD certificate, a bracket, a valuation fact, a monotone/telescope
   bound), check whether the sister effort has an obligation of the same *shape*
   (see the RH-emitter → BG-obligation map kept alongside the BG proof:
   `experiments/graph_hunter/laplacian_ratio/RH_EMITTER_TO_BG_OBLIGATION_MAP.md`).
2. If so, promote the pattern to a first-class emitter kind (or reuse an existing
   one) and wire the sister obligation as an `InequalityFamily`.
3. Certify offline (exact arithmetic, no local Lean build), emit frozen Lean, and
   let the CI kernel gate confirm. Never hand-edit emitted Lean; fix the family
   and regenerate. The proposer is untrusted; the kernel is the only trust.

## Enforcement

The manual discipline above is the floor. The proposed **skill-extraction
monitor** (a scheduled proposer agent that scans new proof commits across both
repos for shapes not yet covered by an existing emitter and drafts candidate
families into a quarantine dir for CI confirmation) is the mechanization of this
standing order — see `EMITTER_ROADMAP` / the monitor design when built.
