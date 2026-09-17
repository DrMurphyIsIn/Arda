# Multiplicative-rigidity search — CLEAN NEGATIVE (result)

*Adversarial multi-agent search `wylptmzxv` (13 agents; 5 explorers + 6 skeptics +
synthesis; ~1.14M tokens; literature web-verified, corpus read against disk).
Outcome: the seed idea is **REFUTED as an RH route across all six angles.** This is a
valid, valuable result. `conjecture1_proved = False`.*

## Seed (refuted)
Can the zeta comb's completely-multiplicative Euler-product Bragg intensities
substitute for uniform discreteness as the hypothesis that forces reality (a
"multiplicative Lee–Yang")? **No.** Two walls do all the work:

1. **Conservation of difficulty.** Multiplicativity (H-mult) is *unconditional/free*
   for the zeta comb (`−ζ′/ζ = Σ (log p) p^{−ks}` is a log-derivative of an Euler
   product; `QC_RIGIDITY_MEMO §2.1`). Substituting a *free* hypothesis for the
   load-bearing one does no work — the cost relocates verbatim to temperedness
   (H-temp), which is RH-equivalent. You re-import RH.
2. **Support-rigidity, not weight-rigidity.** Every genuine reality-forcing theorem
   quantifies over SUPPORT, not mass: OU20 (uniform discreteness); ACV24
   (arXiv:2303.03201 — re-fetched: real-rootedness is a HYPOTHESIS, never derived from
   multiplicativity); Favorov (bounded spectrum); Arias de Reyna (temperedness). Zeta
   fails on the SPECTRUM side (`primeLogSpectrum_dense`, reconfirmed via PNT prime-gap
   ratio → 0). Multiplicativity of *intensities* is orthogonal to a *support* property,
   so it cannot supply the missing rigidity. Bounded below by the open Selberg degree
   conjecture (Kaczorowski–Perelli, Annals 173 (2011)).

## Per-thread collapse (no survivors)
- `mult-leeyang` → conservation of difficulty (H-mult free).
- `selberg-collapse` → "mult + FE" IS the degree-1 Selberg axiom set; converse theorems
  fix the object's identity but are silent on zero location ⇒ unfolds to RH.
- `lit-sweep` → the rigidity is support-based; only fresh residue is TERMINOLOGICAL.
- `euler-factor` → the infinite product's spectrum is dense; uniform discreteness dies.
- `cross-route` → Li>0 and Λ≤0 are both RH-equivalences; any link is RH⇒RH (vacuous).
- `formalize-P1` → the actual Bragg amplitude is von Mangoldt Λ, which is NOT completely
  multiplicative — a completely-multiplicative amplitude describes a DIFFERENT measure.

## The verified guardrail
`telperion/examples/multiplicative_nogo/lean/MultiplicativeNoGo.lean`, compiled v4.32,
`[propext, Classical.choice, Quot.sound]`, 0 sorry:
`not_completelyMultiplicative_vonMangoldt` — `Λ(2·3)=0 ≠ log2·log3 = Λ(2)·Λ(3)`. The
formal heart of the refutation, and a permanent anti-overclaim guardrail against the
whole multiplicative-substitution family.

## Corpus errata (for the owners)
The `formalize-P1` thread flagged stale line-number citations for `DefectDictionary.lean`
(the quarantine claim is independently confirmed by `RvMRoutePInertia.lean:173-185`).

`conjecture1_proved = False`. The seed is a dead end — verifiably — and the map is sharper
for it: on this wall, only a SUPPORT-side / temperedness idea can work; weight-side
(multiplicative) substitution provably cannot.
