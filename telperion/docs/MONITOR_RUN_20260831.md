# Skill-extraction monitor — first run on live 48h corpus (2026-08-31)

`shape_scout.py` run over 358 Lean files / 18,040 theorems from the current
BG + RH + P-vs-NP work (`telperion/examples/*`, `proof/formalization/R3Cert`,
`rh_lean`). This validates the monitor against work that was NOT hand-mapped.

## Buckets

| bucket | count | meaning |
|---|---|---|
| COVERED (emitter-generated) | 13,796 | already automated (frozen telperion output) |
| CANDIDATE (hand-written, emitter-shaped) | 2,881 | proposal queue |
| TRIVIAL (all-numeric) | 282 | norm_num/decide, filtered |
| STRUCTURAL (no emitter) | 1,081 | needs human Lean |

## What it got right (unsupervised)

- **Auto-recovered the known RH→BG channels** — with no hand-mapping:
  - `valuation` → `BGGateStrictness:deficit_v23_k{1,2,3}` (the 23-adic divisibility
    facts) → `emit_padic`.
  - `bracket` → `BGRhoBSqrt:bg_rhob_e2_sqrt2_tight`, `SqrtBracket:sqrt_{two,three,ten}`
    (the √2 crux, first RH→BG spill) → `emit_bracket`.
- **Firewalled the tree→hub research core** — all 50 `R47R7*` obligations
  (`Aobj_child_replace_le`, `strDefect_*`, `DeepPerm` decode) bucketed STRUCTURAL,
  no false "I can emit this." Matches the handoff: two genuine research obligations,
  everything structural around them proven.

## New lead surfaced (+ classifier fix)

- **P-vs-NP joins the shared engine.** `Hsq.lean:hsq_of_subsetForm` —
  `∀ s, s.totalDegree ≤ d → 0 ≤ pe nq (s²)` — is a **pseudo-expectation
  sum-of-squares** obligation (the SoS-3XOR / P-vs-NP lane). It is SOS-shaped, i.e.
  the **same box-positivity/SOS engine** BG's `bg_bulk_discharge` and RH's zero-free
  region use. The monitor initially mis-labeled it `interlacing`; `classify()` now
  routes `0 ≤ pe(… ^ 2)` to `sos_psd` → `SOSEmitter`.
- Consequence: the shared-engine reassessment now spans **three programs** —
  RH (zero-free `(1+x)^n` Handelman), BG (bulk-discharge `φ_v ≤ F*`), and P-vs-NP
  (SoS pseudo-expectation `0 ≤ pe(s²)`) — all box-positivity / SOS. The 23-adic tie
  remains BG-internal (BG↔Φ¹¹); the engine is the three-way meeting point.

## Honest scope

CANDIDATE ≠ closed. The 2,881 candidates are shape-matched, not certified; the value
gate is the offline certify round-trip (`--certify`) then the CI kernel. The
STRUCTURAL core (tree→hub, the tight-τ discharge rule) is the real open research and
no emitter reaches it. `conjecture1_proved = False`.
