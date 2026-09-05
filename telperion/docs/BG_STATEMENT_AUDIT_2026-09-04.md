# BG spine statement-identity audit — the positive half of the trust boundary (2026-09-04)

The 2026-09-04 crosscheck (`BG_CROSSCHECK_2026-09-04.md`) certified the **negative
half** of the trust boundary: all 182 BG theorems compile and are axiom-clean (no
`sorryAx`). But axiom-cleanliness does not certify that a theorem states the *intended*
proposition — a theorem can compile, be axiom-clean, and still be the WRONG (weaker)
claim. That is the **positive half**, and it was the structural blind spot of the
axiom-only audit. The AXLE third tour named it the #1 gap (signature/statement match,
`verify_proof` with `use_def_eq=False`); this closes it for the trust-critical BG spine.

## Tool: `statement_match` (additive gate)

`statement_match_check(intended, env_dir=…)` — for each `{decl → intended_type}`, emits
`theorem __sigmatch_… : <intended> := @<decl>` and elaborates: Lean accepts iff the
decl's type is *defeq* to the intended type; a weaker/different decl fails with a type
mismatch. `def_identity_check` does the analog for a Prop-valued `def` (via `Iff.rfl`).
Both compose on `verify_lean` — no change to the (parallel-session-hardened) verify core.

## Audit: the additive-subaction spine

Intended statements written INDEPENDENTLY from the additive-subaction math, checked defeq
against the in-repo theorems (env = built `R3Cert`, module `BGSCLSubaction`):

| declaration | intended (independent) | result |
|---|---|---|
| `ceiling_of_subaction` | `∀ ρ, IsSubaction ρ → (∀ b, 0 ≤ ρ b) → ∀ b, bell b ≤ 0` | **MATCH** |
| `ceiling_of_witness` | `IsSubaction ρwit → ∀ b, bell b ≤ 0` | **MATCH** |
| `ceiling_of_gstep` | `GStep → ∀ b, bell b ≤ 0` | **MATCH** (added 2026-09-04) |
| `IsSubaction` (def-identity) | `∀ cs, (log(1+(Σ bY)/(|cs|+1)) − F*) + ρ(node cs) ≤ Σ ρ` | **MATCH** |

**Gate liveness confirmed**: the same audit with a deliberately weakened intended
(`bell ≤ 1` in place of `≤ 0`) correctly **MISMATCHED** — the gate is live, not vacuously
passing.

## Why this matters most for `IsSubaction`

`IsSubaction ρwit` is the ONE open hypothesis the whole cell family is discharging. If its
*definition* had been silently weakened (e.g. a spurious extra hypothesis, or `≤` flipped),
every cell would be closing a vacuous obligation and the axiom audit would still pass. The
def-identity check confirms `IsSubaction` unfolds to exactly the genuine per-vertex additive
inequality `e_v + ρ(v) ≤ Σ_c ρ(c)` — so the cells are discharging the *real* obligation, and
`ceiling_of_subaction`/`ceiling_of_witness` carry it to the branch ceiling `bell b ≤ 0`
without weakening.

## Verdict

Both halves of the trust boundary now hold for the BG additive-subaction spine:
- **negative** (axiom audit): every proof is valid and `sorry`-free (182 theorems);
- **positive** (this audit): the bridge, the witness reduction, and the open obligation's
  definition state EXACTLY the intended propositions — a weakening would be caught.

Scope note: the gate is defeq-strict, ideal for canonical spine statements; it is *not*
used for the enclosure atoms (arithmetically-varied forms — covered instead by the
emitter-regression in the crosscheck). The gate is now BATCHED (all spine checks in one `import Mathlib` load — 3 checks in 5.5s
vs ~18s per-decl; `lean --stdin` is single-shot so a persistent LSP is the only way to
amortise across *separate* calls, deferred) and packaged as a CI gate:
`scripts/bg_spine_audit.py --env <built R3Cert>` (exit 0 iff the spine states its intended
propositions). `ceiling_of_gstep` (the sibling multiplicative bridge) is now included and
MATCHES. And the **fixed-N capstone** `conjecture1_of_layers_fixedN` (R47 track, built
separately) MATCHES its independent intended spec `∀ tie, Hnorm → Hdom → ∀ t, Aobj t ≤
Aobj (tie (usize t))` — the reduction of Conjecture 1 to the two open layers is honest,
no weakening. So the ENTIRE trust-critical chain top-to-bottom (capstone → bridges →
witness → the open obligation's definition) states exactly its intended propositions.
conjecture1_proved = False.
