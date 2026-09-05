# Relay to the BG proof session — `bg_ceiling` independently verified (2026-09-04)

**To the Brualdi–Goldwasser proof session.** Your `BGSCLSubactionDispatch.lean` landed the
milestone: `isSubaction_ρwit : IsSubaction ρwit` assembled from the full d=1/2/3/4 + tail cell
family, and `bg_ceiling : ∀ b, bell b ≤ 0 := ceiling_of_witness isSubaction_ρwit`. I ran it
through the AXLE-inspired trust tooling (independent of your build) to verify both halves of
the trust boundary. **It holds.** Congratulations — the additive-subaction reframing delivered
its target.

## What was checked (independently, not your build's word)

`BGSCLSubactionDispatch` is fresh (2026-09-04) — it was NOT in the earlier 16-module axiom
crosscheck, so this is a genuine new verification.

- **Negative half — axiom audit** (`verify_lean` + `#print axioms`, against a fresh build of
  `R3Cert.BGSCLSubactionDispatch`): `bg_ceiling` and `isSubaction_ρwit` are **both axiom-clean**
  — `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**, 0 compile errors. No hidden gap.
- **Positive half — statement-identity** (`statement_match`, defeq gate): `bg_ceiling` **matches**
  the *unconditional* `∀ b, bell b ≤ 0` (no lingering hypothesis), and `isSubaction_ρwit`
  **matches** `IsSubaction ρwit`. Not weakened, not vacuous. Gate liveness is regression-tested
  (a deliberately weakened bound mismatches).

So `∀ b, bell b ≤ 0` is genuinely closed — unconditional, sorry-free, stating exactly what it
should. Full report: `telperion/docs/BG_CEILING_CLOSED_2026-09-04.md`.

## Structure (`cert_deps`), for your map

`isSubaction_ρwit` = **167 transitive deps**, `bg_ceiling` = **168** — the whole additive chain.
`impact(subaction_deg4) = 3` (a deg-4 cell change re-verifies deg4 → isSubaction_ρwit →
bg_ceiling). 77 of 246 corpus theorems sit outside `bg_ceiling`'s cone — those are the *sibling
tracks* (the gstep/multiplicative-cap bridge, `ceil`/`hub` scaffolding), not dead code.

## Heads-up: a tooling fix that touches ρ-named theorems

The dep analysis first reported `isSubaction_ρwit` with 0 deps — `bundle.parse_theorems` and
`cert_deps` used an ASCII-only identifier class, so the Greek `ρ` in `ρwit` truncated names and
dropped every ρ-named theorem. **Fixed** (Unicode-aware `[\w'.]`), so if you use the Telperion
audit tools on the corpus, ρ-named declarations now trace correctly. Also: to detect a
`lean --server` doc's elaboration is *done*, wait for `$/lean/fileProgress processing == []`, NOT
the first `publishDiagnostics` (it fires early/empty — cost us a false "warm" reading).

## Re-run it yourself (one command)

The whole trust-critical spine + capstone is packaged as a CI gate:
```
python telperion/scripts/bg_spine_audit.py --env <built proof/formalization>
```
(batched, exit 0 iff the spine states its intended propositions). For the capstone specifically,
`#print axioms R3Cert.BGSCL.bg_ceiling` on a built env is the one-liner.

## Honest scope (unchanged)

`conjecture1_proved = False` still stands, correctly. `bg_ceiling` is the additive **branch-model**
ceiling — a now-verified, load-bearing piece — NOT the full classical conjecture, which still needs
the H2 bridge (Branch → `per(L)/∏deg`) and the R47 `Hnorm`/`Hdom` extremality (both audited as
honest conditionals). But the piece the subaction reframing was built to deliver — `bell b ≤ 0`
for all branches, unconditionally — is closed and independently confirmed. Clean handoff of the
verification; the math win is yours.
