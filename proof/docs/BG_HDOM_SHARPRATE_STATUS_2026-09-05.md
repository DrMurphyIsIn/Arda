# BG Hdom status: merge-step closed, but Hdom-domination (SharpRateNF) still open — near-star insufficient (2026-09-05)

Careful reconciliation of the residual-cell closure against the actual capstone, with a concrete
obstruction to the near-star route. `conjecture1_proved = False`.

## What IS closed (parallel session, correct)

- `step_mono` (`R47StepMono.lean:98`): an `OrderedStep` merge never decreases `Aobj` on
  Balanced+Capped states. PROVEN.
- `chain_to_normalForm`: iterating merges reduces any Balanced+Capped `s` to a **merge-normal** `s'`
  with `Aobj(backboneU s) ≤ Aobj(backboneU s')`. PROVEN (uses `step_mono`).
- The 5 residual GenEnv cells are outside the Balanced+Capped merge-step regime (Balanced ⇒ arms
  ∈{4,5} ⇒ hub degree ≤7 < the deg_C=8 lowest failure threshold), and `R47R7KelmansGenEnvCert` is
  an unimported leaf. So the residual cells are a non-issue for the **merge step**. CORRECT.

## What is NOT closed (the precise open obligation)

`conjecture1_of_layers_fixedN` (`R47TopCapstoneFixedN.lean:51`) still takes **`Hdom` as an explicit
hypothesis**:

    Hdom : ∀ s, Balanced s → Capped s → (∀u, ¬OrderedStep s u) → Aobj(backboneU s) ≤ Aobj(tie(stateSize s))

`step_mono`/`chain_to_normalForm` discharge the *reduction to* merge-normal form — they do **not**
discharge `Hdom`, which is the **domination of the merge-normal state by the tie** (`= SharpRateNF`,
nowhere proven). "Hdom fully closed via step_mono" conflates the (closed) merge-step reduction with
the (open) merge-normal domination. These are different obligations; only the first is done.

## Concrete obstruction: the NEAR-STAR tie is insufficient (exact witness)

`sharpRate_of_rateBound` discharges `SharpRateNF` against the near-star tie from `hrate`
(`Aobj(backboneU s) ≤ (26/23)/rhoB·rhoB^n`) + `hfit` (size-fit `n = 1+11K`). But `hrate` is **FALSE**
for a legitimate merge-normal Balanced+Capped state — the `OrderedStep` merge retains the absorber's
cherries `cA`, so cherry-carrying merge-normal hubs are reachable:

| state `s` | stateSize | `Aobj` (exact `per(L)/∏deg`) | near-star bound | verdict |
|-----------|-----------|------------------------------|-----------------|---------|
| `[([5,5,5,5,5], 1)]` (1 hub, 5 load-5 arms, **1 cherry**) | 58 | `322571469530889/2147483648` ≈ 150209.046 | ≈ 146974.544 | **Aobj exceeds by 2.20%** |

It is Balanced (arms ∈{4,5}, `c=1≤5`), Capped (5 arms), single-hub hence merge-normal. The bound is
violated because `n=58 ≠ 1+11K`, so the near-star is not the tie at that size (`hfit` fails). At an
aligned cherry-free size the bound is tight (ratio `0.91944610 = (26/23)/rhoB` exactly).

Self-verifying: `proof/verification/sharprate_nearstar_gap.py` (`run()` asserts the exact violation).

## Conclusion — the genuine open crux

Discharging `Hdom`/`SharpRateNF` requires a **per-size broadened tie family** (caterpillars carrying
cherries at non-`1+11K` sizes), not the bare near-star. The `hrate` bound is only correct at aligned
sizes. This is the honest open frontier of the Hdom layer (alongside `StraightProgress_sized` for
Hnorm). The merge-step machinery below it is proven; the residual-cell worry is genuinely gone.
`conjecture1_proved = False`.
