# The 23-adic reconciliation: Φ¹¹ near-star ≡ classical-BG broom (2026-08-31)

Resolves the long-standing "Φ¹¹ is NOT classical BG" tension and connects the two BG programs at the
`621/64 = 27·23` tie. All exact (`Fraction`); verified in `tests/test_spider_broom.py`. `conjecture1_proved =
False`.

## The tension

- **Analytic half (this owner):** classical BG `π = per(L)/∏deg`; the extremal single-hub star-of-B(5)-brooms has
  `total(5) = 621/64`, growth rate `F* = log(621/64)/11`, `c = 5` optimum (`bg_broom_optimum`).
- **Domination-bridge half (origin repo):** the rooted-branch invariant `Φ¹¹` with a near-star arithmetic proof —
  `Φ ≤ 1` on `N(c,k)`, equality iff `c+k = 5`, via `R(s+1)/R(s) = (529/486)(1 − 1/((4s+7)(s+1)))^11` crossing `1`
  once and `R(5) = 1` exactly (`64·243·23 = 621·576`). Prior audit flagged `Φ¹¹ ≠ classical BG` (`81/8 ≠ 621/64`
  at the tie).

## The finding (exact)

The Φ¹¹ near-star invariant `R(s)` **is** the classical-BG broom cross-exponentiation ratio:
```
R(s)  =  X(s)  :=  total(5)^(2s+1) / total(s)^11      (exact, verified s = 0…11)
```
where `total(c) = (3/2)^{c-1}(4c+3)/(2(c+1))` and `X(s) ≥ 1 ⟺ rate(5) ≥ rate(s)` (`rate(c) = total(c)^{1/(2c+1)}`).
Equivalently the recurrence factor
```
broom_ratio(s) = X(s+1)/X(s) = (529/486)(1 − 1/((4s+7)(s+1)))^11
```
is produced *identically* by the broom totals and by the Φ¹¹ near-star recurrence (`529 = 23²`, `486 = 2·3⁵`).

**So the two programs coincide exactly on the extremal near-star/broom family.** The `Φ¹¹ ≠ classical BG`
discrepancy (`81/8`) is on *non-extremal* structures; on the family where the maximum actually lives, `Φ¹¹` and
classical BG are the same object. For the extremality question — the only thing that matters — they agree.

## Consequence 1 — a closed, all-`c` proof of the `c = 5` optimum

`bg_broom_optimum` proved `rate(5) > rate(c)` by *finite* case-check (`c ∈ {2,3,4,6,7,8}`, cross-exponentiation).
The Φ¹¹ recurrence upgrades this to a **closed proof for every `c`**:
- `X(5) = 1` trivially; `broom_ratio(s) = X(s+1)/X(s)`.
- `g(s) = (4s+7)(s+1)` is strictly increasing ⟹ `broom_ratio` is strictly increasing.
- `broom_ratio(4) = 0.98877… < 1 < 1.01681… = broom_ratio(5)` (single crossing).
- ⟹ `X` strictly decreasing on `[0,5]`, strictly increasing on `[5,∞)` ⟹ `X(s) ≥ 1`, equality iff `s = 5`.

Captured in `spider_broom.broom_ratio` + `c5_unimodal_witness`. **This gate already exists:** the frozen
`examples/evolve_nearstar` certificate (evolve-loop champion `ratio_src = (486/529)(1 + 1/(4s²+11s+6))^11`, peak
`s* = 5`, emitted via `UnimodalMaxEmitter` + the `Telperion.unimodal_peak` prelude to
`lean/EvolveNearStar.lean`) is **exactly** `1/broom_ratio(s) = f(s+1)/f(s)` for `f = 1/X` (`4s²+11s+6 = g(s)−1`;
symbolic + exact-numeric verified in `test_spider_broom.py::test_evolve_nearstar_is_the_broom_c5_gate`). So the
already-kernel-gated `evolve_nearstar` unimodal certificate **is** the closed all-`c` proof of the classical-BG
`c = 5` broom optimum — the reconciliation gives that "evolve-discovered near-star" artifact its classical-BG
meaning. (`UnimodalMaxEmitter`'s design is precisely for this: `f` is not rational, only its ratio is.)

## Consequence 2 — the 23-adic tie and `emit_padic`

The tie is arithmetic: `R(5) = 1` is the integer coincidence `64·243·23 = 621·576` (`= 357696`), with
`621 = 27·23`, `529 = 23²`. The prior near-star analysis showed the tie root is `m = 3/23` and that **no smooth
certificate** closes `Φ ≤ 1` — it is a `23`-adic integrality fact. This puts **`emit_padic`** (valuation
certificates) on the BG critical path (cf. memory `rh_bg_shared_endgame_2026-08-31`): the `c = 5` optimum's
tightness is a `23`-adic valuation statement, and both the RH zero-free endgame and the BG bulk-discharge reduce
to the same box-positivity engine (`Handelman`/`SOS`/`cone`/`worst_corner`).

## What this buys the unified program

1. **The domination-bridge RUNG ladder (MR !75) is on the right target *for extremality*** — its near-star
   `piConfig` identities are the classical-BG broom ratio on the extremal family (the `9/23`, `3/23` in the
   RUNG-2 cells are the same `23`-adic tie). The `Φ¹¹ ≠ BG` caveat applies to non-extremal comparisons, not to
   the extremal-family identities the ladder consumes.
2. **My `c = 5` optimum gains a closed proof** (single-crossing), stronger than the finite gate.
3. **The shared crux is now one object:** the bulk discharge `φ_v ≤ F*` (analytic upper bound), the RUNG
   domination ladder, and the RH zero-free box-positivity all reduce to `emit_padic`/box-positivity at
   `621/64 = 27·23`. Next: build `bg_broom_c5_unimodal` (kernel gate) and route the bulk discharge through the
   same `emit_padic`/`worst_corner` engine.

See `proof/docs/design/BG_UNIFIED_PROGRAM_20260831.md` (architecture) and `BG_STAR_OF_BROOMS_RESULT.md` §5b
(bulk discharge). `conjecture1_proved = False`.
