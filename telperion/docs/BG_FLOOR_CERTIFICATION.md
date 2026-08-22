# Brualdi–Goldwasser R7 ledger-floor certification (chain class)

*2026-08-22 — companion to `examples/bg_floor/` and the BG kernel's
`proof/verification/g1_floor_certificates.py`.*

## Where this sits in the proof

The g-step family bound and the vertex/majorization lemma are **already closed on
main** (`CappedJointConfig.gstep_le_one_achievable` via
`GArmExtAbstract.gCoreOff_le_replicate`). The genuinely-open frontier is **R7** —
in particular **G1**, the symbolic hardening of the slack-ledger *context-free
floors*.

The (Lean-checked) `phi_le_one` hinge certificate gives a per-node super-solution
`slack_v ≥ 0`, and telescoping yields the ledger identity
`logPhi(T) = −φ(cav_root) − Σ_v slack_v`. R7 needs a **positive floor** for each
structural class's slack, so the ledger clears the fixed-n budget. Under the
equal-children/Jensen relaxation (the class infimum is attained at equal child
cavities `y ∈ (0,½]`), each floor is a **1-variable hinge minimization**:

```
slack(y) = p·L − a·log(3/2) − log(1+u) − (11/50)·D,
   D = (cav − T0)₊ − m·(y − T0)₊,   cav = 1/(k+1+S),   u = S/(k+1).
```

`g1_floor_certificates.py` certifies these in exact rational arithmetic by
adaptive bisection. This example emits the **chain class** (`a=0, nl=0, m=1`,
floor `27/5000`) as a **single clean two-cell Bernstein certificate** — the
Telperion beachhead for the G1 floor lemma.

## The chain class as two Bernstein cells

Chain: `p=1, k=1, S=y, u=y/2, cav=1/(2+y)`. Bracket the three transcendentals by
verified rationals (the kernel's `_verified_constants`):

- `L = log(621/64)/11 ≥ L_LO = 206586/10⁶`
- `log(1+u) ≤ u − u²/2 + u³/3 − u⁴/4 + u⁵/5` (alternating-series upper bound, `u≥0`;
  loss ~3·10⁻⁵ at `u=¼` — the tight bound the **tight** floor demands: the true
  minimum is ≈0.0055, only ~10⁻⁴ above the floor)
- `T0 = ρB − 1 ≥ T_LO = 2294736/10⁷`

Split the hinge at `T0` into two cells that tile `[0,½]`:

| cell | range | hinge | `D` |
|---|---|---|---|
| `bg_floor_chain_below_knee` | `[0, T_LO]` | `(y−T0)₊ = 0` | `cav − T0 ≤ 1/(2+y) − T_LO` |
| `bg_floor_chain_above_knee` | `[T_LO, ½]` | `T0` **cancels** | `cav − y = 1/(2+y) − y` (exact) |

On each cell, clearing the positive denominator `(2+y)` turns `slack_lb(y) − floor ≥ 0`
into a **degree-6 polynomial positivity**, certified by Telperion's Bernstein
emitter (nonnegative Bernstein coefficients) → search-free `ring` + `linarith`.
CI job: `bg-floor-compiles`.

The theorem certifies `0 ≤ numerator(slack_lb − floor)` per cell; since `(2+y) > 0`
that is exactly `slack_lb(y) ≥ floor`, and `slack_lb(y) ≤ slack(y)` by the rational
brackets above, so `slack(y) ≥ 27/5000` on the whole chain-cavity range. A too-high
floor (`≥ 1/100`, above the tight true minimum) is refused — no nonnegative
Bernstein certificate exists (`tests/test_bg_floor.py::test_too_high_a_floor_is_refused`).

## Scope and next classes

This is **one G1 brick**. The same two-cell recipe (rational log/`L`/`T0` brackets
→ hinge split → per-cell Bernstein) extends to the other context-free classes the
dichotomy relies on — `mixed (a≥1, nl=0, m)`, `bare-leaf (nl=1)`, `nl=2`, the six
tax-window shapes, and the `m≥4` collapse tail — each a slightly different rational
`slack_lb(y)`. The `m≥4` tail additionally needs the collapse lemma's monotonicity
(a `positivity` derivative-sign fact), not just interval Bernstein.

The **lemma-1 local Δslack inequality** is the parallel BG session's active
reduction and is deliberately **not** targeted here (collision avoidance); this
brick hardens the stable floor lemma. `conjecture1_proved = False`.

## Extension: the bare-leaf and nl=2 families (`examples/bg_floor_families/`)

The same recipe extends to the two main context-free classes with a child cavity
`y ∈ (0,½]` — **bare-leaf** (`nl=1`, floor `26/500`, `a∈0..9`, `m∈{1,2,3}`) and
**nl=2** (`nl=2`, floor `54/500`, `a∈0..6`, `m∈{1,2,3}`) — as **102** two-cell
degree-5 Bernstein certificates. Two refinements handle the general class:

- `log(3/2)` is now present (coefficient `−a`); bracket it above by `G_HI = 405466/10⁶`.
- `cav = 1/(k+1+S)` can cross `T0` inside `(0,½]`; since `cav` *decreases* in `y`,
  `(cav−T0)₊ ≤ (cav(0) − T_LO)₊ =: Dc`, a per-class constant. The `−m(y−T0)₊` help
  term is kept via `(y−T0)₊ ≥ y − T_HI` on the above-cell.

Margins are wide (`≥ 0.0089` bare-leaf, `≥ 0.065` nl=2) — strictly lower-risk than
the tight chain. CI job: `bg-floor-families-compiles`.

## The remaining facets (`examples/bg_floor_r7_facets/`)

The last three pieces of the context-free floor layer:

- **m=0 (childless):** slack has no cavity `y` — a point value
  `p·L − a·log(3/2) − log(1+u0) ≥ floor`. Emitted as **structured `norm_num`
  rational inequalities** (bare-leaf `a∈1..9`, nl=2 `a∈0..6`, tax shape `(1,1,0)`).
- **m≥4 (collapse tail):** the collapse monotonicity `R3Cert.R7CollapseMono.g_mono`
  (the kernel session's brick) puts the min at `y=T0`, and `u` is monotone in `m`
  toward `T0`, so a single **m-uniform** point bound
  `p·L_LO − a·G_HI − log1p_upper(u_env) ≥ floor` covers all `m≥4`. Also `norm_num`.
  Each point fact is cross-checked against the kernel's own `certify_floor_m0` /
  `certify_collapse_m_ge_4`.
- **tax windows:** six in-window floors (`amortized_hub` tax lemma) on the `y`-subrange
  where the cavity meets `[T0−29/1000, T0+29/1000]`, plus the below-window `m∈{2,3}`
  shapes. These are the **tight binding floors** (`(2,0,1)` clears by ~5·10⁻⁵), so
  they use a **degree-9** log bound and the **exact** `cav = 1/(k+1+S)` with hinge
  splits at `y=T0` (`T_LO/T_HI`) *and* `cav=T0` (a bracketed `y`-threshold, since
  `(cav−T0)₊ ≤ cav−T_LO` only where `cav ≥ T_LO`) — Bernstein positivity per cell.

CI job: `bg-floor-r7-facets-compiles`. With this, the context-free floor **lemma 2**
is fully Telperion-certified across all classes; **lemma 1** (knee-critical) and the
**G7** assembly remain (Session B). `conjecture1_proved = False`.
