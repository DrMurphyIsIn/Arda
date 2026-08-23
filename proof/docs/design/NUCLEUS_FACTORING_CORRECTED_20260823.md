# Closing the nucleus: the corrected factoring (2026-08-23)

`conjecture1_proved = False`. This is the honest result of an ultrathink attempt to close the general
nucleus (the tree→family reduction) using LPRSC. **It corrects the factoring I proposed when LPRSC was
built** and pins the true residual. Every claim below is exact-`Fraction` verified
(`verification/accumulation_boundary_probe.py`) and cross-checked against the authoritative modules.

## The premise I had to correct

When LPRSC (the Lattice Power-Ratio Single-Crossing certificate) was built, I proposed:
> nucleus = [tree→family reduction, open] + [marginal-tie arithmetic, = LPRSC, built].

**This two-piece split is wrong.** The reduction's hard piece is *not* structural glue over an
LPRSC-solved tie. It contains its **own, distinct arithmetic phenomenon** that LPRSC cannot touch.

## What LPRSC actually solves, and what it cannot

LPRSC certifies an **isolated marginal tie**: a 1-parameter family whose value `R(n)` has a single
lattice minimum (the tie `n*=5`) reached by a single-crossing ratio, with `R(n*)=1` exactly. It closes
the near-star `R_ns(s)` and per-child base `B(kp)` families — the tie is *one lattice point*, bounded
away from any floorless limit.

The reduction's hard piece is the **pure-hub class `(0,0,m)`** (a hub with `m` children, no cherries).
The slack-ledger's context-free floor is *"provably absent"* here — and the reason is exactly an
integrality phenomenon, but **the opposite kind** from an isolated tie:

- **(A1) Achievable cavities accumulate at T0 = ρ_B−1 from below.** The closest achievable subtree
  cavity strictly below T0 creeps toward it as trees grow (gap `0.00367` at N≤5 → `0.00232` at N≤13,
  still shrinking). The achievable set is *dense up to T0*, not a single point with a gap.
- **(A2) So the pure-hub slack has no lattice floor.** With children at the T0-closest achievable
  cavity, the hub's own slack → 0 as `m` grows (`0.049 → 0.019 → 0.0055 → 0.0026`). LPRSC needs a
  lattice minimum bounded away from a floorless limit; the pure hub has none. **LPRSC cannot close it.**
- **(A3) Amortization is the right mechanism.** The *same* hub's TOTAL ledger (hub + all child subtrees)
  *grows* with `m` (`4.3 → 14.2 → 71.0`): the deep children that force cav→T0 each pay their own ledger,
  dominating the hub's slack loss. This is `amortized_hub_bound.py` (`ledger ≥ 0.0235·#pure-hubs`,
  EXIT 0, critical profile symbolic), **not** a per-node floor.

**Isolated tie (one lattice point, gap below it) ⟹ LPRSC. Accumulation boundary (dense up to T0,
floorless) ⟹ amortization.** These are different arithmetic phenomena requiring different tools.

## The corrected factoring

The nucleus is **three** pieces, not two:

| piece | phenomenon | tool | status |
|---|---|---|---|
| isolated marginal tie (near-star, base) | single lattice min, single-crossing | **LPRSC** | built this session |
| accumulation boundary (pure hub, cav→T0) | dense-to-T0, floorless | **amortization** | `amortized_hub_bound`, cert-level |
| structural reduction (depth-collapse, plain model, non-monotone child) | combinatorial | slack-ledger dichotomy | Python-cert assembled; **G7 = Lean-ize** |

## Where the nucleus actually stands (authoritative, cross-checked)

Reconciling with `conjecture1_status.py` and the R7' architecture (`verify_20260814` all-green):

- **Weak form `logΦ ≤ 0` (slack ≥ 0):** proven (Lean super-solution, `phi_le_one`, no sorry).
- **Context-free floors (non-tie classes):** closed (`g1_floor_certificates`, "G1 COMPLETE for the arc").
- **Amortized hub bound (accumulation boundary):** `ledger ≥ 0.0235·#hubs`, EXIT 0, critical family
  symbolic, rational rigor via `g1_endpoint_certificates`.
- **R7' stages I–IV:** Stage I unconditional, Stage II closed, III/IV discharged (G5/G6 + R5/R6).
- **Isolated tie families:** now unified + strengthened (strict-off-tie) by LPRSC.

**So the reduction is far more assembled than "open" suggests — at the Python exact-certificate
(mathematical) standard.** The genuine remaining distance is overwhelmingly **G7 (Lean formalization of
the R7 assembly = the R47 campaign)** + independent review + the tight-form R3 (isolated tie, which LPRSC
now addresses), *not* a missing mathematical idea in the reduction — with the caveat that the certs rest
on the equal-children/Jensen relaxation whose full rational hardening is the residual G1 work (largely
done this arc).

## Honest bottom line

I did not close the nucleus, and I did not find that LPRSC closes the reduction — the opposite: I
verified LPRSC is the wrong tool for the reduction's hard piece, which is a distinct *accumulation*
phenomenon already handled (cert-level) by amortization. The genuine value of this pass is a **corrected,
verified strategic map**: it prevents wasted effort pointing LPRSC at the pure hub, and relocates the
true frontier to **G7 Lean-ization + relaxation-hardening + review**, not a new arithmetic breakthrough
in the reduction. `conjecture1_proved = False`.
