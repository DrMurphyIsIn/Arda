# The Brualdi–Goldwasser frontier: one open arithmetic inequality

**Status: `conjecture1_proved = False`.** Every claim below is exact-checked (Fraction
arithmetic); the layers marked ✅ are kernel-verified in `formalization/`; the single layer
marked ❌ is the open core. This document states the frontier precisely — it is *not* a proof
of the open layer, and does not pretend to be.

## The object

For a rooted tree `C`, the block factor is `F(C) = W^n · (∏_v a_v)^11`, `W = 64/621`, where
`a_v = 1 + z_v S_v` is the cavity amplitude (`z_v = 1/(#children+1)`, `S_v = Σ child cavities`),
and the cavity message is `μ_C = z_root / a_root`. The Brualdi–Goldwasser conjecture (this
normalization) is `F(C) ≤ 1` for every rooted tree, equality iff the near-star tie `N(0,5)`
(and its 5 relatives `N(c,k)`, `c+k=5`). This is the matching-expansion of `per(L)/∏deg`
raised to the 11th power and per-vertex normalized.

## The reduction (proven layers)

Strong induction on `F ≤ 1`. A block is a hub with `j` children `C_1..C_j`; write
`S = Σ μ_{C_i}`, `a_hub = 1 + S/(j+1)`, `μ_hub = 1/((j+1) a_hub)`, so
`F_hub = W · a_hub^11 · ∏_i F(C_i)`.

| Layer | Status | Exact content |
|---|---|---|
| multi-hub front → single-hub | reduced | irreducible cores are single-hub-type (this session) |
| **tie-dominant half** `S ≤ 3j/23` | ✅ kernel-checked | `a_hub < 26/23` ⟺ `23S < 3(j+1)` (from `23S ≤ 3j`); `W(26/23)^11 < 1`. So `F_hub < 0.397`. (`TieClosure.lean`) |
| pure-tie boundary | ✅ green | `W(26/23)^11 < 1` ⟺ `64·26^11 < 621·23^11` (`family_martingale`) |
| near-star family `F(N(c,k)) ≤ 1` | ✅ green | `nearStar_family_le_zero`, unconditional; tie `c+k=5` ⟺ `64·243·23 = 621·576` |
| arm bound | ✅ green | `F_arm = 486/529 < 1` |
| arms+ties skeleton | ✅/⏳ | adding a tie decreases `F_hub` for `p ≥ 1`: `a(p,q+1) ≤ a(p,q)`, telescoping `(14p−9)/(69(j+1)(j+2)) ≥ 0` ⟺ `p ≥ 9/14`. So arms+ties `≤ F_ns(p) ≤ 1`, tight only at `(5,0)=N(0,5)`. |
| **master inequality** | ❌ **open** | the arithmetic core, below |

## The open core: the tight master inequality

The tie-dominant half uses only `F(C_i) ≤ 1`. The **near-star half `S > 3j/23`** has
`a_hub > 26/23`, so `F_hub ≤ W·a_hub^11` is `> 0.397` — the hypothesis `F(C_i) ≤ 1` is *not
enough*; the proof needs the *slack* `∏F(C_i) < 1`. That slack is exactly:

> **Master inequality (OPEN).** For every real rooted block `C` with message `μ_C` and factor
> `F(C)`, `F(C) ≤ Ψ(μ_C)`, where `Ψ(μ) = ` the maximum of `F` over *real* blocks of message `μ`
> (the achievable extremal envelope). Equivalently: for a hub with `S = Σμ_i > 3j/23`,
> `W(1+S/(j+1))^11 ∏_i F(C_i) ≤ 1`.

`Ψ` is realized piecewise by the arm (large `μ`), the near-star (`μ ≈ 3/23`), and the
tie-recursive family (`μ → 0`) — all `≤ 1` and green — with the near-star tie `Ψ(3/23) = 1`
the global max.

## Why it is arithmetic and not analysis (the exact obstruction)

1. **No continuous certificate exists.** The *continuous* near-star `F_ns(k) = W·((4k+3)/(3(k+1)))^11·(486/529)^k`
   exceeds 1: `max F_ns = 1.000459` at `k ≈ 4.82`. Only *integer* `k` give `B(k) ≤ 1` (`B(5)=1`
   exactly). So any valid envelope bound lives on the integer lattice of achievable messages;
   any smooth / SOS / potential certificate provably fails (lattice-convexity obstruction,
   arXiv:2206.12253). A numerical "`0/N` on the achievable domain" is the phantom, not a proof —
   the `> 1/2` and non-integer-`k` "witnesses" are fictitious continuous points.
2. **The optimal child is non-monotone.** The `Ψ`-maximizing child is not monotone in the base
   (`k*: 4 → 3` in the 2-child case), so no clean rearrangement reduces a general child to a
   single extreme.

## The `23`-adic content (the tools staged for it)

The near-star family is proven by ratio-unimodality, whose step is exactly arithmetic:
`R(s+1)/R(s) = (529/486)·((4s+3)(s+2)/((4s+7)(s+1)))^11`, with `529/486 = 23²/(2·3⁵)`,
crossing 1 once at `s = 5` (`R(5) = 1`). The tie identities `64·243·23 = 621·576` and
`64·26^11 < 621·23^11` are the same `23`-adic world. The **per-graft crossing-once**
`r(k) = boost(k)^11 · B(k)` is exact and unimodal (tie-optimal). These are the right
instruments; **what is missing is the integer-tight reduction of an arbitrary `μ_C` to its
arm/tie extreme** — a `23`-adic / integer-crossing argument extending the near-star family's
integrality proof to arbitrary branching. It is genuine new mathematics; neither the literature
(the raw problem's natural maximizer conjecture was *refuted* in 2026, arXiv:2605.14176) nor
this campaign has it.

## Verdict

Brualdi–Goldwasser is reduced, layer by kernel-checked layer, to the single master inequality
above. That inequality is `OBSTRUCTED-AND-LOCATED`: sharply stated, provably arithmetic,
genuinely open. `conjecture1_proved = False` — and it stays there until the arithmetic closes,
not until the tests are clean.

*Every numeric/identity claim in this document was exact-verified in `Fraction` arithmetic.*
