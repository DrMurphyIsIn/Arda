# BG is an integrality gap, not a quasicrystal (2026-08-31)

A diagnostic result: the Brualdi–Goldwasser upper bound is hard for a *specific, provable* reason — the optimum
is an integer-program optimum with a positive integrality gap — and this rules out an entire class of proof
attempts. `conjecture1_proved = False`.

## The numbers

The broom family's per-vertex free energy `f(c) = log(total(c))/(2c+1)`, `total(c) = (3/2)^{c-1}(4c+3)/(2(c+1))`:

| | value |
|---|---|
| integer argmax | `c = 5`, `f(5) = F* = log(621/64)/11 = 0.20658618` (exact rational optimum `621/64`) |
| continuous argmax | `c* ≈ 4.819`, `f(c*) ≈ 0.20659010` |
| **integrality gap** | `f(c*) − F* ≈ +3.9·10⁻⁶` (continuous **overshoots**) |
| peak curvature | `f''(5) ≈ −2·10⁻⁴` (nearly flat) |
| near-degenerate band | every real `c ∈ [4.06, 5.87]` within `10⁻⁴` of the max — `c = 4, 5, 6` almost tie |
| arithmetic fingerprint | `4·5+3 = 23` (prime), `621 = 27·23`, `v₂₃(total(B5)) = +1` |

## Crystal, not quasicrystal

A quasicrystal is governed by an *irrational, badly-approximable* order parameter (golden ratio) and an
*aperiodic* structure. BG's optimum value is an **exact rational** (`621/64`) achieved by a **periodic** motif
(the star of identical `B(5)`-brooms). So it is a **crystal** whose unit cell is arithmetically pinned — not a
quasicrystal. The one quasicrystal-adjacent feature is the **near-degeneracy** (flat peak, a swarm of near-ties),
which is what makes the residual delicate — but the frustration is degeneracy, not aperiodicity.

## The no-go (kernel-gated: `SmoothNoGoCertificate` / `bg_smooth_nogo`)

Because the continuous relaxation overshoots, **any certificate that relaxes the integer arm-count** — convex,
SOS, moment/Lasserre, tangent/concavity, spectral — is bounded below by `f(c*) > F*` and therefore **cannot**
certify `F(T) <= F*`. This is a theorem, not a heuristic: it is exactly why every smooth bound in this campaign
landed `~10⁻⁴` loose, and why eleven "closure" overclaims all sprang the same trap. Gated via the single
`norm_num` atom `f(24/5) > F*` (a rational witness above `F*`; cleared to `209 L(3/2)+55 L(111/5)−55 L(2)−55
L(29/5) > 53 L(621/64)`, frozen log-enclosures).

## Consequence for the closing argument

The proof of the BG upper bound — and of the open residual (b) (the small-degree refined ceiling, binding at
`d = 2, 3`, the most integer-constrained regime) — must be **arithmetic**: exact on the integer arm/child count,
in the spirit of the `× 11` clearing that turns `F*` into `621/64` and the `23`-adic broom optimum. A transfer-
operator or valuation bound that is tight on integers, not another smooth relaxation. This mirrors the earlier
Φ¹¹ finding that `Φ ≤ 1` "must be arithmetic (23-adic)" — the same obstruction, now made a checked theorem for
classical BG. `conjecture1_proved = False`.
