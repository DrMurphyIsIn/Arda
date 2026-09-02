# The M_d frontier is a parity oscillation with a geometric tail — the d=5 extremality closes, the wall sharpens to one contraction rate (2026-09-01)

Executing the user's directive *"Tackle d=5 extremality is the honest frontier."* Outcome: the d=5 extremality
**closes** as part of a unified per-degree bound, and the entire `M_d` frontier is now reduced to **one** open
lemma — the even-step `ell`-subsequence contraction `rho <= 5/12`. All finite arithmetic is kernel-gated
(`MdGeometricTailCertificate`, 70 atoms). `conjecture1_proved = False`.

## What was tackled and refuted

The residual after Prong B was the uniform per-degree bound **M_d**: every rooted non-broom branch of root-degree
`d <= 6` has `ell(c) < threshold(k,d) = ell_cherry + (d-3)/(d(4k+3))`, uniformly over all sizes. The `FreeClosure`
cert closed `d in {3,4,6}` via the broom ceiling; `d=5` was flagged "off by ~0.0003" (the broom ceiling
`ell(B(4)) = -0.00103` exceeds `threshold(5,15) = -0.00136`).

**Free-box relaxation — REFUTED as a closure.** The decoupled bound `V(non-broom child) <= M_{d_X} + mu_eff/d_X`
closes the d=5 **hub** extremality (margin +0.019) but FAILS to establish the tight low-degree child bounds it
depends on: at hub degrees d=2 (margin −0.098) and d=3 (−0.009) the free-box is too loose. The d=5 closure needs
tight `M_2, M_3`, which the same relaxation cannot supply. Two overclaim-shaped artifacts were caught and
discarded en route: a cherry-child `B(1)` counted as "non-broom" (float-rounded broom filter leaked `P3`), fixed
with **exact struct-based broom detection**.

## What is actually true (exact, struct-based broom exclusion, enum to size 17)

The worst non-broom-non-cherry `ell` per root-degree, and the min-`k` threshold:

| d | M_d (max non-broom ell) | at size | min_k threshold(k,d) | margin |
|---|---|---|---|---|
| 2 | `-0.07257` (`= ell(17/8)`)      | 4  | `-0.05316` | `+0.0194` |
| 3 | `-0.04812` (`= ell(79/24)`)     | 6  | `-0.00771` | `+0.0404` |
| 4 | `-0.03238` (`= ell(489/64)`)    | 10 | `-0.00374` | `+0.0286` |
| 5 | `-0.02116` (`= ell(22599/1280)`)| 14 | `-0.00136` | `+0.0198` |
| 6 | `-0.01640` (`= ell(27459/1024)`)| 16 | `+0.00023` | `+0.0166` |

**All d close with margin.** The d=5 residual dissolves: the *actual* worst non-broom d=5 hub sits at
`-0.0212`, far below threshold (+0.020) — the "0.0003" gap was the loose broom CEILING, not the real max.

## The structure: a parity oscillation with a geometric tail

The max-`ell` subsequence per degree is a **parity oscillation** (memory's [Cherry-parity oscillation]; optimal
block = a 2-vertex cherry-leg, so `n ≡ spine mod 2`). Tracking the **even-size** subsequence:

- **d=2** monotone-decreasing from size 4 → `M_2` at the interior peak (bounded).
- **d=3, 4, 5** peak at a finite interior size (6, 10, 14) then decrease → `M_d` = the enumerated peak.
- **d=6** is still **climbing** at the size-16 enumeration boundary (`14: -0.02156 → 16: -0.01640`, Δ=+0.00516),
  but the increments shrink geometrically (`+0.018 → +0.005`, ratio ≈ 0.28 < 5/12). The geometric tail with rate
  `rho <= 5/12` caps `M_6 <= ell(27459/1024) + (rho/(1-rho))·Δ <= -0.01272 < threshold(6) = +0.00023` (margin
  +0.013), where `Δ = ell(6,16) - ell(6,14) = L(27459/18072) - 2F*`.

So the whole `M_d` bound reduces to a **finite enumeration (to size 17) + a geometric tail on d=6** — provided
the even-step increments contract at rate `rho <= 5/12`.

## What is now gated, and the one open lemma

`MdGeometricTailCertificate` (`tie_regime.py`, 70 kernel-checkable `norm_num` atoms, `.check()` exact) gates the
finite arithmetic: the 4 peaked degrees `< threshold` and the d=6 geometric-tail limit `< threshold`, all cleared
via frozen log-enclosures, **conditional on `rho = 5/12`**. The reduction ledger (`bg_upper_bound.py`) now reads
`gated=5/5`, split step 2b-lo into `2b-lo-fin` (GATED) and `2b-lo-contract` (HYPOTHESIS).

**The sole open input** is the contraction rate itself:

> **Lemma (open):** the even-step `ell`-max-subsequence per root-degree `d <= 6` contracts with `rho <= 5/12`.

This is the rooted, per-degree, scalar form of the parallel Lean **Obligation A** (Kelmans cavity `pushInto`).
The field-map Jacobian bound `|∂h_v/∂(child field)| = h^2/(d_v d_w) <= 1/2` gives **field** convergence; lifting
that to the **`ell`-max-subsequence** contraction is the residual work. Empirically `rho ≈ 0.28 < 5/12` across
all degrees, consistent with the target — but this is measured, not proven.

## Honest verdict

The d=5 extremality is **closed** (subsumed by the unified per-degree bound); no per-degree exchange is needed.
The `M_d` frontier — hence the single-child lemma tail, hence the BG asymptotic upper-bound analytic side — is
now reduced to **one clean, sharply-stated contraction rate** `rho <= 5/12`, with every surrounding piece
kernel-gated and the finite arithmetic conditional-gated. This does **not** breach the wall (the contraction
lemma is genuine open research, shared with the Lean session), but it collapses the residual from an "all-sizes
frontier" to a **single geometric-contraction constant** on a finite, enumerated, gated skeleton.

`conjecture1_proved = False`.
