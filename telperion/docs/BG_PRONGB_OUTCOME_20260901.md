# Prong B outcome: the local single-child lemma is the true core; finite part verified, tail is the frontier (2026-09-01)

Executing the `sorted-conjuring-clock` plan's **Prong B** (certify the *local* single-child lemma = HYPOTHESIS
(b), the surviving route after Gate 0 killed the global-dominance Prong A). Outcome: the lemma is verified with a
solid margin and its structure is now fully mapped, but its **tail is the irreducible frontier core** — Prong B
localizes and verifies but does not kernel-gate a complete closure. `conjecture1_proved = False`.

## What Prong B established (exact)

The single-child lemma `ell(c) + μ_k·y_c ≤ V(k)` (`μ_k = 3/(4k+3)`, `y_c = h_c/d_c`, `V = ell(cherry) + μ_k/3`)
— equivalently `mixed ≤ B(k)` — is what closes the asymptotic bound (Gate 0: *local*, not global dominance).
Split by root degree:

- **`d ≥ 7`** — GATED (`HighDegreeTailCertificate`): `x_c` small, ceiling alone.
- **brooms** — GATED (`MixedHubKKTCertificate`): the binding cases (`B(4), B(5)`, the only sub-`0.002`-slack
  branches at the tightest `μ_15`).
- **`d ≤ 6` non-broom** — the residual (b). Reduces (degree-dependent threshold) to `ell(c) < threshold(k,d) =
  ell(cherry) + (d−3)/(d(4k+3))`. Verified: worst `val − V = −0.0216` over all `d≤6` non-broom, all `k∈[2,15]`,
  to size 15. The lemma holds with margin.

**Max `ell` per root-degree is bounded away from the threshold** (the key structural fact):

| d | max non-broom `ell` (exhaustive ≤17 + large families) | `min_k threshold(k,d)` | margin |
|---|---|---|---|
| 2 | `−0.143` | `−0.0532` | `+0.090` |
| 3 | `−0.071` | `−0.0077` | `+0.063` |
| 4 | `−0.040` | `−0.0037` | `+0.036` |
| 5 | `−0.021` | `−0.0014` | `+0.020` |
| 6 | `−0.016` | `+0.0002` | `+0.016` |

So **if** the per-degree bound `max_{d≤6 non-broom} ell ≤ M_d` holds *uniformly over all sizes*, the lemma gates
as a compact per-degree envelope (`M_d < threshold(k,d)`, ~70 rational atoms after clearing `F*` via
enclosures) — no per-branch enumeration.

## The wall (honest)

The uniform per-degree bound `M_d` **is the tail** — and it is the frontier/cavity-contraction problem:

- The cavity field map is a contraction (`|Jacobian| = h²/(d_v d_w) ≤ 1/2 < 1`), so fields converge — but this
  gives field convergence, not directly an `ell` bound.
- The max-`ell` `d≤6` branch is a **small/balanced near-broom** (`ell ≈ −0.016` at `d=6`), NOT the large
  extremal-bulk structures (a big `S(k,5)` rooted at a low-degree vertex is **diluted** to `ell ≈ −0.21`). So
  `M_d` is bounded *by the dilution effect* — the extremal density can't be reached under a bounded-degree root.
- But proving `M_d` uniform is exactly the `(y, ell)`-frontier bound, which `BG_SINGLE_CHILD_FRONTIER_INDUCTION`
  showed has **no simple concave majorant** (the true frontier is recursive/self-similar). A *loose* bound
  (margin `~0.016`) should suffice, but a rigorous one still needs the recursive-frontier / cavity-contraction
  argument — the same wall as the parallel Lean session's Obligation A (the Kelmans cavity `pushInto`), now in
  its rooted, per-degree, scalar-priced form.

## Verdict

Prong B **confirms and sharpens** — it does **not** breach — the core. The asymptotic upper bound is reduced to
**one clean local lemma** (the single-child lemma), verified exhaustively to size 15 + large families with a
per-degree margin `≥ 0.016`, its binding set gated (brooms), its degrees `≥7` gated. The sole residual is the
**uniform per-degree `ell` bound `M_d`** — the rooted frontier / Obligation A. This is genuine open research
(the recursive frontier), not a certification gap that more enumeration closes.

**Net state of the whole BG effort after this plan execution:**
- Gate 0 killed the false Prong A (global `B(c)`-dominance) and reconciled the Lean backbone (sound). ✅
- Prong B localized the true core to the single-child lemma's per-degree tail `M_d`, verified with margin. ✅
- The one open lemma (`M_d` / rooted Obligation A) is shared with the parallel Lean session and is the frontier.
  All arithmetic around it is gated; no smooth certificate can reach it (integrality-gap no-go). The honest next
  target is the recursive-frontier bound for `M_d` (a multi-session research problem, not a next-step gate).

`conjecture1_proved = False`.
