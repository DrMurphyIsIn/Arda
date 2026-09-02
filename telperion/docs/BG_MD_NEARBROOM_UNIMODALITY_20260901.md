# The M_d tail is unimodal, not a contraction — ρ≤5/12 was wrong; the frontier is now extremality alone (2026-09-01)

Follow-up to `BG_MD_GEOMETRIC_TAIL_20260901`, correcting its central claim. Taking the user's directive to
*solve* the "ρ ≤ 5/12" frontier, the honest outcome is: **there is no contraction rate to prove.** The object I
called an "even-step contraction" is the increment of an explicit one-parameter family, and that family is
**unimodal with a finite peak** — now proved UNCONDITIONALLY. The M_d frontier reduces to **extremality alone**.
`conjecture1_proved = False`.

## The correction

`BG_MD_GEOMETRIC_TAIL` claimed d=6's max-`ell` was "still climbing at the size-16 boundary" and needed a
geometric tail with rate `ρ ≤ 5/12`. That was an artifact of enumerating only to size 17. Computing the actual
one-parameter family — `NB(d,m)` = "(d−2) cherries + one sub-broom `B(m)`", root-degree d — to arbitrary m shows:

| d | m* (peak) | peak size | `ell(d,m*)` | behavior for m > m* |
|---|---|---|---|---|
| 2 | 1 | 4  | −0.0726 | strictly decreasing |
| 3 | 1 | 6  | −0.0481 | strictly decreasing |
| 4 | 2 | 10 | −0.0324 | strictly decreasing |
| 5 | 3 | 14 | −0.0212 | strictly decreasing |
| 6 | 3 | 16 | −0.0164 | strictly decreasing (m=4 already −0.0165 < −0.0164) |

The family **peaks at `m* = max(1, d−3)` then decreases *linearly*** (increments → `ELL_CH = log(3/2)−2F* < 0`).
It moves **away** from threshold, not toward it. So `M_d` is the finite peak — no infinite tail, no rate.

## The unimodality, proved (pure rational, F* cleared)

The increment `Δ(d,m) = ell(d,m+1) − ell(d,m)` clears exactly (the 11th power kills `F* = log(621/64)/11`):

> `Δ(d,m) < 0  ⟺  BIG(d,m)^11 < (621/64)^2`,  where
> `BIG(d,m) = (3/2)·(4m+7)(m+1)/((m+2)(4m+3))·(d+s(m+1))/(d+s(m))`,  `s(m) = (d−2)/3 + 3/(4m+3)`  — a rational function.

No log-enclosures. `NearBroomUnimodalityCertificate` (17 pure-rational `norm_num` atoms) gates:

- **Peak** (d=2..6): `BIG(d,m*)^11 < (621/64)^2` — margins fat except razor-thin-but-**strictly positive** at
  d=4,6 (0.07 in the `^11` scale). This is the tie-adjacency (the peak near-broom is close to the k=5 tie).
- **Peak-location** (d=4,5,6): `BIG(d,m*−1)^11 > (621/64)^2` — the peak is exactly `m*`.
- **Monotone tail** (d=3,4,5,6): the numerator of `BIG(d,m*+t) − BIG(d,m*+t+1)`, as a polynomial in `t = m−m* ≥ 0`,
  is `c₁t + c₀` with `c₁,c₀ > 0` (e.g. d=6: `6864t + 33813`) — a **degree-1 Handelman certificate on the ray**, so
  `BIG` is strictly decreasing for all `m ≥ m*`, hence `Δ(d,m) < 0` for all `m ≥ m*`.
- **d=2 tail**: `BIG(2,m) < 3/2` for all m — which reduces algebraically to `1/(m+1) < 12/(8m+9) ⟺ 4m+3 > 0`
  (always) — and `(3/2)^11 < (621/64)^2`.

Assembly: `BIG(d,m) < (621/64)^{2/11}` for all `m ≥ m*` ⟹ `ell(d,m) ≤ ell(d,m*)` ⟹ `M_d(near-broom) = ell(d,m*) <
threshold(d)`, **unconditionally**. (This is the same 11th-root-clearing + ratio-unimodality shape as the earlier
`near_star_arithmetic_proof`; the near-broom is its natural generalization, sub-broom in place of cherry-arms.)

## What remains: extremality (a combinatorial lemma, not a rate)

The one open input of the M_d frontier is now purely: **the near-broom is the argmax `ell` over ALL non-broom
root-degree-d branches** (not merely within the near-broom family). Adversarially checked — two-broom
(`3 cherries + B(m₁) + B(m₂)`) and deep-nested competitors all sit `≥ +0.017` below the near-broom peak. This is
a single-child / interchange statement (cherries maximize the per-child value; the best non-cherry child is a
broom), with a fat margin — genuinely combinatorial, and **not** the analytic contraction I had feared.

## Ledger

`bg_upper_bound.py`: `gated = 6/6`. Step `2b-lo` now splits into `2b-lo-fin` (GATED, MdGeometricTail peak
arithmetic), `2b-lo-unimodal` (GATED, NearBroomUnimodality — the tail, now unconditional), and
`2b-lo-extremality` (the sole HYPOTHESIS). `conjecture1_proved = False`.

## Verdict

The "ρ ≤ 5/12 contraction" frontier **dissolved**: it was a one-parameter unimodality, now proved. The residual
is the extremality — a combinatorial single-child lemma with a comfortable margin, sharply separated from any
transcendental analysis. `conjecture1_proved = False`.
