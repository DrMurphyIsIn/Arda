# bg_smooth_nogo — the integrality-gap no-go (BG upper bound, kernel-gated)

Why *no smooth certificate* can prove the Brualdi–Goldwasser upper bound `F(T) <= F* = log(621/64)/11`.

## The fact

The broom family's per-vertex free energy `f(c) = log(total(c))/(2c+1)` is maximised over **integer** `c` at
`c = 5`, with `f(5) = F*` exactly. Its **continuous** relaxation (real `c`) peaks at `c* ≈ 4.819` with
`f(c*) ≈ 0.20659010 > F* ≈ 0.20658618` — an overshoot of `≈ 3.9·10⁻⁶`. The peak is nearly flat (`f''(5) ≈ −2·10⁻⁴`;
every real `c ∈ [4.06, 5.87]` is within `10⁻⁴` of the max), so `c = 4, 5, 6` are near-degenerate.

**Consequence (no-go).** Any certificate that relaxes the integer arm-count — convex, SOS, moment/Lasserre,
tangent/concavity, spectral: *everything smooth* — is bounded below by `f(c*) > F*`, so it **cannot** certify
`F(T) <= F*`. This is exactly why every smooth bound in this campaign landed `~10⁻⁴` loose. The BG optimum is an
**integer-program** optimum (rational value `621/64`, prime `4·5+3 = 23`, `621 = 27·23`) with a *positive
integrality gap*; the closing argument must be **arithmetic** (exact on integer `c`).

## What is gated

`SmoothNoGoCertificate` (`telperion.spider_broom`) emits a single `norm_num` atom proving `f(24/5) > F*` (a
rational witness above `F*`). Clearing `× 11 × 53`:

```
209·L(3/2) + 55·L(111/5) − 55·L(2) − 55·L(29/5)  >  53·L(621/64),
```

LHS lower-bounded, RHS upper-bounded by frozen log-enclosures (`log(p/q) ∈ [lo,hi]`, floor/ceil at 60-digit
precision); margin `≈ 2.3·10⁻³`.

```
python examples/bg_smooth_nogo/generate.py [--check]
```
CI job `bg-smooth-nogo-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake build`s it.

## Role

This gates the *obstruction*, not the bound: it proves the problem is genuinely arithmetic, guarding against a
whole class of smooth proof attempts (and explaining the campaign's caught overclaims). `conjecture1_proved =
False`.
