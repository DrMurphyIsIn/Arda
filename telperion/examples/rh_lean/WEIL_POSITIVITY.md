# The PSD certifier pointed at the Weil form — a new angle for our tooling

> **Honest scope, up front.** Finite-basis Weil positivity is a NECESSARY condition for RH
> (RH ⟹ the Weil form is PSD, always). Verifying it is *consistent with* RH, never a proof.
> This is a genuinely new *angle* — the natural home for a PSD/SOS certificate, and RH-*equivalent*
> via Weil's criterion — not progress toward *proving* RH. `conjecture1_proved` stays False.

## The idea (challenging our own assumption)

Our earlier zeta-frontier work put the certifier on the **zero-free-region line**, where a nonneg
trig polynomial is only a small cog that still needs an (unformalized) analytic growth bound. That is
the wrong home. The natural home for a *positivity* certificate is where RH **is** a positivity
statement:

**Weil's criterion.** RH ⟺ the Weil quadratic functional `W(g, g) ≥ 0` for all test functions g
(Weil; Bombieri; Connes). On a finite test-function basis `{g_1, …, g_N}` it is a symmetric Gram
matrix
```
    M_{jk} = W(g_j, g_k) = Σ_ρ  ĝ_j(γ_ρ) ĝ_k(γ_ρ),
```
a Gram matrix of the vectors `(ĝ_j(γ))_γ` — hence **positive-definite exactly when the zeros γ are
real, i.e. RH.** Crucially, the entries `M_{jk}` are given by the **explicit formula** (archimedean
`Γ'/Γ` = digamma terms + a prime sum + boundary terms) and are computed **without any knowledge of the
zeros.** So "M positive-definite on a finite basis" is a necessary RH condition checkable from the
arithmetic/archimedean side alone — and certifying a symmetric matrix is PD is exactly our
`WorstCorner`/leading-minor machinery (built this session for Jensen/Hankel).

## What was done (verified)

1. **The Weil explicit formula was implemented and cross-checked** against the actual ζ zeros: for a
   Gaussian test function, `Σ_γ h(γ)` (over the first ~120 zeros) equals `boundary − g(0)logπ +
   (1/2π)∫h(r)Re ψ(1/4+ir/2)dr − 2Σ_n Λ(n)n^{-1/2} g(log n)` to 26 digits. (Same two-way-check
   discipline as the a_k enclosures.)
2. **The finite Weil-Gram matrix M** (Gaussian basis, widths reaching the zeros) was computed from the
   explicit formula (no zeros used). Its leading principal minors are all positive
   (`D_1..D_4 = 2.11, 0.60, 0.033, 0.00195 > 0`) → **M is positive-definite, consistent with RH.**
3. **`WeilPositivityCertificate`** (`src/telperion/weil_positivity.py`, `RH/WeilPositivity.lean`)
   consumes rational brackets on the entries and certifies, by Sylvester, that every symmetric matrix
   in the box is PD — each leading minor `D_r > 0` via `WorstCornerCertificate`. The **3-dim** form is
   kernel-verified (`D_1, D_2, D_3 > 0` at entry brackets ±1e-5).

## Honest limits

- **Necessary, not sufficient** — same ceiling as Robin/Jensen. A new angle, not RH progress.
- **Entry brackets are imported.** The rigorous rational bounds on `M_{jk}` (the digamma integral +
  prime sum) are the transcendental import, analogous to the a_k enclosures — here computed to high
  precision and bracketed; a fully in-kernel entry proof would need rigorous digamma numerics
  (`Complex.digamma` exists in Mathlib; rigorous integration is the missing piece).
- **Conditioning caps the basis size.** The Gaussian Weil-Gram matrix is ill-conditioned
  (`D_4 ≈ 2e-3`), so naive determinant-minor worst-corner tops out around 3×3 at ±1e-5 brackets; larger
  bases need a better-conditioned test basis or an LDL/SOS certificate (tighter than the raw minors).

## Why this is the right "next step" (and what it is not)

It is the natural, RH-*equivalent* home for our PSD/SOS certificate technology, reusing the very machinery
we built for Jensen hyperbolicity on a genuinely different target. Kernel-exact certification of Weil
positivity on test spaces is real, new rigorous-computation work (nobody has done it in a proof
assistant) — in the same honest category as the de Bruijn–Newman Λ-narrowing: rigorous, RH-adjacent, and
**not a proof of RH.** The infinite/finite barrier is untouched.
