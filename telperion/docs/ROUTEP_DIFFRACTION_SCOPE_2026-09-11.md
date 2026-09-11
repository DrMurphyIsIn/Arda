<!-- Scope: connect Route P (rh_iff_companion_ge) to the log-prime diffraction spectrum — the Dyson
quasicrystal reading. The companion coefficient IS a von-Mangoldt (log-prime Bragg) datum; making
that explicit turns Route P's inequality into "log-prime amplitudes ≥ archimedean floor ⟺ RH".
conjecture1_proved = False throughout — this relocates RH onto the prime side, it does not prove it.
Cross-links: RH_CLOSURE_ROUTES_ASSESSMENT_2026-09-10.md, DYSON_QUASICRYSTAL_CERTIFICATES.md. -->

# Route P → the log-prime diffraction reading (Dyson quasicrystal)

## The idea

Route P (#465, `RvMWeierstrass.rh_iff_companion_ge`) is the unconditional, axiom-clean reduction

> `RH ↔ ∀ n, −(1 + (taylorCoeff Γℝ n).re) ≤ (taylorCoeff zetaPoleCompanion n).re`

— the archimedean floor `−(1 + Re taylorCoeff Γℝ n)` is fully explicit (polygamma-at-½ capstone,
#464), so the **companion coefficient is the sole arithmetic carrier**. This scope makes that carrier
*explicit as a log-prime sum*, turning Route P into a **diffraction reading**:

> **RH ⟺ for every `n`, the log-prime (von Mangoldt / Bragg) amplitude of order `n` stays above the
> explicit archimedean floor.**

This is the Route-P instantiation of Dyson's quasicrystal framing (see
`DYSON_QUASICRYSTAL_CERTIFICATES.md`): the Guinand–Weil explicit formula reads the nontrivial zeros as
the *diffraction spectrum* and the prime powers `{log p^k}` as the *dual support* (the Bragg comb).
Route P's companion coefficient is a **moment of the prime-side measure**, so RH becomes a positivity
statement about log-prime amplitudes against a computed archimedean baseline.

## Why the bridge is short — what is already on main

The whole log-prime side is already formalized in `RvMDiffractionCore.lean` (kernel-clean):

- **`logDeriv_zeta_eq_neg_LSeries_vonMangoldt` (Re s>1):** `logDeriv ζ(s) = −Σ Λ(n) n^{−s}` — the Bragg
  spectrum supported on `{log n}` with amplitude `Λ(n)` (nonzero only at prime powers `n = p^k`).
- **`logDeriv_zeta_eq_companion_sub_pole` (#461):** `logDeriv ζ = logDeriv zetaPoleCompanion − pole`.
  Compose: **`logDeriv zetaPoleCompanion(s) = −Σ Λ(n) n^{−s} + pole`** for `Re s > 1` — the companion's
  log-derivative *is* the von Mangoldt prime series plus the (explicit) pole term. The companion is
  entire / pole-regularized (`analyticAt_logDeriv_phi_zetaPoleCompanion`), so its Taylor data is finite.
- **`li_finite_explicit_formula` (#430, `DiffractionCore`):** the finite Li-weighted zero-sum of `ζ`
  `= (horizontal integrals) + (left edge) − (Σ' m, ∫ liWeight n · vonMangoldt term)` — i.e. the finite
  **log-prime Bragg sum for the Li weight is already built**, as a term-level von Mangoldt series on the
  right edge (`right_edge_prime_expansion`, `integral_vonMangoldt_term`).

So both halves exist independently — the companion↔ζ bridge and the ζ↔prime Bragg side. The work is to
**join them at the coefficient level** and expose the diffraction certificate.

## Honest category split (per the closure assessment's honesty theorem)

- **(a) iff-reduction — DONE.** `rh_iff_companion_ge` already relocates RH onto the companion
  coefficient. Making the carrier a prime sum is a *re-coordinatization*, not progress (same wall, new
  coordinate system — cf. §3 of the six-axis assessment).
- **(b) finite Bragg identity — BUILDABLE (this scope).** The companion coefficient equals an
  explicit-formula prime side over a finite contour, with an archimedean residual + Arb-enclosed edges.
  Finite, kernel-checkable, reuses `li_finite_explicit_formula`.
- **(c) RH-hard.** Writing `taylorCoeff zetaPoleCompanion n` as a *convergent* log-prime sum at the Li
  base point needs the explicit formula's contour shift to `Re s = 1/2` and control of the archimedean
  residual uniformly in `n` — the von Mangoldt Dirichlet series diverges at `s = 1`, so the passage from
  the finite (b) identity to a uniform prime-sum lower bound *is* the analytic core of RH. Never crossed
  by finite certificates (Freitas Cor. 4.2; assessment §2.1/2.3 ceiling).

`conjecture1_proved = False`.

## Bricks (dependency-ordered)

- **Brick D1 — the companion log-prime identity (Re s>1).** `logDeriv_zetaPoleCompanion_eq_vonMangoldt`:
  `logDeriv zetaPoleCompanion s = −Σ Λ(n) n^{−s} + (s/(s−1)-pole term)` for `Re s > 1`. A direct
  `rw`-composition of `logDeriv_zeta_eq_companion_sub_pole` + `logDeriv_zeta_eq_neg_LSeries_vonMangoldt`.
  **Near-term, low-risk.** Guard-wire it. This is the clean statement "companion = prime side + pole".
- **Brick D2 — the finite diffraction identity for the companion coefficient.** Specialize
  `li_finite_explicit_formula` and the split `taylorCoeff_riemannXi_split_explicit` (#463) to express the
  *finite-contour* companion contribution of order `n` as `(boundary) − (log-prime Bragg sum)`. Deliver
  `companion_coeff_finite_diffraction`: the finite Bragg identity whose RHS is a manifest
  `Σ_{p^k ≤ N} (log p)-weighted` amplitude sum + a certified-enclosed tail/residual. Category-(b);
  reuses #430 wholesale. The trust seam = the edge zero-avoidance `hnz*` (Arb), identical to #430.
- **Brick D3 — the Dyson-quasicrystal Bragg-amplitude emitter.** A first-class Telperion emitter
  `bragg_floor` (register in `certify.py` + `emitter_sensitivity.py` + negctrl): given `n`, emit the
  finite certificate `Σ_{p^k ≤ N} a_{n}(p^k) − (enclosed tail) ≥ −(1 + Re taylorCoeff Γℝ n)` — the
  truncated log-prime amplitude sum against the explicit archimedean floor — plus a
  `bragg_below_floor_refutes_rh` falsifiability atom (a certified violation refutes RH through Route P).
  Reuses the Li-ladder Arb enclosure backend for the amplitudes/tail and the `UnitModulusSOS` emitter
  (#467) for the on-line square part. Category-(b), consistent-with-RH, falsifiable.
- **Brick D4 (optional, cross-pollination) — the diffraction/inertia bridge.** The on-line paired
  summands are perfect squares (#466) = the `+` directions; the Bragg amplitudes carry the arithmetic.
  Assemble a finite Weil–Gram/Hermitian form from the prime-side amplitudes and run the ported
  `RHLinalg` Sylvester/`posIndex` prelude → the `(1,1)`-signature reading of the diffraction spectrum
  (Bombieri inertia at the Li/prime level). Unifies Route P with the Weil track (assessment §2.3).

## The Dyson quasicrystal connection, precisely

Under Guinand–Weil, `Σ_ρ ĝ(ρ) = (archimedean) − Σ_{n} Λ(n) g(log n)`: the zeros `{γ}` are the spectrum
(Bragg peaks) and `{log p^k}` the almost-periodic support of the dual comb (Meyer / Lev–Olevskii
crystalline-measure picture; Dyson 2009). Route P's `taylorCoeff zetaPoleCompanion n` is the order-`n`
moment of that prime-side comb (Brick D1 makes it literal for `Re s > 1`). Then Route P reads:

> the diffraction spectrum lies on the critical line **⟺** every order-`n` log-prime Bragg moment of the
> companion clears the explicit archimedean floor.

The genuine iff (Kurasov–Sarnak Lee–Yang `N`-valued Fourier quasicrystals) provably does **not** cover
ζ (assessment / Dyson doc), so this stays category-(b) finite-checkable + (c) RH-hard at the uniform
limit — an illuminating coordinate system for the same wall, and a real certificate family, not a
closure.

## Sequencing & acceptance

1. **Brick D1** first (a few `rw`s; ship the "companion = prime side + pole" identity, guard-wired).
2. **Brick D2** (reuse #430; finite Bragg identity for the companion coefficient).
3. **Brick D3** (`bragg_floor` emitter + `bragg_below_floor_refutes_rh`) — the shippable diffraction
   certificate, extending the Li ladder with the explicit archimedean floor.
4. **Brick D4** optional inertia unification.

**Acceptance per brick:** kernel-clean, axioms `{propext, Classical.choice, Quot.sound}`, guard-wired,
no `sorry`; D3 additionally: emit + AXLE statement-match + a forge test (perturb an amplitude/tail →
refused) + negative control. `conjecture1_proved = False` — every brick relocates or finitely-certifies;
none approaches RH.
