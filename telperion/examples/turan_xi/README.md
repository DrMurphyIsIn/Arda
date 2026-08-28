# Turan inequalities for the Riemann xi function

A worked Telperion example applying the exact-rational -> kernel-checked-Lean
pipeline to a **Riemann-Hypothesis-adjacent** inequality family — and an honest
demonstration of exactly where that pipeline stops.

## The mathematics

RH is equivalent to the completed zeta function `xi` lying in the
**Laguerre-Polya class** (uniform limits of real polynomials with only real
zeros). A *necessary* consequence — proved **unconditionally** for `xi` by
Csordas, Norfolk and Varga (1986) — is that the even Taylor coefficients

```
a_k := [z^{2k}] xi(1/2 + z)          (all a_k > 0)
```

satisfy the **Turan (Laguerre) inequalities**

```
a_k^2  >=  a_{k-1} a_{k+1}            for all k >= 1.
```

These hold whether or not RH is true, so verifying them is **not** evidence for
RH; they are a consistency check that any honest RH-toolchain component must
respect.

## What this example certifies

The `a_k` are transcendental, so exact rational arithmetic cannot reach them.
What Telperion certifies is the finite **algebraic** step. Given rational
enclosures `lo_k < a_k < hi_k` (imported — see below), the strict Turan
inequality `a_{k-1} a_{k+1} < a_k^2` holds for every real triple in the
enclosures whenever the worst-corner margin

```
hi_{k-1} * hi_{k+1}  <  lo_k^2
```

is positive — one exact rational inequality (`norm_num`), bridged to the
enclosure hypotheses by the fixed monotonicity lemma `turan_from_enclosure`
(`nlinarith`). Indices **k = 1, 2, 3** are certified; the emitted margins are

| k | `lo_k^2 - hi_{k-1} hi_{k+1}` |
|---|------------------------------|
| 1 | `+7.06e-5` |
| 2 | `+5.68e-9` |
| 3 | `+2.00e-13` |

- `src/telperion/turan.py` — `TuranEnclosureCertificate` (`.check()` exact
  self-check, `.lean()` emitter) and the `TURAN_BRIDGE_LEMMA`.
- `compute_enclosures.py` — the **transcendental import** (mpmath; kept out of
  the sympy-only core). Cauchy-contour Taylor extraction at 60 dps, cross-checked
  at two contour radii to >40 digits, rational windows of width `1e-25`.
- `enclosures.json` — the committed enclosure data.
- `generate.py` — `certify -> emit -> freeze` (with `--check` for drift);
  registered in `telperion.toml` (`quick` group) so it cannot fall out of the
  drift-check net.
- `frozen/RiemannTuran.lean` — the emitted, kernel-checkable file (+ input-hash
  `manifest.json`).

## Honest scope (what this is NOT)

This is deliberately **not** presented as progress toward RH:

1. **Necessary, not sufficient.** The Turan inequalities are implied by RH; they
   do not imply it. Even all of them together (the full Laguerre-Polya
   membership) is the *statement* of RH, not a lever on it.
2. **Finite.** Only k = 1, 2, 3 are certified here. The all-k result is
   CNV 1986 — an analytic theorem this exact-arithmetic tool does not reproduce.
3. **Enclosure-conditional.** The `lo_k, hi_k` are high-precision *numerics*
   imported as Lean hypotheses, not interval-proven inside the kernel. Making
   them rigorous (verified interval arithmetic for `xi` derivatives) is a
   separate, unaddressed step.

The genuine obstruction, stated plainly: RH's content lives in a transcendental,
zeta-zero-dependent quantity with no known uniform-in-k rational certificate.
Telperion can hold the algebraic scaffolding at each fixed k; it cannot
manufacture the analytic all-k bound. A real (non-overclaimed) next step would be
*formalizing* the CNV all-k proof, or the Griffin-Ono-Rolen-Zagier (2019)
hyperbolicity theorem, with Telperion emitting the polynomial-inequality lemmas.

## Reproduce

```bash
python3 examples/turan_xi/compute_enclosures.py        # regenerate enclosures.json (needs mpmath)
python3 examples/turan_xi/compute_enclosures.py --check # enclosure drift check
python3 examples/turan_xi/generate.py                  # certify -> emit -> freeze frozen/RiemannTuran.lean
python3 examples/turan_xi/generate.py --check          # drift check (no mpmath needed)
pytest tests/test_turan.py -q                          # exact-rational self-checks
# lake build (your CI): compiles frozen/RiemannTuran.lean against pinned Mathlib
```
