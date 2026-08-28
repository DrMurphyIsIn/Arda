# Degree-3 Jensen–Pólya hyperbolicity for the Riemann ξ

The cubic rung above `examples/turan_xi/` (which is the degree-2 case). Certifies
that the **cubic Jensen polynomials** of ξ are hyperbolic (real-rooted) for
shifts n = 0, 1, 2 — a necessary consequence of RH — over imported rational
enclosures, emitted as kernel-checkable Lean.

## The mathematics

RH ⟺ `G(u) = Σ_k a_k u^k` (with `a_k = [z^{2k}] ξ(1/2+z)`) lies in the
**Laguerre–Pólya class** ⟺ every Jensen polynomial of the **EGF sequence**

```
γ_k = k! · a_k
```

is hyperbolic. `J^{d,n}(X) = Σ_{j=0}^d C(d,j) γ_{n+j} X^j`; degree 2 is the Turán
inequality (`turan_xi`), degree 3 is the cubic

```
J^{3,n}(X) = γ_n + 3γ_{n+1} X + 3γ_{n+2} X² + γ_{n+3} X³,
```

hyperbolic ⟺ its discriminant is positive:

```
Δ = 162 g0 g1 g2 g3 + 81 g1² g2² − 108 g0 g2³ − 108 g1³ g3 − 27 g0² g3²   >   0
    (g_i = γ_{n+i}).
```

**Normalization matters, and was fixed empirically.** With `(2k)!·a_k` (the ξ
derivatives) the Jensen polynomials are *not* hyperbolic; with `k!·a_k` they are.
`k!·a_k` is the EGF coefficient sequence of `G`, per the classical
Craven–Csordas/Jensen characterization — the RH-tied one. (Same trap that flipped
the Turán sign; caught the same way, by testing before trusting.)

## What is certified, and how

All `γ_k > 0`, so a **worst-corner** lower bound is an exact rational — positive
monomials at the enclosure floor, negative at the ceiling:

```
Δ_lo = 162 lo0 lo1 lo2 lo3 + 81 lo1² lo2²
       − 108 hi0 hi2³ − 108 hi1³ hi3 − 27 hi0² hi3².
```

`Δ_lo > 0` ⟹ `Δ(γ) ≥ Δ_lo > 0` on the whole box ⟹ `J^{3,n}` hyperbolic. The Lean
bridge `cubic_jensen_pos_of_enclosure` proves `Δ(g) > 0` from the twelve
enclosure hypotheses and the rational margin, bounding each of the five monomials
by a monotone `mul_le_mul` chain and assembling with `nlinarith`. Emitted margins:

| n | shift covers | `Δ_lo` |
|---|--------------|--------|
| 0 | γ₀…γ₃ | `+2.02e-13` |
| 1 | γ₁…γ₄ | `+2.49e-20` |
| 2 | γ₂…γ₅ | `+2.61e-27` |

- `src/telperion/jensen.py` — `CubicJensenCertificate` + `CUBIC_JENSEN_BRIDGE_LEMMA`.
- `compute_gammas.py` — transcendental import (mpmath, two-radius cross-check),
  out of the sympy-only core. `gammas.json` — committed enclosures.
- `generate.py` — `certify → emit → freeze`. `frozen/CubicJensen.lean` — emitted.

## Honest scope (what this is NOT)

1. **Necessary, not sufficient.** Hyperbolicity of all Jensen polynomials *is* RH;
   any finite subset is only implied by it.
2. **Finite.** Shifts n = 0, 1, 2 only. The all-n result (each fixed d) is the
   Griffin–Ono–Rolen–Zagier (2019) theorem, an analytic argument this exact tool
   does not reproduce.
3. **Enclosure-conditional.** The `lo_k, hi_k` are high-precision numerics
   imported as Lean hypotheses, not interval-proven in-kernel.
4. **Not `lake`-built here.** Like `turan_xi`/`zerofree`, the emitted Lean is
   regen- and test-gated, not yet wired into a CI `lake build`. The bridge's
   `mul_le_mul` chains were hand-verified but not machine-checked locally (the
   SoC-watchdog hazard forbids local Lean builds).

Degree 4+ (quartic and higher discriminants) is the natural next rung; the
worst-corner method generalizes, though the discriminants have more sign-varying
monomials.

## Reproduce

```bash
python3 examples/jensen_xi/compute_gammas.py         # regenerate gammas.json (needs mpmath)
python3 examples/jensen_xi/generate.py               # certify -> emit -> freeze
python3 examples/jensen_xi/generate.py --check       # drift check (no mpmath)
pytest tests/test_jensen.py -q                        # exact-rational + hyperbolicity checks
```
