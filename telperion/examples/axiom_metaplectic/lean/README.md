# Axiom metaplectic island

A separate Lean island (v4.35.0-rc3, Mathlib 0493595e) that depends on, and does not vendor, the AxiomMath Lean
library [AxiomMath/DedekindZetaZeroFree](https://github.com/AxiomMath/DedekindZetaZeroFree) at commit 284348a4.
That library (Apache-2.0) is the formalization behind Dean Cureton and Jesse Thorner, "A quasi-Riemann hypothesis for
Dedekind zeta functions" (hexagon:2610.00200v1), developed at Axiom Math with AxiomProver. Copyright in the library
belongs to its authors; nothing from it is copied here.

Why it exists: the RH programme's gate 4 found that every existing automorphic construction reaches ζ through the
trivial, non-tempered representation (constant-term shift d = 1). The library proves, for the cubic cover of GL2,
that the global normalizer is ζ(1 + 6s)/ζ(2 + 6s) (`GlobalZetaNormalizer.exceptionalNormalizer`), a kernel-checked case
of that barrier. It also proves complementary-series positivity for PGL2(ℂ) at the single parameter ν = 1/3. This
island's first project, `CompSeriesPositivity`, generalises that to every ν in (0, 1).

Status: not in CI (the dependency closure is about 5,300 modules). Build locally with a capped job count:

```sh
lake exe cache get
LEAN_NUM_THREADS=8 lake build
```

conjecture1_proved = False. Nothing here is progress on RH.
