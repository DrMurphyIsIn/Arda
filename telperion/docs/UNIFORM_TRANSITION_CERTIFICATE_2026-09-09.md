# The Height-Uniform Transition Certificate: What Exists, What Cannot, and the Second Axis

**Prompt.** "Find a height-uniform transition certificate" — a fixed finite rule + kernel theorem
certifying band `[T_k, T_{k+1}]` from band `k`'s certificate, uniformly in `k`, so the tiled
ladder completes to all heights.

**Answer in three parts.** (1) A *complete* height-uniform transition certificate is
foundation-equivalent to RH — provably, not rhetorically. (2) *Partial* height-uniform
certificates exist; we already possess the strongest unconditional one in kernel-verified form,
and its **width** is the honest progress metric for the whole subject. (3) Every known
reformulation of RH migrates the height-quantifier into another ladder whose rungs are finite and
certificate-shaped — which defines a **second axis** for this program, orthogonal to the T-ladder,
and the emitters for it landed on main this week.

`conjecture1_proved = False` throughout.

---

## 1. The equivalence (the honesty theorem)

Call a *transition certificate* a Lean-checkable predicate `R` on bands with per-band data `D_k`,
a kernel theorem `R(D_k) ⟹ all zeros in band k lie on Re = 1/2`, and — the uniformity clause — a
single algorithm producing `D_k` for all `k` with a single kernel proof of its correctness `∀k`.

*If such an `R` exists, RH is a theorem*: instantiate at every `k` and union over bands (our
`rh_box_of_bands` is literally this union, kernel-checked). *If RH is a theorem, such an `R`
exists trivially* (`D_k` empty; `R` = the RH theorem restricted to the band). So:

> **A complete height-uniform transition certificate exists iff RH is provable in the ambient
> foundation.** It is the conjecture in certificate clothing.

Two sharpenings worth recording:

* **RH is Π₁** (Davis–Matiyasevich–Robinson; concretely e.g. Lagarias' elementary form). Hence:
  if RH is *false*, some **finite** band certificate must fail — our ladder is a
  *refutation-complete verifier*: it would discover the counterexample at a finite height, with a
  kernel-checked witness. If RH is *true*, the ladder succeeds forever without ever completing —
  the exact phenomenology of a true Π₁ statement awaiting an idea. The T-ladder is therefore not
  merely evidence-gathering; it is one half of a decision procedure whose other half is the open
  problem.
* **The structural obstruction is not ignorance but a theorem**: Voronin universality makes the
  vertical flow in the strip dense in an infinite-dimensional function space — no finite tile
  alphabet, no finite-type symbolic coding, no Markov transition rule can capture the band data.
  Any candidate `R` must smuggle its infinite content somewhere; universality says "somewhere"
  cannot be a finite alphabet over heights.

## 2. Partial uniform certificates: we hold the record, and width is the metric

A *partial* height-uniform certificate certifies, for **all** heights at once, something weaker
than "all zeros on the line." These exist — and one measures them by **how much of the strip they
certify**:

| Certificate | Certifies (∀ heights, one proof) | Status |
|---|---|---|
| Zero-free region (dVP) | no zeros in `Re > 1 − c/log|γ|` | **KERNEL-VERIFIED HERE** (`riemannZeta_ne_zero_region`, effective `c = dlvpRateC`) — to our knowledge the only unconditional one at kernel level |
| Zero-free region (Vinogradov–Korobov) | width `~ (log|γ|)^{−2/3}(log log)^{−1/3}` | classical (1958); formalization blocked on the Vinogradov mean value theorem / decoupling — a monumental but *defined* target |
| Zero-density estimates | few zeros off-line (quantified) | classical; formalizable with our BC/Jensen kit |
| Bohr–Landau | almost all zeros within `ε` of the line | classical; same kit |
| Levinson–Conrey | ≥ 40% of zeros ON the line | classical; hard formalization (mollifiers + asymptotic moments) |

The first row answers the prompt literally: **`riemannZeta_ne_zero_region` IS a height-uniform
transition certificate** — one theorem, no per-height data, certifying a sliver of the strip at
every height simultaneously. The entire history of the subject since 1896 is the attempt to widen
that certified sliver; it has been stalled at Vinogradov–Korobov since 1958; RH is the demand that
the sliver reach `Re = 1/2`. In this currency our program has: built the kernel-verified record
holder (dVP), and correctly declined the next widening (VK) as mis-priced for now.

## 3. Quantifier migration: every reformulation is another ladder

Each classical "uniform" reformulation of RH trades `∀ heights` for `∀ (something else)` — and in
every case the individual rung is **finite and certificate-shaped** while the limit is RH:

* **Weil positivity.** RH ⟺ the explicit-formula quadratic form `W(g)` is ≥ 0 for all admissible
  test functions. Each `W(g)` evaluation is a *finite prime-side computation* (compactly supported
  `g` ⟹ finite sum over primes + archimedean term). A positivity certificate on an
  `n`-dimensional test-function subspace is a **finite Gram-matrix PSD check** — and it constrains
  the zeros at *all heights at once*. Suitable localized `g` recover zero-free statements: finite
  Weil certificates can *re-derive* our low-strip clearing from prime data alone, no ζ-enclosures.
* **Jensen/Turán hyperbolicity (Griffin–Ono–Rolen–Zagier).** RH ⟺ all Jensen polynomials
  `J^{d,n}` of `ξ` are hyperbolic. Fixed degree `d`, all shifts `n`: proven for `d ≤ 8` — these
  are *actual, existing, height-uniform partial certificates* of a different species. The ladder
  is now in `d`. (This repo already carries a hyperbolicity-ladder module family.)
* **Nyman–Beurling/Báez-Duarte.** RH ⟺ `d_n → 0`, where `d_n²` is the distance from the
  indicator to the span of `n` dilations in `L²` — each `d_n²` a **finite quadratic form** with
  explicit Gram entries (Vasyunin cotangent sums). The ladder is in `n`; every rung is exact
  linear algebra.
* **Hilbert–Pólya.** A self-adjoint operator with spectrum = zeros would be the terminal uniform
  certificate (self-adjointness: one statement, all heights). Open; the operator is not known.

**The migration theorem-shape**: the infinite quantifier never disappears; it changes coordinates.
Universality (heights), degree-exhaustion (Jensen), cone-exhaustion (Weil), basis-exhaustion (BD)
are the same wall in four coordinate systems. What *changes* is the cost and information profile
of a rung.

## 4. The strategic consequence: a second axis

The T-ladder gives **complete knowledge below a height** (everything, up to `T`). The migrated
ladders give **partial knowledge at all heights** (a constraint, everywhere). These are orthogonal
and multiply:

```
             all heights ↑   Weil/BD/Jensen rungs (partial, uniform)
                          │  ┌──────────────────────────────
   certified knowledge →  │  │   the program's rectangle
                          │  │   grows in BOTH directions;
                          │  │   RH is the double limit
                          └──┴────────────────────→ height T (complete, bounded)
                              T-ladder rungs
```

**Convergence note (this week):** PR #326 landed `HermitianMoment` emitters + the `RHLinalg`
prelude — finite Hermitian/Gram positivity certificates are *exactly* the rung shape of the
Weil and Báez-Duarte ladders. The second axis's emitter tooling exists before the campaign does.
(Cf. also the standing memory that the RH and BG endgames share one box-positivity/SOS engine.)

**Proposed milestone W1 (second axis, first rung):** a kernel-verified explicit-formula instance —
one admissible test function `g`, the identity `Σ_ρ ĝ(ρ) = (prime sum) + (archimedean term)` with
every side effectively enclosed, emitted as a certificate; then the first Gram-PSD rung on a small
explicit family. Deliverable value: the first *prime-side* constraint on all zeros at all heights
in kernel form, and independent cross-validation of the T-ladder's Arb inputs from arithmetic data.
(Milestone W0, cheaper: the Báez-Duarte `d_n²` for small `n` via Vasyunin sums as a
HermitianMoment-emitter exercise.)

## 5. Summary

* Found: `riemannZeta_ne_zero_region` — the height-uniform transition certificate that exists,
  kernel-verified, effective, ours. Its width `c/log T` is the honest measure of humanity's
  progress on this question, and the kernel now holds it.
* Proven impossible to complete cheaply: a full-width uniform certificate ⟺ RH provable; the
  wall is a theorem (universality), not a tooling gap; and the wall reappears in every coordinate
  system (quantifier migration).
* Actionable: open the second axis (Weil/Báez-Duarte rungs — finite, prime-side, Gram-shaped,
  emitter-ready), keep raising the first (T-ladder), keep widening the sliver (VK when the
  decoupling formalization economy changes). The rectangle grows; the double limit is the prize.

`conjecture1_proved = False` — and this document is precise about why that line is load-bearing.

## 6. Addendum: the aperiodic-tiling question (Dyson's axis)

**Q (operator).** Universality kills *periodic/finite-Markov* tilings of the strip — but aperiodic
tilings (Penrose, Wang, the 2023 hat monotile) are generated by FINITE local rules without any
period. Could the zeta structure admit an *aperiodic* tiling?

**A.** For the *function strip*: no — and the reason is sharp. Aperiodic tilings evade
periodicity but keep **finite local complexity and repetitivity** (every patch recurs; zero
entropy; that is *why* finite matching rules can force them). Voronin universality gives the
strip the *opposite* profile: every admissible patch from an infinite-dimensional space occurs —
maximal complexity, no finite prototile set, not even in the aperiodic sense. The hat tile lives
at zero entropy; the strip lives at infinity.

For the *zero set on the line*: **yes — conjecturally, and this is a famous serious program.**
Under RH, the explicit formula says the measure `Σ_γ δ_γ` has Fourier transform supported on
`{± k log p} ∪ {0}` — Bragg peaks at the logarithms of prime powers. That makes the zeros a
**crystalline measure / Fourier quasicrystal**: a pure-point-diffractive aperiodic point set —
precisely the mathematical home of Penrose-type aperiodic order (quasicrystal diffraction).
Dyson (2009) proposed exactly this route: *classify one-dimensional quasicrystals; find zeta's
zeros in the classification; win RH.* The migration theorem of §3 applies — "find the tiling"
is the conjecture in aperiodic-order clothing — but the quantifier lands in genuinely different
technology:

* Kurasov–Sarnak (2020) construct 1D Fourier quasicrystals from **Lee–Yang (stable) polynomials**
  on torus lines; subsequent work (Alon–Cohen–Vinzant) shows this is essentially the only 1D
  mechanism. If the zeros are an FQ of this type, the generating object is an infinite-dimensional
  Lee–Yang structure — a Hilbert–Pólya-adjacent reality constraint. *This repo already owns
  Lee–Yang/stable-polynomial certificate emitters (the BG program's box-positivity engine) — the
  cross-pollination standing order points directly at this.*
* Provable limits of the analogy, honestly: the raw ordinates are NOT a Meyer set or
  finite-local-complexity tiling (gaps shrink like `2π/log T` — not uniformly discrete;
  `S(T)` is unbounded — discrepancy too wild for model sets; local statistics are GUE —
  absolutely continuous pair correlation, unlike substitution tilings). The quasicrystal
  structure, if real, lives at the level of the *weighted diffraction measure*, not a
  bounded-complexity tiling.
* **Convergence with §4:** the diffraction identity IS the Weil explicit formula. Verifying Bragg
  peaks against prime data for concrete test functions is *the same computation* as milestone W1.
  Dyson's diffraction axis and the Weil-positivity axis are one program in two languages — so the
  second axis serves both.

**The clean dichotomy this reveals**: the strip is maximally wild (universal — no tiling of any
kind); the critical line is conjecturally maximally rigid (a quasicrystal). **RH is exactly the
statement that all of zeta's rigidity concentrates on the line.** The T-ladder certifies the
rigidity band-by-band; the Weil/diffraction rungs certify Bragg peaks arithmetic-side; the
zero-free region pins the wildness away from `Re = 1`.
