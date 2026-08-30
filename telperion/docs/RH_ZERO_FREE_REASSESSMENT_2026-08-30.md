# Reassessment of the whole zero_free_bridge proof (with the degree-n + hinge + Fejér findings)

**Date:** 2026-08-30. `conjecture1_proved = False`. A clear-eyed re-appraisal of the entire
`zero_free_bridge` formalization in light of this session's findings — what is proven, what it reaches,
and exactly where and why it stops.

## 1. What is now proven (kernel-green, gap-free)

20 theorems, `telperion-lean-e2e` green, and **zero `sorry` / `admit` / `axiom` / `Prop := True`** — a
genuinely gap-free formalization (unlike stubbed "green" builds). The complete arc:

- **Positivity core** — `mertens_three_four_one` (`3+4cos+cos2 ≥ 0`) carried onto the actual `−ζ'/ζ`
  Dirichlet series: `zeta_logDeriv_comb_nonneg` (`σ>1`), via `cpow_re` → `term_re` → sum.
- **`residue_logDeriv`** — a genuine Mathlib v4.32.0 gap-filler (order = residue of `logDeriv`, general
  order; library had only the simple-zero case). Reusable, not RH-specific.
- **`zeta_boundary_contradiction`** — de la Vallée Poussin core: `ζ(1+it) ≠ 0` via the `−ζ'/ζ` route.
- **Improved degree-3 cert** — `mertens_improved` (`20+30cos+12cos2+2cos3 = 8(1+cos)³ ≥ 0`) onto `−ζ'/ζ`
  (`zeta_logDeriv_comb4_nonneg`); the Mossinghoff–Trudgian direction.
- **General degree-n cone** — `cosine_comb_zeta_nonneg`: ANY pointwise-nonnegative cosine polynomial of
  any degree gives the `−ζ'/ζ` positivity. Subsumes all the above + the whole `2ⁿ(1+cos)ⁿ` family.
- **The hinge** — `admissible_boundary_contradiction`: any admissible certificate (`aₖ≥0`, pointwise
  nonneg, and `a₀ < a₁`) forces `ζ(1+it) ≠ 0`. `a₀ < a₁` is the *exact* condition.

This is a faithful, complete, in-kernel formalization of the classical nonnegative-cosine-polynomial
zero-free-region *positivity program* and its boundary conclusion.

## 2. What the new findings say about its REACH (the sharp part)

Three findings compose into a hard verdict on the whole method:

1. **The hinge is `a₁ > a₀`** (proven, `admissible_boundary_contradiction`): the boundary needs exactly
   the pole residue `+a₀` to lose to a zero residue `−a₁·m` (m≥1).
2. **Fejér caps `a₁ < 2 a₀`** for *any* nonnegative cosine polynomial. So the zero-free functional
   `F(P) = (√a₁−√a₀)²/Σ_{k≥1}aₖ` — hence the region constant `c` — has a **finite ceiling** (the
   Mossinghoff–Trudgian optimum, `R₀ = 5.573412`). No cosine-polynomial cert beats it.
3. **The horizon collapses.** The region is `σ > 1 − c/log|t|`. With `c` capped, the edge → 1 as |t|→∞:

   | height \|t\| | best σ (MT-optimal edge) | gap to critical line ½ |
   |---|---|---|
   | 10² | 0.96104 | 0.461 |
   | 10¹² | 0.99351 | 0.494 |
   | 10¹⁰⁰ | 0.99922 | 0.499 |

   The region hugs σ=1 and **collapses onto it** at large height. It never reaches any fixed σ<1, let
   alone ½.

**Verdict on reach:** the entire certificate program — the whole cone, optimized to its Fejér ceiling —
is provably confined to `1 − O(1)/log|t|`, **infinitely far from RH**. Improving the certificate
(degree-n, MT-optimal) only rescales the constant `c`; the `1/log|t|` *shape* is intrinsic and capped.
**The gap to RH is the shape (rate), not the constant.** This is a provable ceiling of the *method*, not a
limitation of the formalization.

## 3. Unification with the marginality picture (digs 1–4)

The certificate is a **fixed, height-independent object**. RH is `Λ = 0` (de Bruijn–Newman) — a
**height-indexed marginal** problem whose ties (Lehmer pairs) sharpen without bound as height grows
(dig #2–3). A height-blind certificate cannot control ties at every height, so the zero-free region
collapses *precisely where the ties sharpen* (large |t|). The certificate horizon and RH's marginality
are the **same phenomenon from two sides**: the certificate improves a *constant* and is blind to height;
RH requires the *arithmetic at every scale*. The proven bottleneck (dig #3, corrected) — the
zero-free-region constant — is exactly what this program optimizes, and exactly where it stops.

## 4. Honest value of the whole proof

- **NOT progress toward RH** — and never claimed to be (`conjecture1_proved = False` throughout).
- **A complete, reusable, in-kernel formalization** of the certificate program's positivity + boundary
  machinery. `cosine_comb_zeta_nonneg` (general cone) and `residue_logDeriv` (Mathlib gap-filler) are
  genuinely reusable beyond this example.
- **A precise localization of the RH gap.** The certificate reaches its Fejér ceiling and stops at
  `1 − O(1)/log|t|`; RH lives beyond, in the height-dependent rate/shape, which is intrinsically
  *not* certificate-shaped (Vinogradov–Korobov / arithmetic-at-every-scale technology, per digs #3–4).
- **The method meta-result.** Six bold RH attempts + four digs + this build, each verified or refuted on
  its own controls, converge on a sharp, honest statement of where the certificate method ends and why —
  which is the deliverable. Not a proof; a map with its edges proven.

## 5b. Dig deeper — CORRECTION: the mechanism is MAGNITUDE, not "positivity recursion"

§2–4 asserted the gap to RH is "the rate/shape, non-certificate-shaped." That was right on the outcome
but I tried to sharpen the *mechanism* as "finite positivity vs scale-recursive positivity" — and a
hostile expert refuted that as a **category error** (sourced: Tenenbaum II.5; Montgomery–Vaughan 11.1;
Iwaniec–Kowalski 5.5; Bourgain–Demeter–Guth 2016; Wooley 2018). The correct structure of Vinogradov–Korobov
is **three separate layers**:

1. **Finite positivity (the 3-4-1 / cosine-polynomial inequality)** — *UNCHANGED* between the classical
   region and VK. Both use the *same* positivity. This is the layer `zero_free_bridge` formalizes and
   optimizes (to the Fejér ceiling).
2. **Magnitude bound `|ζ(σ+it)|` in the critical strip** — the layer VK *improves*, via Vinogradov's mean
   value theorem / exponential sums (Weyl differencing, ℓ²-decoupling, Wooley efficient congruencing). These
   are scale-recursive and *positivity-flavored* (`|S|² ≥ 0` autocorrelation; ℓ² orthogonality) but are
   **iterated Cauchy–Schwarz / induction-on-scales, NOT finite SOS certificates**, and they bound a
   **magnitude**, not the positivity of a Dirichlet series.
3. **Hadamard / Borel–Carathéodory extraction** — turns the magnitude bound into the zero-free region.

So the honest dichotomy is **finite positivity (shared, Fejér-capped) vs scale-recursive MAGNITUDE bound
(the actual lever)** — not "positivity vs recursed-positivity." Calling Weyl/decoupling "positivity" or
"certificates" overclaims: they use squares, but they are not SOS witnesses.

**This STRENGTHENS the no-go.** The certificate program optimizes Layer 1 — but Layer 1 is *shared with VK
and already at its ceiling*, so it was never the bottleneck. The entire reach beyond `1−O(1)/log|t|` is
gated by Layer 2, the magnitude bound on `|ζ|`, which is a *different object* the positivity certificate
does not touch at all. "Improve the certificate" is therefore provably the wrong lever: it refines an
already-shared, already-capped layer while the actual frontier (the `|ζ|` bound) sits in a layer with no
finite-certificate structure. The `1/log|t|` → `1/(log t)^{2/3}` shape improvement is *entirely* Layer 2.
(My "positivity recursion" framing is retracted; adversarial verification caught it.)

## 5c. Dig deeper again — is the MAGNITUDE layer itself certificate-shaped? (mostly no, and a 2nd overclaim caught)

§5b said the magnitude layer "carries no finite-certificate structure." I challenged that too, proposing
**van der Corput exponent pairs** (finite words in the A/B processes) as a certificate-like foothold reaching
**Littlewood's** region. A hostile expert (Titchmarsh 1986; Tenenbaum–Iwaniec; Graham–Korolev 2014;
Karatsuba–Voronin 1992) split the verdict:

- **CONFIRMED:** exponent pairs *are* a discrete, recursively-verifiable structure — a finitely-generated
  A/B monoid; membership is mechanically checkable.
- **RETRACTED (overclaim #2):** calling them "certificates" repeats the previous error. Each A/B step is an
  **analytic inequality** (Weyl differencing / Cauchy–Schwarz / Poisson summation), *not* an algebraic
  identity. They are **discrete bookkeeping over analytic operations**, not algebraic SOS certificates.
- **RETRACTED:** "exponent pairs reach Littlewood's `loglog t/log t`." Unsourced and likely wrong —
  Littlewood (1922) used independent zero-density machinery; exponent-pair bounds on `|ζ|` are weaker, and
  the intermediate exponent-pair zero-free region for ζ is *not standardly named*. The A/B semigroup is also
  **infinite**, and optimal-pair selection is application-dependent, not one finite optimization.
- **CONFIRMED:** the full VK `(log)^{2/3}` region genuinely needs Vinogradov's mean value theorem
  (scale-recursive), beyond direct exponent-pair application.

**Net, honestly:** the magnitude layer *does* contain discrete structure (exponent pairs), so "no finite
structure at all" was too strong — but that structure is **analytic-operation bookkeeping, not algebraic
SOS**, and its precise reach is not what I claimed. This actually *sharpens the Telperion-relevant line*: the
horizon for **algebraic SOS / kernel certificates** (what Telperion and `zero_free_bridge` produce) is
exactly the **positivity layer** (Fejér-capped). Everything past it — even the discrete exponent-pair layer —
is *analytic*, not algebraically certifiable, and VK proper is scale-recursive. Two consecutive bold
sharpenings, two overclaims caught by adversarial verification: the true statement is more modest and more
precise than either attempt.

## 6. Final consolidated reassessment (three convergent verifications)

The reassessment (§2–4) and two adversarial digs (§5b, §5c) now converge on one picture — and the honest
"next step," after two overclaims caught, is to consolidate it rather than propose a third bold sharpening
(the pattern says that would be a third overclaim; the discipline is to stop calling analytic methods
"certificates" once three independent checks agree they are not).

**(i) The positivity-layer formalization is COMPLETE and its limits are EXACTLY characterized.**
`zero_free_bridge` no longer formalizes one polynomial — `cosine_comb_zeta_nonneg` is the *whole nonnegative
cosine cone* on `−ζ'/ζ` (any pointwise-nonneg cosine polynomial, any degree). Its boundary reach is pinned by
two exact inequalities, both now in-kernel or classical: the hinge `a₀ < a₁` (`admissible_boundary_contradiction`,
necessary and sufficient for the residue sign-flip) and the Fejér ceiling `a₁ < 2 a₀` (the cone's cap). So the
positivity layer is bracketed exactly: **`a₀ < a₁ < 2 a₀`**. There is nothing left to build in this layer — it
is closed, kernel-checked (20 theorems, no `sorry`/`axiom`/stub), and capped.

**(ii) This layer is load-bearing but not the frontier.** It is *shared* with Vinogradov–Korobov (VK reuses
the same 3-4-1 positivity unchanged) — so the formalization captures a genuine, universal component of every
zero-free-region proof, not a toy. But its contribution is a *bounded constant* within a fixed `1/log|t|`
shape; the shape (hence every region improvement, up to and including whatever RH would need) lives entirely
in **Layer 2, the magnitude bound `|ζ(σ+it)|`**.

**(iii) The frontier beyond is ANALYTIC, not algebraically certifiable.** Layer 2 has discrete structure in
places (van der Corput exponent pairs — a finitely-generated A/B monoid) but it is *analytic-operation
bookkeeping*, and VK proper is scale-recursive (Vinogradov mean value theorem). Neither is a finite algebraic
SOS certificate. Three independent verifications (this reassessment + two hostile digs) agree: the horizon for
**algebraic / kernel-checkable certificates** — Telperion's and `zero_free_bridge`'s medium — is *exactly* the
positivity layer. Past it there is no finite-SOS witness.

**(iv) Unification with the marginality picture.** The positivity certificate is a fixed, height-blind
object. RH is `Λ=0` (de Bruijn–Newman), height-indexed, its Lehmer-pair ties sharpening without bound with
height. The completed, capped positivity certificate is exactly as far as height-blind algebra reaches; the
remaining gap to RH is the height-indexed, analytic magnitude control — a different object in a different
medium.

## Bottom line

`zero_free_bridge` is a **complete, gap-free, kernel-checked formalization of the entire positivity layer** of
the classical zero-free-region method — the whole cosine cone, with its admissibility (`a₀<a₁`) and ceiling
(`a₁<2a₀`) exactly characterized. That layer is real, universal, and reused by Vinogradov–Korobov — and also
*finished and capped*: no better cosine polynomial, no higher degree, no cleverer SOS extends its reach past
`1−O(1)/log|t|`. Every remaining step toward RH lives in the **magnitude layer** (`|ζ|` in the critical strip),
which is analytic — discrete in places, scale-recursive at the VK frontier — and carries no finite algebraic
certificate. The proof is exactly what it is and no more: the algebraic-certificate frontier of the zero-free
region, drawn precisely, with its far edge proven. `conjecture1_proved = False`.
