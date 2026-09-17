# Arithmetic Fourier Quasicrystal — Membership Statement (formulation spec)

*2026-09-16. Formulation draft for Route A (reverse-Dyson), node A0/A1a. This
document DEFINES a class and STATES "membership ⟹ reality"; it does **not** prove
it for the arithmetic (zeta) class — that direction **is** RH.
`conjecture1_proved = False`.*

This is the honest form of "author the regularized-triple membership statement,"
at the fidelity the current formal library permits. A faithful Lean `def` is
**substrate-blocked** (see §4): the Mathlib pin has no Fourier-of-measures,
almost-periodic/crystalline-measure, or ∏ₚS¹-restriction apparatus, so a Lean
`def` today would be `opaque`-scaffolded and therefore vacuous. This spec is the
prose statement + the substrate build-order + the vacuity discipline that any
later Lean formalization must pass.

---

## 1. The tame shadow — ALREADY kernel-formalized (do not reinvent)

The `Quasicrystal` island already carries the reality-forcing at the level Mathlib
supports, and the certified obstruction that it does not reach zeta:

- **Reality-forcing, finite/rational-frequency** (the KS→OU→ACV shadow):
  `twoFreq_realRooted_iff`, `ratFreq_realRooted_of_leeYangCircle`,
  `leeYangCircle_reached_of_realRooted`, `selfInversive_binomial_realRooted`
  (all `#print axioms`-guarded, `{propext, Classical.choice, Quot.sound}`).
  These say: at finite/rational frequency, a self-inversive exponential sum is
  real-rooted **iff** its coefficient vector lies on the Lee–Yang circle — reality
  forced by membership, exactly Dyson's shape, at the tame level.
- **The certified escape**: `primeLogSpectrum_dense` + `not_uniformlyDiscrete_of_dense`
  — the prime-log frequency set is dense, so the zeta comb is **not** uniformly
  discrete, hence **not** a member of the tame (ℕ-valued, uniformly-discrete) class
  the theorems above govern. The tame proof provably does **not** transfer to zeta.

So the finite shadow of "membership forces reality" is done, and we have proven
*where* it stops.

## 2. The arithmetic class (definition — from arithmetic data ONLY)

Let `μ` be a translation-bounded (complex) measure on `ℝ` with autocorrelation
`γ` and diffraction `γ̂`. Call `μ` an **arithmetic Fourier quasicrystal (AFQ)** iff:

- **(i) pure-point diffraction.** `γ̂` is a pure-point measure (Bragg peaks): a
  countable sum of point masses. [Dyson's "quasicrystal": pure point spectrum.]
- **(ii) log-density counting.** The support-counting function satisfies
  `N_μ(T) = a·T·log T + O(T)`, `a > 0` (Riemann–von Mangoldt shape) — superlinear,
  hence **not** uniformly discrete. [This is where AFQ leaves the tame class.]
- **(iii) multiplicative (Euler) intensity.** The Bragg intensities are carried by
  the prime powers: `γ̂` is supported on `{ ± m·log p : p prime, m ≥ 1 }` with
  amplitude of the shape `(log p)·p^{−m/2}` — i.e. the intensity function is
  completely multiplicative through the primes. [The **arithmetic** content: the
  Euler product, NOT the location of zeros.]
- **(iv) torus restriction.** `μ` is the restriction to a line of a measure on the
  infinite torus `∏_p S¹` invariant under the `⊕_p ℤ` action (the solenoid/adelic
  structure dual to the multiplicative semigroup of positive integers).

**VACUITY CHECK (load-bearing).** None of (i)–(iv) mentions the reality of
`supp μ`, the critical line, or the location of any zero. Reality is **not** baked
in. Therefore "AFQ ⟹ reality" is a non-vacuous proposition — and for the zeta comb
it is RH-hard. (Contrast the `rfl`-bait the roadmap flags: any definition that
included "spectrum real" or "zeros on Re = ½" would make §3 trivial and worthless.
This one does not. Any future Lean `def` MUST preserve this — the negative control
is: exhibit a completely-multiplicative-intensity, log-density, pure-point,
torus-restricted measure whose support is NOT real, and check the class predicate
rejects it only via a genuine argument, never by fiat.)

**Membership object (the regularized triple).** `zeta_comb ∈ AFQ` must be stated
for the **Guinand–Weil-regularized** triple, not the raw dual comb: the raw comb
`Σ (log p) p^{−m/2} δ_{m log p}` is **unconditionally non-tempered** (partial sums
`Σ_{n ≤ e^R} Λ(n) n^{−1/2} ~ 2 e^{R/2}` by PNT), and carries an absolutely-
continuous archimedean `Γ′/Γ` component, so it is never pure-point un-regularized.
The regularization (subtract the archimedean density; pair test-function classes)
is itself **open formulation work** — authoring the precise subtraction is node A0.

## 3. The statement

> **AFQ-REALITY (open; RH-hard on the arithmetic class).**
> For `μ ∈ AFQ`, `supp(γ̂_μ)` — equivalently the parameters of the generating
> object — forces `μ` real, i.e. the zeros/frequencies lie on the symmetry axis.
> On the zeta comb: `zeta_comb ∈ AFQ ⟹ RiemannHypothesis`.

- The **tame** analog (`μ` uniformly discrete, ℕ-valued) **is a theorem**
  (KS→OU→ACV; finite shadow = §1). It is provable because a uniformly-discrete
  ℕ-valued FQ is the zero-counting measure of a Lee–Yang exponential polynomial,
  whose zeros are real by construction.
- The **arithmetic** case is **open precisely because zeta escapes uniform
  discreteness** (`primeLogSpectrum_dense`): the Lee–Yang route does not transfer.
  Closing it is the classification problem "arithmetic FQ ⟺ Selberg element,"
  bounded below by the Selberg degree conjecture. This is `zeta_FQ_iff_RH` — the
  `rh-hard-wall` node. Carried as `:= by sorry` in any Lean rendering, `status =
  "open"`. **No proof is claimed or supplied.**

## 4. Substrate gap (what Mathlib must gain for a faithful Lean `def`)

Checked against the pinned Mathlib (2026-09-16): **absent** — no
`MeasureTheory.*Fourier` (Fourier transform of measures), no `AlmostPeriodic`, no
crystalline/quasicrystal measure predicate, no `∏_p S¹` restriction. A faithful
formalization must first build, roughly in order:

1. Fourier transform of translation-bounded / tempered measures on `ℝ`; the
   autocorrelation and diffraction `γ̂`.
2. Pure-point / almost-periodic predicates on measures; translation-boundedness;
   the support-counting function and its density.
3. The completely-multiplicative intensity structure (this one can lean on the
   existing arithmetic-function/Euler machinery).
4. The infinite torus `∏_p S¹` / solenoid and the line-restriction map.

Each is a genuine formalization sub-project. Until (1)–(2) exist, the class
predicate cannot be stated without `opaque` placeholders, and a placeholder
predicate fails the §2 vacuity check by construction — so **the honest move is to
build the substrate or work the finite shadow, not to register a hollow `def`.**

## 5. Reachable now (finite, build-verifiable — advances the route, not the wall)

These do **not** reach §3; they dismantle around it, and each is authorable
against the current substrate:

- **Leakage dictionary (A2b).** `completely-multiplicative amplitude ⇒ zero
  composite Bragg amplitude`, as kernel lemmas on the existing defect/Bragg
  instruments (`DefectDictionary`, `BraggDefect`, `R2Rigidity.defect_eq_offline_pairs`).
  Content is the log-derivative coefficient functional; the Λ-support direction is
  `rfl`-bait and must be excluded.
- **GL(1)/GL(2) classification anchors (A1b).** Extend `B-mult-twisted` so
  `L(s, Δ)` joins the certified zoo; falsification value: the current clause
  rejects it — a live negative control on the class definition.
- **Escape-theorem extensions.** More certified instances of `zeta ∉ tame class`
  building on `primeLogSpectrum_dense` (gap-shrinking bounds, non-Bohr-discreteness
  witnesses) — sharpening exactly *why* §3 is open.

---

*This spec authors the membership STATEMENT and the class DEFINITION at prose
fidelity, vacuity-checked, with the proof direction (arithmetic case) held open as
the named RH-hard wall. It reaches RH nowhere. `conjecture1_proved = False`.*
