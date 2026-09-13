# QC_AXIOMS_DRAFT — candidate "log-lattice Fourier quasicrystal" axiomatizations + falsification matrix

*(PROGRAM MIRRORMERE, Wave-A scout A2 `qc-axioms`. Reverse-Dyson: classify 1-D
quasicrystals, locate zeta in the classification, extract zero-localization.)*

`conjecture1_proved = False`. **These are DRAFT axioms for experimental constraint, not
claims.** Every "PASS/FAIL" below is a *predicted* verdict to be mechanized by QC-0 (the zoo,
`telperion/examples/quasicrystal/zoo.py`); a variant that this doc marks PASS on a conditional
axiom carries the honest conditional label until the zoo certifies the finite evidence at some
height T. No RH claim is made or implied. Companion docs: `DYSON_QUASICRYSTAL_CERTIFICATES.md`
(category triage + citations), `QC_LITERATURE.md` (A1, exact theorem statements — gate for the
conditional-axiom labels here).

---

## 0. Setup, notation, and the one honest ceiling

Fix the additive-frequency conventions of the Guinand–Weil (GW) explicit formula so that the
"support side" carries the **zeta ordinates** and the "spectrum side" carries the **prime
powers**. Write the two combs:

- **Zeta comb** (support side): `μ_ζ = Σ_ρ m(ρ) δ_{γ_ρ}`, where `γ_ρ = −i(ρ − 1/2)` runs over
  the completed-zeta nontrivial zeros, symmetrized `±γ` and weighted by multiplicity
  `m(ρ) ∈ ℤ_{≥1}`. **Unconditionally the γ_ρ are complex**; RH ⟺ all γ_ρ real. Counting
  function `N(T) ~ (T/2π) log(T/2π) − T/2π`; consecutive gaps `~ 2π / log(γ/2π) → 0`, so the
  support is **NOT uniformly discrete** (its density grows like `log`).

- **Prime comb** (spectrum side): `σ = Σ_{p,k} (log p) p^{−k/2} (δ_{k log p} + δ_{−k log p})`
  plus the archimedean smooth density and pole terms. This comb exists **unconditionally** as a
  tempered distribution; its atoms sit on the **log-lattice**
  `Λ_log = { ±k log p : p prime, k ∈ ℤ_{≥1} }`, a multiplicatively finitely generated set.

GW pairs them: for suitable even test `g` with transform `h`,
`Σ_ρ h(γ_ρ) = A_∞(h) − 2 Σ_{p,k} (log p) p^{−k/2} g(k log p) + [poles]`.

**The honest ceiling (from `DYSON_QUASICRYSTAL_CERTIFICATES.md`, verified panel).** Kurasov–
Sarnak prove that **every 1-D ℤ_{≥1}-valued Fourier quasicrystal (FQ) is a real zero set of a
Lee–Yang exponential polynomial** — and that **the zeta measure is provably NOT an FQ** (verbatim:
"the explicit formula in the theory of primes does not give a Fourier quasicrystal"). So the
*classical* FQ class is the wrong target: it already excludes zeta unconditionally, by density.
The reverse-Dyson move of this document is therefore **not** "is zeta an FQ" (answer: no), but
"**which weakening of the FQ axioms is the minimal one that (a) still excludes DH and (b) admits
zeta, so that the residual gap between (a) and (b) is exactly the RH-hard content.**" That
residual gap is what each variant below tries to name.

Two design axes generate the variants:

1. **Support grade.** From strongest to weakest: uniformly discrete (classical FQ) → log-density
   (`N(T)`-shaped, admits zeta) → density-bounded-in-windows → arbitrary locally finite.
2. **Spectrum/weight grade.** From strongest to weakest: atomic spectrum ⊂ Λ_log with the exact
   `(log p) p^{−k/2}` weights and **positive** → atomic ⊂ Λ_log with signed weights →
   atomic-on-any-lattice → no atomic-spectrum requirement.

The **DH-killer bet** lives on axis 2: DH's explicit-formula spectrum is **not** of the
`(log p) p^{−k/2}` positive-weight form — it is built from two conjugate characters mod 5 with
**complex / sign-varying** coefficients and **no Euler product**, so its "prime side" is not a
positive log-lattice comb at all. Section 6 makes this precise; it is the single property we lean
on hardest.

---

## 1. Variant A — "Log-lattice FQ (weak/support-relaxed)"

**Intent.** The *minimal* relaxation of the classical FQ axioms that drops uniform discreteness
so that a `log`-density support (hence zeta) is admissible, while keeping a genuinely atomic,
lattice-supported spectrum so that Poisson/random combs and DH still fail.

A measure `μ = Σ_j a_j δ_{x_j}` on ℝ is a **Variant-A log-lattice FQ** iff:

- **(A-i) Support class.** `supp μ` is locally finite, symmetric (`x ∈ supp ⇒ −x ∈ supp`), and
  has counting function of **at most log-linear growth**: `#{x_j : |x_j| ≤ T} = O(T log T)`
  (equivalently, gaps may shrink no faster than `1/log`). Masses `a_j ∈ ℤ_{≥1}` (multiplicity).
  [Zeta: `N(T) ~ (T/2π)log(T/2π)` — PASSES unconditionally; this is a density statement, not a
  reality statement.]
- **(A-ii) Spectrum class.** The distributional Fourier transform `μ̂` is a **pure-point** measure
  whose atomic support (its Bragg spectrum) is contained in a set that is **multiplicatively
  finitely generated per bounded window**: for every `R`, `supp μ̂ ∩ [−R,R]` lies in
  `{ ±Σ_i k_i log p_i }` with finitely many primes `p_i ≤ e^R`. (This is the "atomic spectrum on
  the log-lattice `Λ_log`" condition, windowed so it is finitely checkable.)
- **(A-iii) Weight/amplitude.** *None beyond `μ̂` pure-point.* (Variant A does **not** constrain
  the sign or decay of the Bragg amplitudes; that is deferred to B/C.)
- **(A-iv) Temperedness grade.** `μ` and `μ̂` are tempered distributions of finite order.

**Zeta status under A.** (A-i), (A-iv) hold **unconditionally**. (A-ii) is the hard one: it is a
**pure-point-diffraction** statement about the zeta comb, which is **RH-adjacent** — under RH the
zeta comb pairs (via GW) against the prime comb on `Λ_log`, giving Bragg peaks there; *without*
RH the "peaks" at `log p^k` are not established as genuine atoms of a pure-point `μ̂` (the panel
REFUTED the unconditional `{log p^k}`-support claim 0-3). **Label: (A-ii) is CONDITIONAL for
zeta — pure-point-diffraction at log-lattice frequencies is not unconditionally known; it is the
GW-image of exactly the reality/temperedness of the support side.** Variant A is thus the *first*
place RH-equivalent content appears, and it appears entirely in the spectrum axiom, not the
support axiom.

**Verdict on A as a killer.** A excludes uniformly-discrete-only objects' *complement* correctly
but is **weak on DH**: DH's zero-counting also grows like `T log T` (same functional-equation
class), so (A-i) does not separate it, and DH *does* have a bounded-density spectrum. A separates
DH **only** through (A-ii)'s log-lattice restriction — DH's diffraction atoms sit at
`{±k log 5}` scaled combinations from the *conductor 5*, i.e. on a **`log`-lattice generated by a
single modulus, not by the full prime log-lattice with `(log p)p^{−k/2}` weights**. This is a
*genuine but fragile* separation (see §6): it fails if one reads "`Λ_log`" loosely enough to
include `log 5`. **A is therefore marked LIVE-BUT-FRAGILE: it needs the weight axiom of B/C to
kill DH robustly.**

---

## 2. Variant B — "Positive log-lattice FQ (weight-graded)"

**Intent.** Add the DH-killer explicitly: the spectrum must be the prime comb *shape* — atoms on
`Λ_log` with **positive** amplitudes of the correct `(log p) p^{−k/2}` order. This is the variant
we bet on.

`μ` is a **Variant-B positive log-lattice FQ** iff (A-i), (A-iv) hold and:

- **(B-ii) Spectrum class (sharpened).** `μ̂` is pure-point with atomic support **exactly** in the
  prime log-lattice `Λ_log = {±k log p}`; no atoms at non-prime-power frequencies. (Finitely
  checkable per window: "certified nonzero mass only at `u = k log p` and certified **zero** mass
  at any tested non-log-prime `u`.")
- **(B-iii) Weight/amplitude (the killer).** For each atom at `u = k log p`, the Bragg amplitude
  `c(u)` is **real, strictly positive, and of order `(log p) p^{−k/2}`**: there exist absolute
  `0 < c_− ≤ c_+` with `c_− (log p) p^{−k/2} ≤ c(u) ≤ c_+ (log p) p^{−k/2}`. **Positivity is the
  load-bearing clause.**
- **(B-i), (B-iv)** as in A.

**Zeta status under B.** (B-ii)/(B-iii) are the GW-image of RH: the prime side of GW *is* exactly
`(log p) p^{−k/2} > 0`, so **zeta PASSES (B-iii) by the explicit formula unconditionally** (the
prime-side weights of GW are literally `(log p)p^{−k/2}` and positive — this is arithmetic, not
RH). What is **CONDITIONAL** is again (B-ii)'s *pure-point-ness* of `μ̂` — that the support side
really is a Dirac comb dual to this positive prime comb — which is the RH content. So Variant B
**cleanly splits the difficulty**: the *weight* axiom (B-iii) is unconditional for zeta and is the
DH-killer; the *pure-point spectrum* axiom (B-ii) is RH-equivalent. This split is the main
conceptual output of this document.

**DH under B.** DH **FAILS (B-iii)** decisively. DH `= (1−iκ)/2 · L(s,χ) + (1+iκ)/2 · L(s,χ̄)`
for a character `χ mod 5` (κ related to the golden ratio); it has **no Euler product**, so its
Dirichlet coefficients are **not multiplicative** and its explicit-formula "prime side" is a
combination of the two characters that is **not of the single positive `(log p)p^{−k/2}` form** —
the character values `χ(p), χ̄(p)` are roots of unity (complex, sign/phase-varying), so the
per-prime amplitudes are **complex and not sign-definite**. Positivity fails. **DH is DEAD under
B.** (This is the intended kill and the reason B is the recommended variant.)

---

## 3. Variant C — "Signed log-lattice crystalline measure (weight-relaxed)"

**Intent.** A deliberately *too-weak* control: drop positivity, keep only "atomic spectrum on
`Λ_log`." Included precisely so the matrix demonstrates a variant that **DH survives** — hence a
DEAD variant — pinning down that **positivity, not lattice-support, is what kills DH.**

`μ` is a **Variant-C signed log-lattice crystalline measure** iff (A-i), (A-iv) hold and:

- **(C-ii)** `μ̂` is pure-point, atomic support ⊂ `Λ_log` (windowed, as A-ii/B-ii).
- **(C-iii) Weight/amplitude.** Amplitudes may be **any** complex numbers with `|c(u)| =
  O((log p) p^{−k/2})` (decay kept, **positivity dropped**).
- **(C-i), (C-iv)** as in A.

**DH under C.** DH's explicit-formula spectrum *does* sit on a log-lattice (generated by the
conductor and, through the character sums, effectively on `{±k log p}` with the character
weights) and its amplitudes are `O((log p)p^{−k/2})` in size. So **DH PASSES (C-ii), (C-iii)** —
the only thing C removed is the exact positivity that B used. **⇒ Variant C is DEAD** (governance
rule: any axiom set DH satisfies is dead, because DH has off-line zeros). C is retained in the
matrix as the **contrastive control** that isolates the killer: comparing C (DH passes) with B
(DH fails) proves the DH-killer is **weight positivity**, clause (B-iii), and nothing else.

---

## 4. Variant D — "Temperedness-graded / defect-tolerant log-lattice FQ" (stretch)

**Intent.** The 2/3-paper-grade variant. Instead of demanding full pure-point spectrum
(RH-equivalent), demand it **up to a controlled finite defect** measured by the negative index of
finite Weil-form compressions — the Alpöge–Furman signature-`(1,1)` blocks. This is the variant
that pairs with the Pillar-3 wedge and is only **partially** verifiable for zeta.

`μ` is a **Variant-D defect-`k` log-lattice FQ** iff (B-i), (B-iii), (B-iv) hold and:

- **(D-ii) Defect-graded spectrum.** There is `k ∈ ℤ_{≥0}` such that every finite GW-compression
  (the Weil Hermitian form restricted to a finite test-function subspace) has **negative index
  ≤ k**; equivalently `μ̂` is pure-point **up to `k` conjugate off-line pairs**, each contributing
  a signature-`(1,1)` block. `k = 0` ⟺ Variant B ⟺ RH. `k` finite-and-bounded is the
  Alpöge–Furman "2/3"-style partial statement.
- **(D-temperedness grade.)** The order/growth of `μ̂` is allowed to degrade by a factor
  controlled by `k` (each off-line pair worsens temperedness by a fixed increment) — this is where
  the "temperedness grade" axis meets the "defect" axis.

**Zeta status under D.** **PARTIAL / 2/3-paper-grade.** By Alpöge–Furman (arXiv:2608.13637),
finite compressions of the Weil Hermitian form have **unconditionally bounded negative-index
contributions from off-line pairs** (the signature-`(1,1)` blocks). So a *finite, unconditional*
`k` bound at each height T is exactly what their machinery yields — this is the honestly-partial,
verifiable-now content. Driving `k → 0` is RH. **Label: (D-ii) is UNCONDITIONALLY PARTIAL for
zeta — a finite `k` at each height is provable; `k = 0` is RH.**

**DH under D.** DH has a **positive proportion** of off-line zeros, so its defect `k = k(T) → ∞`
(unbounded, growing with height) — it can **never** satisfy a *bounded*-`k` D-axiom. **DH is DEAD
under D** for a *quantitatively different* reason than B: not "wrong weight sign" but "**unbounded
defect**." D thus kills DH two ways (it also fails (B-iii)), and this redundancy is a feature: it
shows the defect grading is not merely re-encoding the positivity kill.

---

## 5. THE MATRIX (axiom variant × control-zoo object → predicted PASS/FAIL + reason)

Columns (the QC-0 control zoo):
- **ζ** = zeta comb (support side of GW).
- **DH** = Davenport–Heilbronn comb (must FAIL every live variant — it has off-line zeros).
- **Eps** = Epstein zeta of a **non-arithmetic** binary quadratic form (functional equation,
  off-line zeros, coefficients `r_Q(n)` = representation numbers — no Euler product).
- **Lat** = a genuine lattice Dirac comb `Σ_{n∈ℤ} δ_{nα}` (Poisson summation — the trivial FQ;
  sanity, must PASS).
- **KS-LY** = a Kurasov–Sarnak Lee–Yang FQ from a fixed stable polynomial (real-rooted
  exponential polynomial; the *canonical* FQ — must PASS the FQ-shaped axioms).
- **Rnd** = a random (Poisson-process) comb with i.i.d. weights (no atomic spectrum — must FAIL).

Legend: **P** = predicted PASS (finite evidence should certify), **F** = predicted FAIL,
**P*** = PASS but on a **conditional/partial** axiom (label carried), **DEAD** = variant killed
because DH passes it.

| Variant | ζ | DH | Eps | Lat | KS-LY | Rnd | Variant verdict |
|---|---|---|---|---|---|---|---|
| **A** log-lattice FQ (support-relaxed) | **P*** (A-ii pure-point = RH-adjacent) | F (spectrum not on prime `Λ_log`; but *fragile*, see §6) | F (spectrum on `√`-form/Epstein frequencies, not `Λ_log`) | **P** (Poisson: `μ̂` atomic on dual lattice `⊂Λ_log`-trivially) | **P** (real-rooted ⇒ pure-point, Favorov gate) | **F** (no atomic spectrum) | **LIVE-but-fragile** — needs weight axiom to kill DH robustly |
| **B** positive log-lattice FQ (weight killer) | **P** on (B-iii) weights [uncond.]; **P*** on (B-ii) pure-point [RH] | **F** (no Euler product ⇒ character weights complex/sign-varying ⇒ **positivity fails**) | **F** (`r_Q(n)` weights not `(log p)p^{−k/2}`-shaped; not sign-definite prime comb) | **P** (trivial: single positive atom family) | **P** (positive-mass FQ by construction) | **F** (no atomic spectrum) | **RECOMMENDED** — clean split: weights uncond., pure-point RH; DH dead by positivity |
| **C** signed log-lattice (weight-relaxed) | **P*** (same as B minus positivity) | **P** (DH's signed weights on log-lattice satisfy it) | **P** (Epstein signed weights fit signed axiom) | **P** | **P** | **F** | **DEAD** (DH passes) — proves killer = **positivity**, contrastive control |
| **D** defect-`k` / temperedness-graded (2/3-grade) | **P** partial (finite `k` uncond., Alpöge–Furman); `k=0`⟺RH | **F** (defect `k(T)→∞`: positive proportion off-line) | **F** (Epstein also has ∞-defect off-line zeros) | **P** (`k=0`) | **P** (`k=0`) | **F** (not even defect-crystalline) | **LIVE / partial** — pairs with Pillar-3 wedge |

**Cross-checks against the governance rules:**
- **DH FAILS every LIVE variant (A, B, D).** ✔ It PASSES only C — which is therefore correctly
  marked DEAD. This is the required behavior.
- **ζ PASSES each variant's unconditionally-checkable axioms; conditional ones are labeled `P*`
  or "partial."** ✔ In B, the *weight* axiom is unconditional-PASS and only *pure-pointness* is
  `P*` (RH); this is the intended clean separation.
- **Lat PASSES trivially** (Poisson summation, Mathlib-available). ✔
- **Rnd FAILS** all (no atomic spectrum). ✔
- **KS-LY PASSES** the FQ-shaped axioms (it is the canonical FQ). ✔ It is the positive control
  that a live axiom is not vacuously empty.
- **Epstein** FAILS A/B/D (its spectrum is on quadratic-form frequencies with `r_Q(n)` weights,
  not the positive prime log-lattice) and PASSES only C — a *second* DEAD-witness, reinforcing
  that C is dead. Epstein is the "off-line zeros from a different arithmetic source" control.

---

## 6. The DH-killer, made precise (the bet)

**Claim (the bet).** The property that kills DH across all live variants is **weight positivity of
the prime-side comb (clause B-iii)**, which fails for DH because **DH has no Euler product**.

Precise mechanism:
- For zeta, `−ζ'/ζ(s) = Σ_{p,k} (log p) p^{−ks}`, so the GW prime side has amplitudes
  `(log p) p^{−k/2} > 0` — a **single, positive, multiplicative** comb.
- For DH `F(s) = (1−iκ)/2 L(s,χ) + (1+iκ)/2 L(s,χ̄)`, there is **no** `−F'/F` with nonnegative
  Dirichlet coefficients: `F` is a *sum* of two L-functions, so `F'/F` is **not** a Dirichlet
  series with multiplicative, sign-definite coefficients. The "prime side" of a DH explicit
  formula is governed by the **logarithmic derivative of a linear combination**, whose local
  factors mix `χ(p)` and `χ̄(p)` (complex conjugate roots of unity) and are **not** of the form
  `(positive) · (log p) p^{−k/2}`. Positivity — and even a single-comb structure — is destroyed.
- **Contrast that isolates the killer.** Variant C keeps everything *except* positivity; DH
  **passes C**. Variant B adds positivity; DH **fails B**. Since C and B differ *only* in clause
  (B-iii), the kill is attributable to positivity alone. That is the experiment the zoo runs.

**Why not bet on support density (support-axis) instead?** Because DH is in the *same*
functional-equation class as zeta and has the same `T log T` zero density — the support axiom
(A-i/B-i) does **not** separate them. Density is a red herring for the DH kill; the separation is
purely spectral/weight-side. (Support density *does* separate zeta from the classical
uniformly-discrete FQ class — that is what forces us off the classical axioms in the first place —
but it does nothing against DH.)

**Fragility note on Variant A.** Under A alone (no weight axiom) the DH kill rests on "DH's
spectrum is not on the *prime* log-lattice." This is true but definitionally slippery: DH's
spectrum lives on a `log`-lattice tied to conductor 5 and the character sums, and a loose reading
of `Λ_log` could swallow `log 5`. B removes the slipperiness by demanding the exact positive
`(log p)p^{−k/2}` *weights*, which no reading of DH satisfies. **Hence the recommendation: B, not
A, is the operative axiom set; A is kept only as the minimal support-relaxation milestone.**

---

## 7. Classification conclusion each variant could yield, and its Pillar-3 wedge

- **Variant A → "reality of support up to nothing / pure-point dichotomy."** Best hope: a
  *dichotomy* theorem — a log-density symmetric comb with pure-point spectrum on `Λ_log` is either
  the GW image of an arithmetic L-function or is excluded. This is weak (it does not force zero
  reality) and pairs with **no** strong wedge; A's role is to establish the support-relaxed
  category exists and is nonempty (KS-LY inside it).
- **Variant B → "Lee–Yang forced form on the positive log-lattice."** Best hope: *if* a positive
  log-lattice FQ exists with zeta's weights, the KS/Alon–Cohen–Vinzant machinery would force its
  support to be the real zero set of a real-rooted exponential polynomial — i.e. **forced zero
  reality** on the support side. This is the strongest classification target and pairs with the
  **partial-Weil-positivity wedge** (Pillar 3): positivity of the finite GW/Weil form is exactly
  clause (B-iii) lifted to the Hermitian form, so B is the axiom-language home of "Weil positivity
  ⇒ crystalline ⇒ real support."
- **Variant C → (dead)** — no classification conclusion; its only output is the *negative*
  lemma "positivity is necessary," which is itself a useful wedge-adjacent fact: it says the wedge
  **must** be a positivity statement, not a mere lattice-support statement.
- **Variant D → "crystalline up to defect `k`; `k=0` ⟺ real support."** Best hope: a **quantitative
  rigidity** — bound the diffraction defect by the negative index `k` of finite Weil-form
  compressions, so that *reducing `k`* (the Alpöge–Furman program's direction) *is* sharpening
  crystallinity toward RH. This pairs with the **complex-support-rigidity wedge** (Pillar 3): the
  signature-`(1,1)` leakage of each off-line pair is the measured obstruction to full
  crystallinity, and D is its axiomatic container. **D is the variant most likely to produce a new
  RH-equivalence in rigidity language** ("zeta is defect-0 crystalline on the positive log-lattice"
  ⟺ RH), which is the program's stated realistic payoff.

---

## 8. MECHANIZATION CONTRACT for QC-0 (the zoo)

For each axiom clause, the finite certified computation that QC-0 must run to emit PASS/FAIL at a
given height `T`, plus the **forged-input negative control** that must FAIL where a genuine input
PASSes. All Bragg quantities go through the existing certified pipeline
(`BraggH100`/`CosEnclosure`/`BraggSupport`, `bragg_refine.py`, `bragg_figures.py`); "Landau value"
= the theoretical Bragg amplitude predicted by the GW/Kurasov–Sarnak closed form.

| Axiom clause | Certified PASS evidence at height T | Certified FAIL evidence | Forged-input negative control |
|---|---|---|---|
| **(A-i)/(B-i) support density** | Certified count `#{|x_j|≤T}` within Arb error of the `T log T`-model (for ζ: RvM/`N(T)`; in-corpus certified ladder to T=240,000) | Count grows faster than `T log T` (or support not locally finite in a certified box) | Feed a *uniformly-discrete* comb: must be flagged as NOT log-density (distinguishes classical FQ) |
| **(A-ii)/(B-ii) atomic spectrum ⊂ Λ_log** | Certified **nonzero Bragg mass** at `u = k log p` (e.g. `u=log 2, log 3, 2log2, log 5`) via CosEnclosure box strictly excluding 0 | Certified **nonzero mass at a non-log-prime frequency** `u ∉ Λ_log` (e.g. `u = log 6 = log2+log3` must be checkable, and a *generic* `u=1.0`) | Feed a comb with a planted atom at an irrational non-lattice `u₀`: box at `u₀` must certify nonzero ⇒ FAIL |
| **(B-iii) weight positivity + decay** | Certified Bragg amplitude `c(k log p)` enclosure with **lower bound > 0** and within `[c_−,c_+]·(log p)p^{−k/2}` | Certified amplitude enclosure whose interval **contains a negative value** or straddles 0 (as for DH's character-mixed weights) | Feed DH's certified comb (from A3 `arb_dh.py`): amplitude box at `log 2` must straddle/there-be-no-positive-comb ⇒ FAIL; **and** a forged comb with a hand-set *negative* weight at `log 2` ⇒ FAIL |
| **(C-iii) signed decay only** | Certified `|c(k log p)| ≤ c_+ (log p)p^{−k/2}` (no sign test) | Amplitude magnitude exceeds decay envelope | Forged comb with an atom of `O(1)` amplitude at large `u`: violates decay ⇒ FAIL (guards against C being vacuously true) |
| **(D-ii) defect-`k` bound** | Certified negative index of a finite GW/Weil-form compression `≤ k` at height T (port zeta-23/D4 inertia bricks) | Negative index `> k` (or increasing with the test-space dimension, as for DH) | Feed DH: certified negative index must be seen to **grow** with T ⇒ unbounded defect ⇒ FAIL; forged single off-line pair (BraggH100 + synthetic β≠1/2, the B3 experiment) ⇒ exactly one signature-`(1,1)` block ⇒ defect `1` |
| **temperedness (A-iv…D)** | Certified finite-order growth bound on the paired distribution against a fixed Schwartz test | Growth exceeds any polynomial order in a certified box | Forged non-tempered comb (exponentially growing weights): FAIL |

**Global harness requirements (restating governance):**
1. **DH must FAIL** the intended clause of every live variant — specifically (B-iii) positivity and
   (D-ii) bounded-defect — using the *real* certified DH comb from A3, not a caricature.
2. **ζ's certified data must PASS** every unconditionally-checkable clause (support density,
   positive weights (B-iii), finite defect (D-ii)) and every RH-conditional clause (B-ii
   pure-pointness) must be emitted **labeled `CONDITIONAL`, never as an unqualified PASS.**
3. **At least one forged-input negative control per clause** (table col. 4) must FAIL, proving the
   harness has discriminating power and is not vacuously green.
4. **Lat / KS-LY** positive controls must PASS the FQ-shaped clauses; **Rnd** must FAIL the atomic
   -spectrum clause — sanity rails.

---

## 9. Sharpest open definitional problem hit

**The windowing of "spectrum ⊂ `Λ_log`" is not obviously the right invariant, because `Λ_log` is
not uniformly discrete and its finite-window generation is basis-dependent.** Concretely: clause
(A-ii)/(B-ii) says "`supp μ̂ ∩ [−R,R] ⊂ {±Σ k_i log p_i}, p_i ≤ e^R`." But `{Σ k_i log p_i}` is
**dense** modulo any real (the log-primes are ℚ-linearly independent, so integer combinations are
equidistributed) — so *any* finite set of frequencies is `ε`-close to a log-lattice point, and a
naive "is `u` on `Λ_log`?" test is ill-posed at finite precision. The zoo's non-log-prime negative
control (`u = log 6`, `u = 1.0`) only works because we test **fixed rational-log targets vs a fixed
gap `η`**; but a truly adversarial DH-like comb could place atoms *arbitrarily close* to genuine
`k log p` without being arithmetic. **The clean definitional fix is unresolved:** whether to
characterize the log-lattice by (a) the *weights* `(log p)p^{−k/2}` alone (making (B-iii) the real
definition and (B-ii) derivative — the reading this doc leans toward), or (b) a genuine
Diophantine separation condition on the atom locations, or (c) the *Euler-product / multiplicativity*
of the amplitude sequence as the primitive (which would make "on the prime log-lattice" mean
"amplitudes are a multiplicative function of the frequency's prime content" — arguably the deepest
and the one that most directly excludes DH). Resolving this — **is the correct primitive the
positive weights, the Diophantine support, or the multiplicativity?** — is the definitional crux
the whole matrix rests on, and it is where A1 (`QC_LITERATURE.md`, the exact Kurasov–Sarnak /
Olevskii–Ulanovskii hypotheses on weight classes and spectrum) must adjudicate before B2 formalizes
any of these as named Props.

---

## Sources (verified; full precise statements deferred to A1 `QC_LITERATURE.md`)

- Dyson, "Birds and Frogs," *Notices AMS* 56(2), 2009 (the quasicrystal framing).
- Kurasov & Sarnak, "Stable polynomials and crystalline measures," *J. Math. Phys.* 61:083501
  (2020) / arXiv:2004.05678 (construction; verbatim "the explicit formula … does not give a
  Fourier quasicrystal").
- Alon, Cohen & Vinzant, "Every real-rooted exponential polynomial is the restriction of a
  Lee–Yang polynomial," arXiv:2307.13498 (2023); Alon, Kummer, Kurasov & Vinzant, "Higher
  dimensional Fourier quasicrystals from Lee–Yang varieties," *Inventiones* 2024
  (s00222-024-01307-8).
- Olevskii & Ulanovskii (1-1 correspondence FQ ↔ real-rooted exponential polynomials;
  completeness of the ℤ-valued FQ classification with Kurasov–Sarnak).
- Favorov, arXiv:2311.02728 (real-rootedness ⇒ pure-point diffraction gate).
- Davenport & Heilbronn 1936; Spira 1994 (certified off-line DH zeros, e.g.
  `0.808517 + 85.699348 i`); DH `= (1−iκ)/2 L(s,χ) + (1+iκ)/2 L(s,χ̄)`, `χ mod 5`.
- Alpöge & Furman, arXiv:2608.13637 (bounded negative index of finite Weil-form compressions;
  signature-`(1,1)` off-line blocks — the Variant-D / Pillar-3 input).
- Companion in-repo: `telperion/docs/DYSON_QUASICRYSTAL_CERTIFICATES.md` (category triage,
  adversarially verified), certified Bragg pipeline
  `telperion/examples/zeta_zero_localization/{BraggH100,BraggSupport,bragg_refine.py}`.

`conjecture1_proved = False`.
