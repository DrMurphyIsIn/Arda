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

---

# APPENDIX (v2, W3a) — Variant B-mult: the MULTIPLICATIVITY restatement

*(PROGRAM MIRRORMERE, Wave-3 rung W3a `qc3-mult`. Appended, not rewriting the
history above. `conjecture1_proved = False`.)*

## W3a.0 Why this appendix exists — the adjudication

§9 above left the sharpest open definitional problem: what is the correct **primitive**
for "spectrum on the prime log-lattice"? Three candidates were on the table —
(a) the positive **weights** `(log p)p^{−k/2}`, (b) a **Diophantine separation**
condition on atom locations, (c) the **multiplicativity / Euler-product** structure of
the amplitude sequence. §9(c) already flagged (c) as "arguably the deepest and the one
that most directly excludes DH."

The program's symmetry analysis adjudicated for **(c) multiplicativity**, on the
following grounds (this is the W3a input, from the ROADMAP and QC_LITERATURE §1.3):

- The **classified** ℕ-valued FQs (ACV Cor 1.4) are restrictions-from-finite-tori:
  a real-rooted `f(x) = e^{λ_0 x} p(e^{ixℓ})` with `ℓ ∈ ℝ₊ⁿ` ℚ-linearly independent,
  whose **spectrum lies in a finitely generated group `ℤ⟨ℓ⟩`** (ACV hypothesis (iv)).
  The generating structure — a **product** over finitely many independent
  frequencies — is what the classification is *about*, not a metric/separation
  condition on locations.
- Zeta's upstairs object is the **infinite torus `∏_p S¹`** (one circle per prime),
  and its Euler product `ζ(s) = ∏_p (1−p^{−s})^{−1}` is *literally* a product over that
  torus's factors. The **product structure**, not a Diophantine gap, is what
  generalizes from the finite-`n` ACV picture to zeta's infinite-`n` picture (W3c).
- The zoo already showed (variant C, §3 and §6) that DH's admission under the **loose**
  lattice reading is exactly what the *definitional slipperiness* of "on `Λ_log`"
  buys DH. A2 §6 made that operational; multiplicativity removes the slipperiness at
  the root, because it is a property of the **amplitude sequence**, not the atom set.

So B-mult replaces B's **weight-positivity** primitive (B-iii) with a strictly
stronger **multiplicative-generation** primitive. Positivity becomes a *consequence*
(each prime-layer von-Mangoldt amplitude is `+log p > 0`), not the axiom.

## W3a.1 The axiom, verbatim

Let `μ` be a symmetric, log-density, tempered atomic measure (clauses (A-i), (A-iv) as
in Variant A) whose dual comb `μ̂` is pure-point (clause (B-ii), still RH-conditional
for zeta). Write the Bragg (prime-side) atoms as frequency–amplitude pairs
`{(u, c(u)) : u ∈ supp μ̂, u > 0}`.

> **(B-mult) — Multiplicative amplitude generation.**
> The frequency–amplitude pairs are **generated multiplicatively from the prime
> layer**. Precisely: the atomic support of `μ̂` is `Λ_log = {±m log p : p prime,
> m ∈ ℤ_{≥1}}` — **no atoms at any non-prime-power frequency** (in particular
> `c(u) = 0` for every `u = log n` with `n` composite) — and there is a **per-prime
> weight** `w : {primes} → ℝ_{>0}` such that for every prime `p` and every `m ≥ 1`
> the amplitude at `u = m log p` is
> \[ \; c(m\log p) \;=\; (\log p)\, w(p)^m . \; \]
> Equivalently: the dual comb is the image of a **completely multiplicative** structure
> on the free commutative monoid over the primes — the pairs
> `{(m log p, (log p)·w(p)^m)}` are the multiplicative closure of the prime-layer pairs
> `{(log p, (log p)·w(p))}`, with the arithmetic normalization `w(p) = p^{−1/2}`.

**Reading.** "On the prime log-lattice" is now *derived*: it means precisely
"the amplitude sequence is the log-derivative of an Euler product." The condition
`c(u)=0` at composite `u` is the finite fingerprint of the Euler product (a completely
multiplicative Dirichlet series has von-Mangoldt coefficients supported only on prime
powers). The geometric law `c(mlog p)/c((m−1)log p) = w(p)` (independent of `m`) is the
per-prime self-similarity that a single circle-factor `S¹_p` of the torus contributes.

**Relation to B (dominance).** B-mult ⟹ B-iii: `c(log p) = (log p)w(p) = (log p)p^{−1/2}
> 0`, so positivity of the prime layer is automatic, and the decay envelope
`c_− ≤ 1 ≤ c_+` holds with `w(p)=p^{−1/2}`. The converse fails (a signed-but-positive-at-
primes comb need not be multiplicatively generated), so **B-mult ⊋ B** as an axiom.

## W3a.2 Zeta instance (unconditional — the Euler product)

For zeta the prime side of the GW explicit formula is the log-derivative of the Euler
product:
\[ -\frac{\zeta'}{\zeta}(s) = \sum_{p}\sum_{m\ge1} (\log p)\, p^{-ms}
   = \sum_n \Lambda(n) n^{-s},\qquad \Lambda(p^m)=\log p,\ \Lambda(\text{composite})=0. \]
Hence the Bragg amplitudes are `c(m log p) = Λ(p^m)·p^{−m/2} = (log p)·p^{−m/2}`, which
is exactly `(log p)·w(p)^m` with `w(p)=p^{−1/2}`. Both fingerprints hold **arithmetically,
with no appeal to RH**:

- **Composite-vanishing:** `Λ(6)=Λ(10)=…=0` (verified in the zoo: `b(6)=b(10)=b(25)=0`).
- **Per-prime geometric law:** `c(m log p)/c((m−1)log p)=p^{−1/2}` exactly for every
  `p,m` (verified: ratios `2^{−1/2}, 3^{−1/2}, 5^{−1/2}, …` to machine precision).

**This is the clean split preserved from §2**: the *generation of the amplitudes*
(B-mult) is **unconditional/arithmetic** — zeta PASSes it outright — while the
*pure-pointness of the dual comb* (B-ii) remains the RH-conditional clause. B-mult
changes **which** unconditional property is the DH-killer (multiplicativity, not bare
positivity); it does **not** move any RH content.

## W3a.3 DH refutation, made precise (which amplitude breaks the law)

DH is the period-5 Dirichlet series `D(s) = Σ_n c(n) n^{−s}` with coefficient vector
`c = [1, κ, −κ, −1, 0]` (indexed `c(1)=1, c(2)=κ, c(3)=−κ, c(4)=−1, c(5)=0`, repeating),
`κ = (√(10−2√5)−2)/(√5−1) ≈ 0.284079` (QC_DH_SCOUT.md). Equivalently
`D = (1−iκ)/2·L(s,χ) + (1+iκ)/2·L(s,χ̄)` for `χ mod 5`. **DH has no Euler product**, so
its "prime side" `−D'/D(s) = Σ_n b(n) n^{−s}` is the log-derivative of a
**non-multiplicative** series. Computing `b(n)` from the exact recursion
`c(n)log n = Σ_{d|n} b(d) c(n/d)` (mechanized in the zoo) exhibits the breakage
**at the very first composite**:

| n | 2 | 3 | 4=2² | 6=2·3 | 9=3² | 25=5² |
|---|---|---|---|---|---|---|
| DH `b(n)` | +0.1969 | **−0.3121** | −1.4422 | **+1.9364** | −2.2859 | 0.0000 |
| ζ `Λ(n)` | +0.6931 | +1.0986 | +0.6931 | **0.0000** | +1.0986 | +1.6094 |

Two independent failures of B-mult, both certified:

1. **Composite atom (the primary kill).** `b(6) = +1.9364 ≠ 0`. The generation law
   demands `c(log 6)=0` (no atom at the composite frequency `log 6 = log 2 + log 3`).
   DH's von-Mangoldt-analogue coefficient at `n=6` is *manifestly nonzero* — this is the
   direct fingerprint of "no Euler product," and it is the amplitude the zoo reports as
   the failing one. (The DH coefficients are `Λ(n)·(χ(n)+χ̄(n))`-flavored — sign-varying
   with `n mod 5` — so `b` acquires cross terms at composite `n` that any multiplicative
   series kills.)
2. **Sign-varying prime layer + broken m-generation (the redundant kill).** Already at
   `m=1`: `b(2)=+0.197 > 0` but `b(3)=−0.312 < 0` — no **positive** `w(p)` can produce a
   negative prime-layer amplitude, so even restricted to primes the sequence is not
   `(log p)w(p)`. And the `m=2` layer breaks generation from `m=1`: for zeta
   `Λ(4)=Λ(2)=log 2` (m-constant), whereas DH has `b(4)=−1.442 ≠ b(2)=+0.197`, opposite
   sign — the geometric law `c(m log p)=(log p)w(p)^m` fails at `2²`.

Either fingerprint alone kills DH; the zoo trips on (1) first (`b(6)≠0`) and reports it.

## W3a.4 Relation to the infinite-torus formulation (W3c) and the ACV hypothesis

B-mult is the **finite/spatial shadow** of the W3c torus formulation. ACV (QC_LIT §1.3
hyp (iv)) classifies ℕ-FQs whose spectrum lies in a **finitely generated group**
`ℤ⟨ℓ⟩` — a *finite* torus `(S¹)^n`. B-mult is precisely the statement that zeta's dual
comb is the restriction of a completely multiplicative structure on the **free monoid
over all primes** — the *infinite* analogue, `∏_p S¹`, one generator `w(p)` per prime.
The two connect as:

- **Finite (ACV / W3b GW-finite):** truncate to primes `p ≤ e^R` inside a window
  `[−R,R]`; B-mult restricted to the window is exactly ACV's finitely-generated-group
  condition with generators `ℓ = (log p)_{p≤e^R}` and the *specific* Lee–Yang polynomial
  being the local Euler factor product `∏_{p≤e^R}(1−z_p)^{−1}` evaluated on `z_p=e^{−ix log p}`.
- **Infinite (W3c):** the whole dual comb is the restriction-from-`∏_p S¹` of the
  Kronecker character; B-mult is the **spatial (Poincaré-section) reading** of that
  restriction, W3d the **dynamical (Kronecker-flow) reading** — "W3c and W3d are the
  same torus seen spatially vs dynamically" (ROADMAP). B-mult is thus the correct
  finite-checkable primitive that **survives the limit `n → ∞`**: it is a per-prime
  local condition, so it does not depend on the (basis-dependent, dense-mod-1)
  windowing that made §9's "is `u ∈ Λ_log`?" test ill-posed.

This is why multiplicativity, not Diophantine separation, is the right primitive:
separation is a *global* metric property of the atom set that degenerates as the
log-primes fill in densely (§9); multiplicativity is a *local, per-generator* property
of the amplitude that is stable under the torus dimension going to infinity.

## W3a.5 The updated matrix row + verdict

The zoo mechanizes B-mult as a new clause `multiplicativity` (variant tag `Bm`),
`check_multiplicativity`: it rebuilds the log-derivative coefficients from each object's
Dirichlet-coefficient model and tests both fingerprints directly. Re-running the full
matrix (T=100):

```
clause \ object                                  zeta     dh   lattice  ksly  random
(A-ii/B-ii) atomic spectrum on prime Lambda_log  COND    FAIL   PASS    PASS   FAIL
(B-iii) weight positivity + decay  [KILLER]      PASS    FAIL   PASS    PASS   FAIL
(B-mult) multiplicative generation [W3a KILLER]  PASS    FAIL   FAIL    FAIL   FAIL
```

**New variant verdict row:**

| Variant | ζ | DH | Eps | Lat | KS-LY | Rnd | Variant verdict |
|---|---|---|---|---|---|---|---|
| **B-mult** multiplicative generation (W3a) | **P** on (B-mult) generation [uncond., Euler product]; **P\*** on (B-ii) pure-point [RH] | **F** (no Euler product ⇒ `b(6)=+1.936 ≠ 0` at composite `log 6`; prime layer sign-varying) | **F** (Epstein `r_Q(n)` not multiplicative; no Euler product) | **F** (no Dirichlet-coefficient / prime-layer structure at all) | **F** (generic Lee–Yang FQ: amplitudes not multiplicatively generated) | **F** (no atomic spectrum) | **SHARPEST** — admits **only ζ**; DH dead by non-multiplicativity; positivity now a *consequence* |

**The KS-FQ interpretation call (honest).** A generic Kurasov–Sarnak Lee–Yang FQ
(the zoo's `ksly`, zeros of `cos x − c`) **FAILS B-mult** — and this is correct and
intended. Its Bragg amplitudes are the Fourier coefficients of a periodic function on a
*single* frequency generator; they are **not** the multiplicative image of a prime
layer (there is no prime-indexed `w(p)` structure at all). So B-mult **excludes generic
Lee–Yang FQs** that B (which only asked for positive mass) admitted. Under B, `ksly`
survives as the positive control that the axiom is non-vacuous; under B-mult it is
**killed**. This makes B-mult **strictly sharper than B**: it carves the *arithmetic*
FQs (those with Euler-product amplitudes) out of the generic Lee–Yang class. This is a
**FEATURE** — the axiom is aimed at zeta's class specifically, not at all FQs — but it
means the "non-vacuity" role that `ksly` played for B must, under B-mult, be played by a
**genuinely arithmetic** FQ (a Dirichlet L-function comb), which is the natural next
positive control (flagged for W3b/W3c). The harness reflects this honestly:
`ksly`'s B-mult verdict is FAIL with detail "no multiplicative prime-layer," and the
governance rail `test_bmult_strictly_sharper_than_b` asserts the B-survives/B-mult-kills
split rather than papering over it.

**Forged negative control (discriminating power).** Corrupting a single amplitude of
zeta's sequence so that `a(6) ≠ a(2)a(3)` (override `a(6)=1.5` on the completely-
multiplicative base) injects a nonzero composite atom `b(6) ≠ 0`; the B-mult verdict
flips PASS → FAIL. This proves the clause is a real function of the amplitude data, not
a descriptor lookup.

## W3a.6 What B-mult buys (verdict memo)

**B-mult + defect-0 (variant D at `k=0`) is the sharpest current candidate for the
"zeta class."** The two live primitives now read:

- **B-mult** (unconditional/arithmetic): the dual comb's amplitudes are the
  multiplicative image of the prime layer — the *Euler-product* fingerprint. Zeta
  satisfies it outright; **every** other zoo object (DH, Epstein, generic FQ, lattice,
  random) fails it. It is the tightest **necessary** arithmetic condition isolated so
  far, and it makes the old positivity killer (B-iii) a **corollary**.
- **Defect-0** (RH-conditional, Alpöge–Furman graded): the dual comb is genuinely
  pure-point with no off-line leakage — the *reality* fingerprint. `k=0 ⟺ RH`.

Their conjunction is the natural axiomatic home of "zeta, and RH": *B-mult pins the
arithmetic (which L-function class), defect-0 pins the analysis (RH within it).*

**The classification-shaped conjecture B-mult suggests (arithmetic Lee–Yang).**

> **Conjecture (arithmetic Lee–Yang, W3a).** Let `μ` be a log-density symmetric ℤ-mass
> atomic measure with pure-point dual comb `μ̂` whose amplitude sequence satisfies
> **(B-mult)** — i.e. is the log-derivative of a completely multiplicative Dirichlet
> series (an Euler product). Then `μ` is the GW image of a degree-1 arithmetic
> L-function, and its support is real (⟺ that L-function satisfies its Riemann
> Hypothesis). In slogan: **multiplicative FQ ⟹ Euler-product structure ⟹ (with
> defect-0) real support.**

This is the B-mult analogue of ACV Cor 1.4 ("every ℕ-FQ is a Lee–Yang zero set"): where
ACV forces *generic* real-rootedness from the finite-torus structure, the arithmetic-
Lee–Yang conjecture would force *arithmeticity* from the multiplicative (infinite-torus)
structure, with RH as the residual defect-0 clause. It is the strongest classification
target the matrix now points at, and it is the precise statement W3c (infinite-torus)
would need to formulate rigorously.

**Honest ledger — definitional vs provable.**

- **Provable now (unconditional, mechanized):** zeta satisfies B-mult (Euler product,
  arithmetic); DH/Epstein/generic-FQ/lattice/random all fail it; positivity is a
  consequence of B-mult. These are the certified zoo verdicts (Arb/interval-trust
  orchestration + exact rational coefficient recursion — **not** a Lean kernel proof).
- **Still definitional:** whether B-mult as stated is the *unique minimal* arithmetic
  primitive, or whether the "completely multiplicative ⟹ degree-1 L-function" step needs
  additional hypotheses (functional equation, conductor bound) to exclude exotic
  Euler-product Dirichlet series. The infinite-torus formulation (W3c) is where this is
  decided; B-mult is its finite-checkable shadow, adjudicated as the primitive but not
  yet proven to be *sufficient* for the classification conjecture.
- **Still RH-hard:** the defect-0 / pure-point clause. B-mult **does not** move it — by
  design. The whole value of the split is that B-mult absorbs *all* the arithmetic
  (unconditional) content, leaving RH cleanly isolated in the defect grading.

`conjecture1_proved = False`.

---

# APPENDIX (v3, W3c) — B-mult-TWISTED: the honest arithmetic-class generalization

*(PROGRAM MIRRORMERE, Wave-3 rung W3c `qc3-torus`. Appended, not rewriting the
v2 appendix. `conjecture1_proved = False`.)*

## W3c.0 Why this appendix exists — the class-not-description objection

The v2 appendix (W3a) adjudicated **multiplicativity** as the primitive and showed
B-mult admits **only ζ** across the then-current zoo `{ζ, DH, lattice, KS-FQ,
random}`. That sharpness is a double-edged sword, and the mission that produced this
appendix stated the edge precisely:

> B-mult is **zeta-UNIQUE** across the zoo. That is either the right sharpness (it
> selects the ARITHMETIC class) or **over-sharpness** (a description of ζ alone,
> which would make the "classification" circular).

The decisive test: **genuine L-functions should pass; DH — their non-multiplicative
linear combination — should keep failing.** If a whole family of arithmetic objects
(not just ζ) passes while DH fails, the clause is a genuine *class* predicate; if
only ζ passes, it is a *description*. W3c ran that test with the two L-functions DH
is literally built from, and the answer is: **class, not description** — but the
clause as stated in v2 needed **one honest generalization to admit them: a unimodular
character twist.**

## W3c.1 The two L-function objects (the experiment)

DH is, verbatim from `arb_dh.py` / `QC_DH_SCOUT.md`,
\[ D(s) \;=\; \tfrac{1-i\kappa}{2}\,L(s,\chi) \;+\; \tfrac{1+i\kappa}{2}\,L(s,\bar\chi),
   \qquad \kappa=\tfrac{\sqrt{10-2\sqrt5}-2}{\sqrt5-1}=0.284079\ldots \]
for the **odd primitive character `χ mod 5`**. With `2` a generator of `(ℤ/5)^*`
(`2¹=2, 2²=4, 2³=3, 2⁴=1`) and the odd character sending the generator to `i`:
\[ \chi = [\chi(1),\chi(2),\chi(3),\chi(4)] = [\,1,\; i,\; -i,\; -1\,],\quad \chi(5)=0. \]
This is verified: `(1-iκ)/2·χ(n) + (1+iκ)/2·χ̄(n)` reproduces exactly the real DH
vector `c=[1, κ, −κ, −1, 0]` (all imaginary parts vanish to machine precision), and
the two-L combination equals the 4-Hurwitz DH driver to `<10⁻²⁰` (mpmath) and
`<10⁻¹²` through the certified FLINT balls.

Each `L(s,χ)` is a **bona-fide degree-1 arithmetic L-function with an Euler product**
`L(s,χ)=∏_p (1−χ(p)p^{−s})^{−1}`. Its prime-side comb is
`−L'/L(s,χ) = Σ_n Λ(n)χ(n) n^{−s}`, so the Bragg amplitudes are
\[ c(m\log p) \;=\; \Lambda(p^m)\,\chi(p)^m\,p^{-m/2} \;=\; (\log p)\,\chi(p)^m\,p^{-m/2}, \]
i.e. **zeta's positive prime layer times a UNIMODULAR twist `χ(p)^m`** (`|χ(p)|=1` on
`(ℤ/5)^*`, `χ(5)=0` at the conductor prime — a trivial local factor, no atom).

New in-worktree driver: `arb_dh.l_chi5_eval(s_re, s_im, prec, conj)` — rigorous
Arb-ball `L(s,χ)`/`L(s,χ̄)` via the same period-5 → Hurwitz collapse as `dh_eval`
(`L(s,χ)=5^{−s}Σ_{a=1}^{4} χ(a)ζ(s,a/5)`).

## W3c.2 The axiom, verbatim (B-mult-twisted)

Let `μ` be a symmetric, log-density, tempered atomic measure ((A-i),(A-iv)) whose
dual comb `μ̂` is pure-point ((B-ii), still RH/GRH-conditional). Write the Bragg
atoms `{(u, c(u)) : u ∈ supp μ̂, u>0}`.

> **[REFUTED 2026-09-19 — see APPENDIX (v4, A1b) at the end of this file. This
> clause is FALSE as an arithmetic-class predicate: it rejects `L(s,Δ)`. It is
> correct only on the GL(1) fiber. Do not build on it un-repaired.]**
>
> **(B-mult-twisted) — Multiplicative amplitude generation with a unimodular twist.**
> The atomic support of `μ̂` is contained in the prime log-lattice
> `Λ_log={±m log p}` with **no atoms at composite (non-prime-power) frequencies**
> (`c(u)=0` for every `u=log n`, `n` composite), and there is a **per-prime twist**
> `t : {primes} → S¹ ∪ {0}` — a value on the unit circle, or `0` at the finitely many
> primes dividing a fixed conductor `q` (ramified: trivial local factor, no atom) —
> such that for every unramified prime `p` and every `m ≥ 1`
> \[ \; c(m\log p) \;=\; (\log p)\, t(p)^m\, p^{-m/2}, \qquad |t(p)|=1. \; \]
> Equivalently: the dual comb is the log-derivative of a **completely multiplicative
> Dirichlet series with unimodular coefficients** — an Euler product
> `∏_p(1−t(p)p^{−s})^{−1}` over the unramified primes. **B-mult (v2) is the special
> case `t(p)≡+1`** (trivial twist); **B-mult-twisted (v3) allows any unimodular
> `t(p)`** — the Dirichlet-character generalization.

**Reading.** "On the prime log-lattice" is still *derived*: it means "the amplitude
sequence is the log-derivative of an Euler product," now allowing the Euler factor to
carry a unit-modulus character. The composite-vanishing `c(log n)=0` is the Euler-
product fingerprint (unchanged from v2). The new content is only in the prime layer:
its modulus is `(log p)p^{−m/2}` (constant-in-`m` modulus `log p` for the raw von-
Mangoldt coefficient `b(p^m)=(log p)t(p)^m`), and its **phase** advances by the fixed
per-prime twist `t(p)`.

**Relation to v2 B-mult and to B-iii (the precise dominance).**
- **B-mult (v2) ⊂ B-mult-twisted (v3):** `t(p)≡1` is the trivial twist.
- **B-mult-twisted ⟹ B-iii positivity ONLY for the trivial twist.** For `t(p)≡+1`
  the prime layer `(log p)p^{−m/2}` is real-positive, so positivity is a *corollary*
  (as in v2). For a **genuinely complex** twist (`t(p)=χ(p)` a nontrivial root of
  unity) the prime layer is **unimodular-complex, not positive-real** — so
  B-mult-twisted holds while **bare (B-iii) positivity FAILS.** This is the crux
  finding: **bare positivity is `t(p)≡+1`-unique, i.e. ζ-unique — over-sharp for the
  arithmetic class.** B-mult-twisted is the corrected primitive; positivity is
  recovered only in the trivial-twist (ζ) fiber.

## W3c.3 The DH refutation, twist-language (which amplitude breaks the law)

DH is `D(s)=Σ_n c(n)n^{−s}`, `c=[1,κ,−κ,−1,0]` period 5. As a **sum** of two Euler
products it is **not itself an Euler product**, so `−D'/D=Σ_n b(n)n^{−s}` is the log-
derivative of a **non-multiplicative** series. Computing `b(n)` from the exact
recursion `a(n)log n=Σ_{d|n} b(d)a(n/d)` (mechanized in the zoo, real coefficients)
gives, certified:

| n | 2 | 3 | 4=2² | 6=2·3 | 9=3² | 25=5² |
|---|---|---|---|---|---|---|
| DH `b(n)`   | +0.1969 | −0.3121 | −1.4422 | **+1.9364** | −2.2859 | 0.0000 |
| ζ `Λ(n)`    | +0.6931 | +1.0986 | +0.6931 | **0.0000**  | +1.0986 | +1.6094 |
| L(χ) `b(n)` | `+0.6931 i` | `−1.0986 i` | `−0.6931` | **0.0000** | `−1.0986` | 0.0000 |

Two independent, certified failures of B-mult-twisted for DH — the **primary** one is
now sharper because we can point at *why the sum breaks it*:

1. **Composite atom (primary kill).** `b(6)=+1.9364 ≠ 0`. B-mult-twisted demands
   `c(log 6)=0`. **Each summand** `L(χ)`, `L(χ̄)` satisfies this (their `b(6)=0`,
   verified above — genuine Euler products); **the sum does not**, because
   multiplicativity is *not preserved under linear combination*. Concretely the DH
   amplitude at `log p` is `(log p)(χ(p)+χ̄(p))p^{−1/2}·(½-type normalization)` and the
   generation to `m=2` fails because, at `p=2,3`,
   \[ (\chi(p)+\bar\chi(p))^2 = 0 \quad\text{but}\quad \chi(p^2)+\bar\chi(p^2) = -2, \]
   (verified: `χ(2)=i ⇒ χ(2)+χ̄(2)=0`, while `χ(4)+χ̄(4)=−2`) — the `m=1` prime-layer
   datum cannot generate the `m=2` datum, so no single twist `t(2)` fits. The cross
   term between the two characters is exactly the composite-frequency leakage `b(6)`.
2. **Real-but-sign-varying prime layer (redundant kill).** `b(2)=+0.197>0` but
   `b(3)=−0.312<0`: no **unimodular** `t(p)` (which would give `|b(p)|=log p`, i.e.
   `|b(2)|=0.693, |b(3)|=1.099`) matches DH's `|b(2)|=0.197, |b(3)|=0.312`. DH's prime
   layer is not even of the `(log p)·(\text{unit})` modulus form.

Either fingerprint kills DH; the zoo trips on (1) first (`b(6)≠0`) and reports it.

## W3c.4 The updated matrix row + the class verdict

The zoo mechanizes B-mult-twisted as the (upgraded) `multiplicativity` clause,
`check_multiplicativity` over **complex** amplitudes with a unimodular-twist test and
ramified-prime handling. Re-running the full matrix (T=100):

```
clause \ object                                  zeta     dh    l_chi5  lattice  ksly  random
(A-ii/B-ii) atomic spectrum on prime Lambda_log  COND    FAIL   COND    PASS    PASS   FAIL
(B-iii) weight positivity + decay  [KILLER]      PASS    FAIL   FAIL    PASS    PASS   FAIL
(B-mult) multiplicative generation [W3a KILLER]  PASS    FAIL   PASS    FAIL    FAIL   FAIL
```

**New/updated variant verdict rows:**

| Variant | ζ | DH | L(χ) | Lat | KS-LY | Rnd | Variant verdict |
|---|---|---|---|---|---|---|---|
| **B** positive (v1) | P (uncond.) / P* (RH) | F | **F** (twist complex ⇒ not positive) | P | P | F | ζ-UNIQUE among Euler products (over-sharp) |
| **B-mult** trivial-twist (v2) | **P** / P* | F | **F** (nontrivial twist) | F | F | F | ζ-UNIQUE (the over-sharpness the objection named) |
| **B-mult-twisted** (v3) | **P** (t≡1) / P* | **F** (sum-of-L, `b(6)≠0`) | **P** (t=χ) / P* (GRH) | F | F | F | **ARITHMETIC CLASS** — admits {ζ, L(χ)}, excludes DH; class predicate, not a description |

The class-not-description question is thereby **settled at the finite-instrument
level**: B-mult-twisted admits at least two genuinely distinct arithmetic objects (ζ
with trivial twist, `L(χ)` with a nontrivial character twist) and excludes DH (their
own non-multiplicative combination) plus every non-arithmetic object. It is a genuine
predicate on the *amplitude sequence's arithmetic type*, not a lookup of ζ.

- **L(χ)'s conditional labels mirror ζ's exactly (honest).** L(χ) is a genuine
  L-function: **support density and temperedness are unconditional PASS**; **atomic-
  spectrum pure-pointness and defect-0 are GRH-CONDITIONAL** (`k=0 ⟺` GRH for `L(χ)`;
  Alpöge–Furman extends to primitive Dirichlet L-functions). L(χ) has **no known off-
  line zeros** — the DH off-line zeros come from the *combination*, not the summands —
  so its defect is `0` conditionally, exactly ζ's status.
- **Forged twist control (discriminating power).** Corrupting a single character
  value (`χ(2): i → 0.5`, breaking both `|χ(2)|=1` and complete multiplicativity)
  flips L(χ)'s B-mult-twisted verdict `PASS → FAIL`. The clause is a real function of
  the character data, not a descriptor.

## W3c.5 What B-mult-twisted buys (verdict memo)

- **The primitive is now provably a class predicate.** v2 left open whether B-mult was
  "ζ or a description of ζ." v3 answers: it is the **arithmetic (Euler-product-with-
  unimodular-twist) class**, i.e. the amplitude side of **degree-1 (`GL(1)`)
  automorphic L-functions** — Dirichlet L-functions. Positivity (B-iii) is the *ζ
  fiber* (trivial twist) of this class, which is why bare positivity looked ζ-unique.
- **The updated classification-shaped conjecture (arithmetic Lee–Yang, v3).**

  > **Conjecture (arithmetic Lee–Yang, W3c).** Let `μ` be a log-density symmetric
  > ℤ-mass atomic measure with pure-point dual comb `μ̂` whose amplitude sequence
  > satisfies **(B-mult-twisted)** — the log-derivative of a completely multiplicative
  > Dirichlet series with unimodular coefficients (an Euler product with a character
  > twist). Then `μ` is the GW image of a degree-1 arithmetic L-function `L(s,χ)`, and
  > its support is real (⟺ that L-function satisfies GRH). Slogan: **twisted-
  > multiplicative FQ ⟹ Dirichlet Euler-product structure ⟹ (with defect-0) real
  > support.**

  This is strictly stronger evidence than the v2 statement: the finite instruments now
  exhibit **two** points of the conjectured class and correctly reject their non-
  multiplicative span. The step "completely-multiplicative-unimodular ⟹ *Dirichlet*
  character (vs an exotic non-arithmetic unimodular sequence)" is where a functional-
  equation / conductor hypothesis is still needed — flagged, not proved (this is the
  `GL(1)` shadow of the Selberg-class classification; see `QC_TORUS_MEMO.md`).

**Honest ledger — definitional vs provable.**

- **Provable now (unconditional, mechanized):** ζ (trivial twist) and `L(χ)`
  (character twist) both satisfy B-mult-twisted; DH — their non-multiplicative sum —
  fails it (`b(6)=+1.936≠0`); bare positivity is the trivial-twist fiber only; all
  certified via Arb/interval orchestration + exact coefficient recursion (**not** a
  Lean kernel proof).
- **Still definitional:** whether "completely-multiplicative unimodular" forces a
  *Dirichlet character* (vs an exotic Euler-product sequence), and whether the class
  extends to `GL(n)` (Satake, non-unimodular `a_p` — see `QC_TORUS_MEMO.md` §Wave-4).
- **Still RH/GRH-hard:** the defect-0 / pure-point clause. B-mult-twisted **does not**
  move it — by design; it absorbs *all* the arithmetic content, leaving GRH isolated
  in the defect grading, uniformly across the class.

`conjecture1_proved = False`.

---

# APPENDIX (v4, A1b) — B-mult-TWISTED IS FALSE: the GL(2) Satake falsification

*(PROGRAM MIRRORMERE, ROUTE A milestone A1b, 2026-09-19. Appended, not rewriting the
v3 appendix. Registry node `MM_satake_degree_two_rejects_delta` (NOT granted — awaiting
independent blind read-back). Kernel module
`examples/quasicrystal/lean/SatakeDegreeTwo.lean`. `conjecture1_proved = False`.)*

## A1b.0 What this appendix does

The v3 appendix settled "class, not description" by exhibiting **two** members, ζ and
`L(s,χ)`. That test was passed with a sample of size two — and both samples were
**degree 1**. This appendix runs the first degree-**2** test, and the clause fails it.

`L(s,Δ)` — Ramanujan's modular discriminant, weight 12, level 1 — is a degree-2 element
of the Selberg class, **tempered by Ramanujan–Petersson, a theorem of Deligne** (Weil I,
Publ. IHES 43, 1974): `|α_p| = |β_p| = 1`. Its comb has the same amplitude-decay profile
as ζ's. It is a genuine member of the arithmetic class (B-mult-twisted) claims to
characterize. **The clause rejects it.** A classification clause that rejects a genuine
member of its own class is false.

## A1b.1 The kernel result — an IFF, not merely a rejection

For a degree-≤2 local factor with Satake parameters `(α,β)` the prime-layer amplitude is
the **Newton power sum**, because `−L'/L` has von-Mangoldt coefficients
`b(p^m) = (log p)·(α^m + β^m)`:

    c(m log p) = (log p)(α^m + β^m) p^{−m/2}.

(B-mult-twisted) demands instead that this be **geometric in a single scalar**,
`(log p) t(p)^m p^{−m/2}`. Kernel theorem (`scalarGenerated_powerSum_iff`, axiom-clean):

> `(∃ t, ∀ m ≥ 1, α^m + β^m = t^m)  ⟺  α·β = 0.`

`m = 1` forces `t = α+β`; `m = 2` then forces `α²+β² = (α+β)²`, i.e. `2αβ = 0`. So the
clause admits **exactly the degenerate degree-≤1 factors** and nothing else. Unitary
normalization of a GL(2) factor is `αβ = 1`, so every GL(2) form is rejected
(`unitary_deg2_not_scalarGenerated`), with the `m = 2` defect exactly `2αβ`
(`deg2_amplitude_defect`) — a constant that does not shrink at any prime for any form.

**The predicate is stronger than the clause.** The Lean predicate drops the clause's own
`|t| = 1` demand, so refuting it refutes the clause a fortiori: the rejection is not an
artifact of unimodularity bookkeeping.

**Anti-vacuity.** `deg1_scalarGenerated` proves the SAME predicate **holds** on the
`β = 0` fiber. That is precisely why ζ (`t = 1`) and `L(s,χ)` (`t = χ(p)`) pass. The
clause's defect is therefore localized at the degree-1 → degree-2 jump — **not** at
unimodularity, **not** at positivity. 14 rfl/simp/decide probes on these statements all
refuse (`ProbeSatake.lean`), CI-gated.

## A1b.2 The Δ instance, with every constant re-derived

τ is **computed** in-kernel from `Δ = q ∏(1−qⁿ)²⁴` by exact truncated integer power
series — no τ value is quoted anywhere — giving `τ(2) = −24`, `τ(4) = −1472`. In the
analytic normalization `λ(n) = τ(n)/n^{11/2}` both `λ(2)² = 9/32` and `λ(4) = −23/32` are
rational, so the Satake determinant is **re-derived**, not assumed, from
`a(p) = α+β` and `a(p²) = α²+αβ+β²`:

    α₂β₂ = λ(2)² − λ(4) = 9/32 + 23/32 = 1   (exactly; `delta_satakeDet_two`).

| quantity at p = 2 | clause demands | `L(s,Δ)` has |
|---|---|---|
| `m = 2` amplitude `α²+β²` | `t² = λ(2)² = 9/32` | `λ(2)² − 2 = −55/32` |
| twist modulus `|t(2)|²` | `1` | `9/32` |

Two independent failures; the defect is exactly `2`. **Anti-phantom:** the Hecke
recursion `τ(4) = τ(2)² − 2¹¹` and coprime multiplicativity `τ(6) = τ(2)τ(3)` are kernel
cross-checks (`tau_hecke_p2`, `tau_mult_six`) and the mirrored Python gate raises rather
than reports. Both fire when the η-exponent 24 is corrupted — verified, not asserted
(`antiphantom_probe.py`, CI-gated).

## A1b.3 The updated matrix (T = 100) — Δ joins the zoo

```
clause \ object                                  zeta     dh    l_chi5   delta   lattice  ksly  random
(A-i/B-i)   support density                      PASS    PASS    PASS     PASS     PASS    PASS   PASS
(A-ii/B-ii) atomic spectrum on prime Lambda_log  COND    FAIL    COND     COND     PASS    PASS   FAIL
(B-iii)     weight positivity          [KILLER]  PASS    FAIL    FAIL     FAIL     PASS    PASS   FAIL
(B-mult-tw) multiplicative generation  [KILLER]  PASS    FAIL    PASS     FAIL     FAIL    FAIL   FAIL
(D-ii)      bounded defect k                     COND    FAIL    COND     COND     PASS    PASS   FAIL
(A-iv..D)   temperedness                         PASS    PASS    PASS     PASS     PASS    PASS   PASS
```

| Variant | ζ | DH | L(χ) | **Δ** | Lat | KS-LY | Rnd | verdict |
|---|---|---|---|---|---|---|---|---|
| **B-mult-twisted** (v3) | P | F | P | **F** | F | F | F | **REFUTED — rejects a genuine degree-2 member** |

**Δ is killed by variant Bm and by Bm alone**; it survives A, C and D exactly as ζ and
`L(s,χ)` do. So the rejection is not Δ being pathological — Δ is unconditionally tempered
and its conditional labels mirror ζ's. The rejection is localized in the arithmetic
clause, which is the whole point. The zoo asserts this as a governance rail and prints
`A1b FALSIFICATION CONFIRMED`; if the clause is ever repaired, that rail is what must
change, deliberately.

## A1b.4 The diagnosis — a degree-1 coincidence promoted to a primitive

At degree 1 the Dirichlet coefficient **equals** the single Satake parameter,
`a_p = α_p`. So "unimodular coefficient" and "unimodular Satake parameter" are the same
condition, and v3 could not tell which one it had written down. It wrote the coefficient
one. At degree ≥ 2 they diverge: Ramanujan–Petersson says `|α_p| = |β_p| = 1` while
`a_p = α_p + β_p` only satisfies `|a_p| ≤ 2`. **The clause kept the wrong one.** The
deeper error is the *shape*: the clause asked the amplitude sequence to be geometric,
which is a rank-1 statement; the truth is that it is a **power sum**, which is geometric
only in rank 1.

## A1b.5 The repair, and what it does and does not buy

**The repair (identified, costed, NOT performed here).** Replace the scalar geometric law
by the degree-`d` Satake power sum:

> **(B-mult-Satake)** there are `α_{1,p},…,α_{d,p}` with `|α_{j,p}| = 1` such that
> `c(m log p) = (log p)(Σ_j α_{j,p}^m) p^{−m/2}` for all `m ≥ 1`.

The **composite-vanishing half** of the clause — the genuine Euler-product fingerprint,
and the half that actually kills DH (`b(6) = +1.9364 ≠ 0`) — survives **unchanged** and is
degree-agnostic. Only the prime layer is rewritten. `d = 1` recovers v3; `t(p) ≡ 1`
recovers v2.

**Cost.** (i) The clause acquires a degree parameter, and the generation law becomes a
Newton/Chebyshev recursion rather than a geometric one, so the finite instrument must
**fit** `d` parameters per prime instead of reading one off `m = 1`. (ii) The zoo's
`check_multiplicativity` gate `|t(p)| = 1` must become "the local inverse polynomial has
all reciprocal roots on the unit circle" — at `d = 2` a discriminant/real-rootedness
test, not a modulus test. This is the same equal-modulus condition the island already
formalized at `n = 2` (`twoFreq_realRooted_iff`), which is a genuine reuse and the reason
this repair is cheap. (iii) An emitter becomes worthwhile at that point (a per-form,
per-prime Satake family); the present node needs none, because the refutation is uniform
in the prime.

**What the repair does NOT buy — state this plainly.** Repairing the clause does not
repair the conjecture it serves. "Unimodular Satake power sums ⇒ automorphic" is the
`GL(n)` Selberg-class classification, bounded below by the **Selberg degree conjecture**,
which has moved exactly one unit interval in thirty years (roadmap A1e,
`open-research`, generational). **The clause is cheaply repairable; the conjecture it
serves is not.** Claiming otherwise would repeat the error this appendix exists to
correct.

## A1b.6 Consequences for the route

- **A1c (primitivity instrument) and A1d (GL(1) fiber theorem) inherit a broken
  premise.** Both were scoped against (B-mult-twisted) as stated. Their statements need
  re-basing on the repaired clause before either is attacked. A1d is the more
  interesting for being *unaffected in substance* — it is explicitly the GL(1) fiber, and
  A1b has now proved that the v3 clause characterizes exactly that fiber, which makes
  A1d's scope precise rather than merely stipulated.
- **The v3 "class, not description" verdict does not survive as stated.** What v3
  established is that the clause admits more than ζ; what A1b establishes is that it
  admits exactly the degree-1 arithmetic objects. That is a *class* — the `GL(1)` class —
  but not the arithmetic class the conjecture needs.

**Honest ledger.**

- **Provable now (unconditional, kernel):** the IFF, the GL(2) rejection, the Δ instance
  with re-derived constants, the anti-vacuity witness. Axiom-clean
  `[propext, Classical.choice, Quot.sound]`.
- **Named input, not formalized:** Ramanujan–Petersson (Deligne) — used ONLY to certify
  that Δ is tempered and hence a legitimate class member. No theorem consumes it.
- **Still open:** the repaired clause's own sufficiency, and the classification
  conjecture (A1e).

`conjecture1_proved = False.` This falsifies a clause in this program's own working
definition. It proves nothing about RH.


# APPENDIX (v5, Dedekind) -- (B-mult-twisted) IS NOT CLOSED UNDER PRODUCTS

*(PROGRAM MIRRORMERE, 2026-09-23. Appended after the v4 A1b appendix. The Delta
falsification needed Deligne to certify class membership; this one needs nothing.
conjecture1_proved = False.)*

## v5.0 The object

`zeta_K(s) = zeta(s) L(s, chi_{-20})` for `K = Q(sqrt(-5))`, discriminant `-20`,
class number `2`. Its Dirichlet coefficients are the ideal counts
`a(n) = sum_{d | n} chi_{-20}(d)`, which the zoo RE-DERIVES and cross-checks, at every
`n <= 60`, against the classical representation-number identity for the two reduced
forms of discriminant `-20`:

    r_{x^2 + 5y^2}(n) + r_{2x^2 + 2xy + 3y^2}(n) = 2 a(n).

The loader refuses to emit if the two derivations disagree (a planted phantom ideal of
norm 6 is refused, and that refusal is a test). No coefficient is quoted.

## v5.1 The verdict

The local factor at `p` is `(1 - p^{-s})^{-1} (1 - chi(p) p^{-s})^{-1}`: Satake pair
`{1, chi(p)}`, unimodular by construction. The prime layer of the log-derivative is
`b(p^m) = (log p)(1 + chi(p)^m)`:

| prime | `chi_{-20}(p)` | `b(p^m)` | clause (B-mult-twisted) |
|---|---|---|---|
| split (3, 7, 23, ...) | `+1` | `2 log p` for every `m` | REJECTED: `|t(p)| = 2 != 1` |
| inert (11, 13, 17, 19, ...) | `-1` | `0` (odd `m`), `2 log p` (even `m`) | REJECTED: inconsistent vanishing |
| ramified (2, 5) | `0` | `log p` | admitted (degree-1 fiber) |

The harness trips at the first split prime: `|t(3)| = 2.0000 != 1`. Meanwhile `zeta`
PASSES the clause and `L(s, chi_{-20})` PASSES it (a real character: twists `+1`/`-1`,
ramified primes `[2, 5]` reported as atom-free). So the clause admits both factors and
rejects their product. The Selberg class is closed under products; a predicate meant to
carve out an arithmetic subclass of it cannot fail closure under products.

Bare (B-iii) positivity also fails `zeta_K`, for a THIRD distinct reason: its layer is
real and nonnegative (`Lambda_K >= 0`, never sign-varying), but it vanishes at every odd
power of an inert prime and is doubled at split primes. Half the prime log-lattice
carries no atom.

## v5.2 The kernel companion

`examples/quasicrystal/lean/DedekindQuadratic.lean` (in the island's default targets
and axiom guard, three standard axioms):

* `dedekind_split_rejected`, `dedekind_inert_rejected`: the pairs `{1, 1}` and `{1, -1}`
  are not scalar-generated (instances of `scalarGenerated_powerSum_iff`);
* `dedekind_ramified_admitted`: the pair `{1, 0}` is (the anti-vacuity fiber);
* `dedekind_inert_layer_odd` / `_even`: the inert layer is `0` at odd and `2` at even `m`;
* `layer_of_product` + `scalarGenerated_not_closed_under_product`: the layer of the
  product is the sum of the factors' layers (for `m >= 1`), each scalar-generated, and
  the sum is not, for every `chi(p) != 0`;
* `chi_m20_three = 1`, `chi_m20_eleven = -1` by `norm_num` on the Jacobi symbol, and
  `dedekind_at_three_rejected` / `dedekind_at_eleven_rejected` instantiate the
  rejection with the character values computed in-kernel.

## v5.3 The matrix (T = 100) -- zeta_K joins the zoo

Same verdict profile as `zeta`, `l_chi5` and `delta` on every non-arithmetic clause
(support density PASS, temperedness PASS, pure-point spectrum and defect CONDITIONAL
on GRH), killed by variant B-mult alone, survives A, C, D. The forged twin that drops
the `L(chi)` factor (hands the same code path the coefficient vector of `zeta`) flips
FAIL -> PASS, so the rejection is exactly the second Satake parameter.

## v5.4 What this changes

Nothing about RH. It sharpens A1b: the clause's defect is not an artifact of GL(2)
automorphic forms or of Deligne's theorem; it already shows up for the simplest
degree-2 Euler product there is, and it shows up as a failure of product closure. Any
repaired clause must be checked against `zeta_K` first, because `zeta_K` is the
cheapest member of the class that a GL(1) predicate rejects.
