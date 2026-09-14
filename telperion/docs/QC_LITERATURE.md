# QC_LITERATURE.md — Literature Ground Truth for PROGRAM MIRRORMERE

> **`conjecture1_proved = False`.** This is a survey of existing mathematics, not
> new mathematics and not a proof of the Riemann Hypothesis. Every statement below
> is a report of published work with citation; where a statement is a *conjecture*
> (Dyson's program, the rigidity strengthenings) or could not be verified to the
> program's precision standard, it is marked as such explicitly. The reverse-Dyson
> derivation is a research program; RH remains open.

**Agent:** `qc-lit` (Wave A, MIRRORMERE). **Deliverable A1.** No code, no Lean.
**Method:** WebSearch + WebFetch; each central statement cross-checked against ≥2
independent sources (paper abstract/body + survey, or paper + journal metadata).
Several arXiv PDFs would not render as text through the fetch tool (binary); for
those the statement was recovered from the HTML (`arxiv.org/html/...`), the abstract
page, and a corroborating survey/journal record — flagged per item.

---

## §0. The one-paragraph map (read this first)

Dyson (2009) observed: **if RH holds, the multiset of nontrivial zeta zeros is a
one-dimensional "quasicrystal"** — a discrete point measure on a line whose Fourier
transform is again a discrete point measure, supported at `{±m log p}`. He proposed
*classifying all one-dimensional quasicrystals* and finding zeta among them. Since
then the classification of the *well-behaved* one-dimensional objects (Fourier
quasicrystals with ℕ-valued / unit masses) has been **completed**: they are exactly
the zero sets of Lee–Yang real-rooted exponential polynomials (Kurasov–Sarnak
construct → Olevskii–Ulanovskii converse → Alon–Cohen–Vinzant close the loop). **The
zeta comb is not in this class** — it violates uniform discreteness (gaps →0) and
bounded density (density ~ log T), and Weil's explicit-formula measure is not even a
crystalline measure in the strict sense. So the reverse-Dyson program is *not*
"apply the completed classification to zeta" (that classification's hypotheses zeta
fails); it is to find the *right generalized axiom class* whose zeta instance exists
**iff RH**, and in which off-line zeros must violate a specific, checkable property.
The Alpöge–Furman (2026) inertia/rank-trace machinery is the concrete instrument for
"off-line zero ⇒ signature-(1,1) defect," the wedge/defect-k reading (Pillar 3).

---

## §1. Exact statements

### 1.1 Kurasov–Sarnak — stable-polynomial / Lee–Yang construction

- **Reference.** P. Kurasov and P. Sarnak, *Stable polynomials and crystalline
  measures*, **J. Math. Phys. 61 (2020), no. 8, 083501**, 13–15 pp.
  DOI `10.1063/5.0012286`. arXiv **2004.05678** (submitted 12 Apr 2020).
  (Special issue celebrating J. Bourgain.)
- **What they construct (verbatim abstract):** *"Explicit examples of **positive**
  crystalline measures and Fourier quasicrystals are constructed using pairs of
  stable polynomials, answering several open questions in the area."*
- **Precise content.** From a Lee–Yang polynomial `p(z_1,…,z_n)` (no zeros in `𝔻ⁿ`
  nor in `(ℂ∖𝔻̄)ⁿ`) and a positive frequency vector `ℓ ∈ ℝ₊ⁿ` with ℚ-linearly
  independent entries, the counting measure of the real zeros (with multiplicity) of
  the one-variable restriction `x ↦ p(e^{i x ℓ_1},…,e^{i x ℓ_n})` is an **ℕ-valued
  Fourier quasicrystal**: support discrete, unit/integer masses, and the Fourier
  transform is a discrete (pure-point) tempered measure with spectrum in the finitely
  generated group `ℤ⟨ℓ_1,…,ℓ_n⟩`. In particular they produce a **non-periodic FQ with
  unit coefficients and uniformly discrete support** — answering a question of Meyer.
- **Cross-check.** Abstract + journal metadata (AIP, arXiv, Princeton "Collaborate"
  record) agree on venue/DOI; the construction description corroborated verbatim by
  the Alon–Vinzant 2023 abstract ("Kurasov and Sarnak provides a method for
  constructing one-dimensional Fourier quasicrystals from the torus zero sets of …
  Lee-Yang polynomials … a non-periodic FQ with unit coefficients and uniformly
  discrete support, answering an open question posed by Meyer").
- **Precision flag.** Exact numbered theorem statements from the body not fetched
  (PDF binary; HTML n/a for this JMP paper). The construction/hypotheses above are
  confirmed by three independent secondary sources but the *verbatim theorem number*
  is not pinned. **Get the JMP PDF locally for B2 before formalizing the construction.**

### 1.2 Olevskii–Ulanovskii — the converse (1-D), and rigidity lineage

- **Converse reference.** A. Olevskii and A. Ulanovskii, *Fourier quasicrystals with
  unit masses*, **C. R. Math. Acad. Sci. Paris 358 (2020), no. 11–12, 1207–1211**.
  DOI `10.5802/crmath.142`. arXiv **2009.12810**.
- **Exact main result (as stated by the paper / Numdam record).** *"The sum of
  δ-measures sitting at the points of a discrete set `Λ ⊂ ℝ` forms a Fourier
  quasicrystal if and only if `Λ` is the zero set of an exponential polynomial with
  imaginary frequencies"* — i.e. `Λ = {x : f(x)=0}` for `f(x)=Σ_j c_j e^{i ω_j x}`,
  `ω_j ∈ ℝ`, all of whose zeros are **real** (a "real-rooted"/"real-zero" exponential
  polynomial), with multiplicities matching the masses. Hypotheses: `Λ` discrete,
  **unit masses**; conclusion is the two-way equivalence with real-rooted exponential
  sums. This is the converse to §1.1 and the direct 1-D input to §1.3.
- **Companion: "A Simple Crystalline Measure."** A. Olevskii and A. Ulanovskii,
  arXiv **2006.12037** (2020). Explicit elementary construction of a non-trivial
  crystalline measure. Useful as a *control object* for the zoo (B1).
- **Rigidity (Lev–Olevskii).** N. Lev and A. Olevskii, *Quasicrystals and Poisson's
  summation formula*, **Invent. Math. 200 (2015), 585–606** (arXiv **1312.6884**,
  Dec 2013). **[Charter said "Annals" — CORRECTION: it is Inventiones 2015, not
  Annals.]** Statement: **a measure on ℝ (and ℝⁿ) with both support and spectrum
  *uniformly discrete* is, essentially, a finite combination of Dirac combs of
  lattices** (periodic structure). The uniform-discreteness of *both* sides is
  load-bearing: dropping it is exactly what admits the Kurasov–Sarnak non-periodic
  FQs (uniformly discrete support, but spectrum only *countable/dense*, not uniformly
  discrete) and Meyer's crystalline measures. See also N. Lev, A. Olevskii, *Fourier
  quasicrystals and Poisson summation* line of work (TAU "Fourier quasicrystals").
- **Cross-check.** Numdam article page + arXiv 2009.12810 for the converse; Springer
  Invent. Math. record + arXiv 1312.6884 for rigidity; multiple survey mentions
  concur on the "uniformly discrete both sides ⇒ periodic" statement.

### 1.3 THE PILLAR-2 ANCHOR — Alon–Cohen–Vinzant, the 1-D characterization

- **Reference.** L. Alon, A. Cohen, C. Vinzant, *Every real-rooted exponential
  polynomial is the restriction of a Lee–Yang polynomial*, **J. Funct. Anal.**
  (2024), DOI `10.1016/j.jfa.2023.110226`. arXiv **2303.03201** (v1 6 Mar 2023,
  v3 8 Oct 2024).
- **Definitions used (verbatim / near-verbatim from HTML).**
  - *Lee–Yang polynomial:* `p(z_1,…,z_n)` with **no zeros in `𝔻ⁿ` and none in
    `(ℂ∖𝔻̄)ⁿ`** (the open polydisc and the "inverse" polydisc).
  - *Fourier quasicrystal:* a **crystalline measure `μ` with both `|μ|` and `|μ̂|`
    tempered**. *Crystalline measure:* a **discrete (locally finite, atomic) tempered
    measure whose distributional Fourier transform is also a discrete measure.**
  - *ℕ-valued FQ:* an FQ whose atoms carry masses in `ℕ` (a *counting measure* of a
    multiset).
- **Main theorem (Theorem 1.1, verbatim from HTML).**
  > Let `f(x) = Σ_{j=0}^{s} c_j e^{λ_j x}` where `c_0,…,c_s ∈ ℂ*` and
  > `λ_0,…,λ_s ∈ ℂ`, ordered so that `Im(λ_0) = min_{0≤j≤s} Im(λ_j)`. Let
  > `n = dim_ℚ {Im(λ_1−λ_0),…,Im(λ_s−λ_0)}`. If `f(x)` is real rooted, then there is
  > a Lee–Yang polynomial `p ∈ ℂ[z_1,…,z_n]` and `ℓ ∈ ℝ₊ⁿ` such that
  > `f(x) = e^{λ_0 x} p(exp(i x ℓ))`, and the entries of `ℓ` are ℚ-linearly
  > independent.
- **The characterization (Corollary 1.4, verbatim from HTML).**
  > A measure `μ` on ℝ is an **ℕ-valued Fourier quasicrystal if and only if
  > `μ = μ_{p,ℓ}`** for some Lee–Yang polynomial `p(z_1,…,z_n)` and positive
  > frequencies `ℓ ∈ ℝ₊ⁿ`.
  (`μ_{p,ℓ}` = counting measure of the real zeros of `x ↦ p(e^{i x ℓ})`.)
- **What "closes the loop."** KS (§1.1) gives ⇐ (Lee–Yang ⇒ FQ). O–U (§1.2) gives
  the 1-D converse in exponential-polynomial language. ACV upgrade every real-rooted
  *exponential polynomial* to a *restriction of a genuinely Lee–Yang multivariate
  polynomial*, which (with O–U) yields the clean iff **Cor 1.4**. Their own abstract:
  *"Together with previous work by Olevskii and Ulanovskii, this implies that the
  Kurasov–Sarnak construction of ℕ-valued Fourier quasicrystals from stable
  polynomials comprises every possible ℕ-valued Fourier quasicrystal."*
- **Hypotheses that matter for MIRRORMERE (this is the crux).** The classification is
  for **ℕ-valued (unit/integer-mass) Fourier quasicrystals**. It bundles:
  (i) **atoms with ℕ masses** (a counting measure of a multiset);
  (ii) **discrete support** and **`|μ|` tempered** (polynomially bounded density);
  (iii) **`|μ̂|` tempered** — the DUAL comb also tempered (the FQ, not merely
  crystalline, condition);
  (iv) the spectrum lies in a **finitely generated group** `ℤ⟨ℓ⟩` of frequencies.
  It does **not** require uniform discreteness — that's a *further* generic property
  studied separately (§1.6). Anshul **Adve** does not appear as an author of the 1-D
  characterization; see §1.6/§4 for where his name is (mis)attached.
- **Cross-check.** HTML body (Thm 1.1, Cor 1.4) + arXiv abstract + J. Funct. Anal.
  DOI + Alon–Vinzant 2023 abstract's summary ("later shown to generate all
  one-dimensional Fourier quasicrystals with ℕ-valued coefficients"). Three
  independent corroborations of the iff.

### 1.4 Higher-dimensional Lee–Yang varieties (context, not 1-D critical path)

- **Reference.** L. Alon, M. Kummer, P. Kurasov, C. Vinzant, *Higher dimensional
  Fourier quasicrystals from Lee–Yang varieties*, **Invent. Math. 239 (2025),
  321–376**. arXiv **2407.11184**; DOI `10.1007/s00222-024-01307-8`.
- **Content.** Constructs unit-mass FQs in arbitrary dimension from complex algebraic
  varieties avoiding certain regions of `ℂⁿ` (generalizing Lee–Yang hypersurfaces).
  Notable structural theorems reported: FQ supports are **Delone almost-periodic**
  and have **at most finite intersection with any discrete periodic set**; and (a
  theorem quoted as **Thm 2.9**) *if a discrete set `Λ ⊆ ℝ^d` is a Fourier
  quasicrystal then it is **stealthy hyperuniform**.* Relevance: the "stealthy
  hyperuniform / structured" rigidity is exactly the kind of property the zeta comb
  should be shown to *lack or satisfy-only-conditionally*.
- **Cross-check.** Springer Invent. Math. record + arXiv 2407.11184 + IAS talk page.
  **Precision flag:** Thm 2.9 number recovered from a secondary summary; verify
  against PDF before citing the number in the paper/ledger.

### 1.5 Meyer — crystalline measures (older + the 2016 revival)

- **Reference.** Y. Meyer, *Measures with locally finite support and spectrum*,
  **PNAS 113 (2016), no. 12, 3152–3158** (MR3482845). Related survey material in
  Y. Meyer, *Curved model sets and crystalline measures* (Springer, 2020).
- **Content.** A **crystalline measure** = atomic measure on a locally finite set
  whose distributional Fourier transform is also atomic on a locally finite set.
  Meyer's driving question: *is the Poisson summation formula essentially unique, or
  is there a wider class?* He constructs measures `μ` on ℝⁿ that are (i) sums of
  weighted Diracs on a locally finite set, (ii) with `μ̂` also such a sum, and
  (iii) **not** generalized Dirac combs — establishing the class is strictly richer
  than lattice combs. This is the historical root of the whole subject and the source
  of the "is zeta such a measure?" question in modern language.
- **Cross-check.** PNAS DOI `10.1073/pnas.1600685113` + EMS/ADS records + multiple
  survey citations agree on the (i)–(iii) content.

### 1.6 Generic uniform discreteness, gap distributions, and the crystalline ⊋ FQ gap

- **Gap distributions.** L. Alon, C. Vinzant, *Gap distributions of Fourier
  quasicrystals via Lee–Yang polynomials*, arXiv **2307.13498** [math-ph]
  (Jul 2023). **Abstract (verbatim):** *"…they provided a non-periodic FQ with unit
  coefficients and uniformly discrete support, answering an open question posed by
  Meyer. Their method was later shown to generate all one-dimensional Fourier
  quasicrystals with ℕ-valued coefficients (ℕ-FQ). In this paper, we characterize
  which Lee–Yang polynomials give rise to non-periodic ℕ-FQs with unit coefficients
  and uniformly discrete support, and show that this property is generic among
  Lee–Yang polynomials. We also show that the infinite sequence of gaps between
  consecutive atoms of any ℕ-FQ has a well-defined distribution, which, under mild
  conditions, is absolutely continuous."* **Program relevance:** every ℕ-FQ has a
  *well-defined limiting gap distribution*. The zeta comb's normalized gaps have GUE
  (Montgomery–Odlyzko) statistics — a well-defined distribution — but its *unnormalized*
  gaps shrink to 0 (density grows), so it fails the uniform-discreteness that is
  *generic* here. This is a concrete "escape."
- **The crystalline ⊋ FQ separation.** S. Favorov, *The crystalline measure that is
  not a Fourier Quasicrystal*, arXiv **2401.01121** (Jan 2024). Abstract (verbatim):
  *"We construct a crystalline measure on the real line, which is not a Fourier
  Quasicrystal."* **This pins the exact class gap:** *crystalline* requires `μ` and
  `μ̂` discrete-and-tempered; *Fourier quasicrystal* additionally requires **`|μ|`
  and `|μ̂|` (the total-variation / absolute-value combs) tempered.** A measure can be
  crystalline yet have `|μ̂|` non-tempered → not an FQ. **This is the precise hook for
  the zeta comb** (see §2, §3): the archimedean/error terms in the explicit formula
  are exactly what threatens temperedness of the absolute dual comb.
- **"Adve" attribution — RESOLVED (B4 re-check, 2026-09-14).** There is no Adve
  theorem in this orbit: arXiv 2203.06733 is **Favorov (sole author)**; the 1-D iff
  is ACV + O–U + KS as above, and the bounded-density rigidity in that orbit is
  Favorov's (uniform-discreteness hypothesis — off zeta's path). The "Adve"
  name in the program charter was a hallucinated attribution; do not cite it.

### 1.7 The Weil explicit formula as a (near-)crystalline measure — the Dyson lineage

- **Origin.** F. Dyson, *Birds and Frogs*, **Notices AMS 56 (2009), no. 2,
  212–223**. **Verbatim definition:** *"A quasi-crystal is a distribution of discrete
  point masses whose Fourier transform is a distribution of discrete point
  frequencies"* — *"a pure point distribution that has a pure point spectrum."*
  **Verbatim RH claim:** *"If the Riemann hypothesis is true, then the zeros of the
  zeta-function form a one-dimensional quasi-crystal according to the definition. They
  constitute a distribution of point masses on a straight line, and their Fourier
  transform is likewise a distribution of point masses, one at each of the logarithms
  of ordinary prime numbers and prime-power numbers."* **Verbatim program:** *"Let us
  try to obtain a complete enumeration and classification of one-dimensional
  quasi-crystals. That is to say, we enumerate and classify all point distributions
  that have a discrete point spectrum."* → then find zeta among them ⇒ RH.
- **Survey framing.** J. Lagarias, *Mathematical quasicrystals and the problem of
  diffraction*, in *Directions in Mathematical Quasicrystals* (Baake–Moody, eds.),
  CRM Monograph Ser. 13, AMS 2000, pp. 61–93. Frames "which Dirac combs have discrete
  FT" and is the standard reference for the definitional landscape Dyson invokes.
- **The honest caveat (load-bearing for the whole program).** Multiple sources state
  that **the measures underlying Weil's 1952 explicit formula are NOT crystalline
  measures in the strict Meyer/KS sense** — the zero side is not a bona-fide
  tempered *measure* summable as `Σ δ_γ` without the archimedean term and a
  regularizing test function; the "prime comb" `Σ (log p) δ_{m log p}` and the "zero
  comb" `Σ δ_γ` are paired only *through* the explicit formula with its
  Γ-factor/archimedean contribution and error control. **So the naïve "zeta zeros are
  a crystalline measure" is false as stated; it becomes a precise statement only after
  choosing the regularization, and its FQ-grade (temperedness of the absolute dual)
  is exactly what RH governs.** This is the single most important nuance in §1 for the
  axiom design (A2) and the rigidity memo (B4).
- **Follow-ups (Weil-form ↔ finite matrices).** "Construction of Finite Hilbert–Pólya
  Matrices from Weil's Explicit Formula" (arXiv **2609.04908**) and "A probabilistic
  interpretation of Weil's explicit sums and arithmetic spectral measures"
  (arXiv **2311.08519**) treat finite compressions / spectral-measure readings of the
  explicit formula — the same "finite compression of Weil's Hermitian form" object
  the Alpöge–Furman argument uses (§1.8). **Precision flag:** I did not verify a
  paper that literally proves "RH ⇔ temperedness of the dual comb"; the closest is
  the Dyson/Lagarias framing plus the crystalline-vs-FQ temperedness distinction
  (§1.6). Treat "RH ⇔ dual-comb temperedness" as a **program conjecture to be made
  precise (A2/B4), not a cited theorem.**

### 1.8 Alpöge–Furman — the wedge instrument (Pillar 3 anchor)

- **Reference.** L. Alpöge, R. Furman, *More than two thirds of the zeros of the
  Riemann zeta function are simple and on the critical line*, arXiv **2608.13637**
  (2026). *"formally verified in Lean 4."* Argument credited as autonomously
  discovered by Claude (Anthropic); public formalization at
  `github.com/anthropics/formal-math`, project `zeta23/` (Lean v4.33.0-rc2), per the
  MIRRORMERE charter's feasibility pre-check. **Abstract (verbatim):** *"…the Riemann
  hypothesis, classically needed to read the zero side as a positive sum over real
  ordinates, is replaced by a rank-trace inequality applied to a finite compression
  of Weil's Hermitian form, with Sylvester's law of inertia handling off-line pairs.
  … The results extend to primitive Dirichlet L-functions and are formally verified
  in Lean 4."* (Note: a *second, distinct* paper arXiv **2609.02882**, "A new proof
  that more than 2/3 …", gives the 0.6725/0.8362 improvements — same circle, verify
  which the D4/zeta-23 Lean port tracks.)
- **§2/§3 lemma statements (verbatim from HTML).**
  - **Finite compression of Weil's form (§2.3):** the `d×d` real symmetric matrix
    `G̃ := (a L²)⁻¹ Σ_{Re γ_ρ ∈ I'} m_ρ v_ρ v_ρᵀ`, where
    `v_ρ := (φ̂(γ_ρ − α_k))_{0≤k<d} ∈ ℂᵈ` and `I' := [T−√T, 2T+√T)`.
  - **Lemma 3.1 (Inertia under pull-back):** *"Let `Q_0` be a Hermitian form on `ℂᵐ`
    and `A : ℂᵈ → ℂᵐ` linear. Then `n₊(A*Q_0 A) ≤ n₊(Q_0)`."* (Sylvester monotonicity
    of the positive index under compression.)
  - **Lemma 3.2 (Rank–trace inequality):** for Hermitian `P,Q` with `P ⪰ 0`,
    `rank P ≤ r`, `n₊(Q) ≤ b`:
    `r ≥ 2·tr P + 4·tr Q − 4b − ‖P+Q‖²_{HS}`.
  - **Proposition 4.1 (off-line pair ⇒ indefinite block):** each off-line pair
    `{ρ, 1−ρ̄}` contributes *"a block of signature `(1,1)` to `Q`"*; explicitly, with
    `v_ρ = a + i b` (`a,b ∈ ℝᵈ`),
    `m_ρ(v_ρ v_ρᵀ + v_{ρ̄} v_{ρ̄}ᵀ) = 2 m_ρ (a aᵀ − b bᵀ)`, the pull-back of
    `m_ρ · diag(1,−1)`.
- **The wedge reading (for B3).** An off-line zero is *forced* to contribute a
  **signature-(1,1) (indefinite) defect** to the compressed Weil form; RH ⇔ *no such
  indefinite blocks* ⇔ the compressed form is positive-semidefinite. This is precisely
  "crystalline up to defect k = number of off-line pairs," and the certified
  perturbation experiment (B3) is to *measure* the `(1,1)` leakage at finite `T` as a
  kernel object. **This §1.8 is the exact input the charter's B3 asks for.**
- **Cross-check.** HTML body (Lemmas 3.1/3.2, Prop 4.1, §2.3) + arXiv abstract; the
  substitution "RH replaced by rank-trace + Sylvester inertia" appears verbatim in
  the abstract and is corroborated by the secondary summary. Repo/Lean provenance per
  charter pre-check (not independently re-cloned here).

---

## §2. THE TABLE — where the zeta comb escapes each hypothesis

**Zeta-comb facts used (all cross-checked):**
- Counting function `N(T) = (T/2π) log(T/2π) − T/2π + O(log T)` (Riemann–von
  Mangoldt). → **density GROWS ~ (1/2π) log(T/2π)**, not bounded.
- Average gap between consecutive ordinates `~ 2π / log(γ/2π) → 0`. → **NOT uniformly
  discrete** (no positive lower bound on gaps).
- Conjectural spectrum of the dual comb: `{±m log p : p prime, m ≥ 1}`, which is
  **dense in ℝ** (log-lattice, countable, non-uniformly-discrete).
- Explicit-formula weights on the dual: `(log p) · p^{−m/2}` (von Mangoldt Λ against
  the `s ↦ 1/2 + it` normalization) — decaying but summed against a test function,
  not a stand-alone tempered measure.
- **Temperedness of the *absolute* dual comb is the RH-sensitive grade** (off-line
  zeros ⇒ terms `p^{−β}` with `β ≠ 1/2` ⇒ growth mismatch).

Legend: **SAT** = zeta satisfies; **VIOL** = violates (reason); **RH?** = holds iff
(or is governed by) RH — the point where the program lives.

| Theorem / hypothesis | Support **uniformly discrete** | Support **bounded density** | Spectrum **uniformly discrete** | `μ` (support) **tempered** | `μ̂` **discrete** | `|μ̂|` (abs. dual) **tempered** | Masses **ℕ / unit** | Zeta's status |
|---|---|---|---|---|---|---|---|---|
| **Lev–Olevskii rigidity** (§1.2): both sides unif. discrete ⇒ periodic | **VIOL** (gaps→0) | — | **VIOL** ({m log p} dense) | — | — | — | — | Hypothesis fails on *both* sides ⇒ rigidity says nothing; zeta is *not* forced periodic. Escapes by failing uniform discreteness on both comb and dual. |
| **KS / ACV ℕ-FQ classification** (§1.1,§1.3): ℕ-FQ ⇔ Lee–Yang zero set | not required | **VIOL** (density~log T ⇒ `|μ|` grows super-poly? see note) | not required | **SAT?** (as counting measure, poly-bounded) | **RH?** (dual discrete needs the primes side to be a genuine measure) | **RH?** | **SAT** (zeros counted w/ mult., ℕ masses) | Zeta comb is **not an ℕ-FQ**: even granting RH, the density growth + primes-side-not-a-tempered-measure break the FQ (not merely crystalline) grade. This is why the *completed* classification does **not** apply to zeta. |
| **Meyer crystalline** (§1.5): `μ`,`μ̂` atomic on locally finite sets | not required | not required | not required | SAT (locally finite) | **RH?/VIOL** | not required | integer | Weil measure is **not crystalline in the strict sense** (needs archimedean term + regularization); becomes a statement only after regularizing. |
| **Favorov separation** (§1.6): crystalline but not FQ ⇔ `|μ̂|` non-tempered | — | — | — | — | — | **the discriminator** | — | Zeta is the *motivating* candidate on the crystalline-but-not-FQ side: off-line zeros threaten `|μ̂|` temperedness. **RH? — this cell is the target equivalence.** |
| **Alon–Vinzant gap law** (§1.6): every ℕ-FQ has well-defined gap distribution | generic **SAT** for ℕ-FQ | — | — | — | — | — | — | Zeta has a well-defined *normalized* (GUE) gap law but **VIOL** uniform discreteness of raw gaps ⇒ not covered as an ℕ-FQ. |
| **AKKV higher-dim** (§1.4): FQ ⇒ Delone almost-periodic & stealthy hyperuniform | **VIOL** (not Delone: gaps→0) | **VIOL** | — | — | — | — | — | Zeta comb is not Delone (fails the uniform lower gap bound), so the FQ⇒Delone direction excludes it. |
| **Alpöge–Furman inertia** (§1.8): off-line pair ⇒ signature-(1,1) block | — | — | — | — | — | — | — | **RH? made finite:** RH ⇔ no `(1,1)` indefinite blocks in the compressed Weil form. The defect *is* the off-line count. This is the wedge/defect-k axis. |

**Note on "bounded density."** The FQ definition requires `|μ|` *tempered* (polynomial
growth of `|μ|([−R,R])`), which zeta's `N(T)~ (T/2π) log T` **does** satisfy (log-times-
linear is polynomially bounded). The genuine obstruction is **(a) uniform discreteness
(gaps→0)** and **(b) temperedness/discreteness of the *dual* comb `|μ̂|`, which is
RH-sensitive**. So the crisp "escape" is: *zeta is (at best, under RH) a crystalline-
type object that fails uniform discreteness and whose FQ-grade — temperedness of the
absolute dual — is exactly the RH content.* Do not overstate (a) as a temperedness
failure of `|μ|`; it is a Delone/uniform-discreteness failure.

---

## §3. Wedge-relevant notes (Pillar 3 feed to B3)

1. **Defect = signature.** Alpöge–Furman (§1.8) give the exact dictionary: off-line
   zeros ↦ indefinite `(1,1)` blocks in the finite compression `G̃` of Weil's form.
   "Crystalline up to defect `k`" ↔ "compressed Weil form has negative index `≤ k`"
   ↔ "`≤ k` off-line pairs in the window." B3's certified perturbation experiment
   (synthetic off-line pair at `β ≠ 1/2`) should target a kernel enclosure of the
   `n₋(G̃) ≥ 1` contribution — the measured `(1,1)` leakage.
2. **Partial/defect positivity in the literature.** The rank-trace inequality
   (Lemma 3.2) is a *quantitative partial-positivity* statement: it converts a bound
   on the negative index (`n₊(Q) ≤ b`, i.e. few off-line pairs) into a rank/multiplicity
   count. This is the formal shape of "partial Weil positivity ⇒ wedge." The
   dictionary B3 must state connects `posIndex/signature` of the D4/zeta-23 finite
   Weil–Gram bricks to this `n₊/n₋` language.
3. **Complex-supported / defect-tolerant crystallinity.** Direct hits are thin. The
   Favorov separation (§1.6) is the cleanest *defect-tolerant* result (crystalline but
   not FQ). **CORRECTION (B4 re-check, 2026-09-14): strip-supported FQ theory is NOT
   virgin territory.** Favorov–Değer (arXiv 2605.10766, May 2026; also 2408.09563)
   own the strip-FQ category: their result is a **growth dichotomy** under a
   per-window ℤ-independence hypothesis — it does NOT force support onto ℝ (an
   automated summary claiming reality-forcing was checked against the verbatim
   abstract and discarded). The program's R1/R2 conjectures must be positioned as
   the **arithmetic-spectrum + defect-graded specialization** of the Favorov–Değer
   program and cite them; the *reality-forcing* question in the arithmetic
   specialization remains open, and the inertia instrument gives it a finite test.
4. **Regularization is mandatory.** Any axiom set (A2) that treats the zeta zero comb
   as a bare crystalline measure is DEAD on arrival (§1.7): the explicit formula pairs
   the combs only through the archimedean Γ-factor and a test function. The axiom must
   be stated at the level of the *paired* (comb, dual, archimedean-corrected) triple,
   or as temperedness of a *specific regularized* dual.

---

## §4. Open questions, ranked by attackability (feed to B4 = qc-rigidity)

1. **[most attackable] Toy strip-rigidity for finite exponential sums / Dirichlet
   polynomials.** Does real-rootedness of a *finite* exponential sum force its zero
   comb into the Lee–Yang class with no complex-support defect? ACV Thm 1.1 (§1.3) is
   essentially the machinery; a clean *finite/Dirichlet-polynomial* strip-rigidity toy
   theorem looks reachable in the B2 Lean island using zero-reality lemmas. **Direct
   B4 toy-case candidate.**
2. **Make "RH ⇔ temperedness of the dual comb" precise.** No cited theorem states it;
   §1.6 (Favorov) + §1.7 (Dyson/Lagarias) give the pieces. Formulate the exact
   regularized statement and its DH test (DH must *fail* the hypothesis — it has
   off-line zeros). **This is A2's central axiom candidate; B4 states it at 3
   strengths: full strip-rigidity / defect-k / spectrum-restricted.**
3. **Defect-k crystallinity via inertia (bridge to B3).** State precisely: "a comb is
   crystalline-up-to-defect-k iff its compressed Weil form has negative index ≤ k."
   Prove the easy direction (finite compression) in kernel; leave the converse as a
   named Prop. **Gated on §1.8 dictionary; jointly owned with B3.**
4. ~~**Resolve the "Adve" attribution**~~ **RESOLVED** (§1.6): no such theorem;
   arXiv 2203.06733 is Favorov sole-author. Remaining sub-question only: whether any
   generalized-FQ work weakens the ℕ-valued restriction (which would matter for whether
   a *ℝ-valued* or signed zeta comb is in scope). **Unverified — do not build on it.**
5. **Complex-supported rigidity classification** (hardest). Is there any nontrivial
   classification of crystalline/FQ-type measures with off-line (complex) support?
   Prior art appears empty; the payoff is a genuinely new RH-equivalence in rigidity
   language. **Long-horizon; the honest "reverse-Dyson" endgame.**

---

## §5. Full citation ledger

| # | Authors | Title | Venue | arXiv | DOI |
|---|---|---|---|---|---|
| KS20 | Kurasov, Sarnak | Stable polynomials and crystalline measures | J. Math. Phys. 61 (2020) 083501 | 2004.05678 | 10.1063/5.0012286 |
| OU20a | Olevskii, Ulanovskii | Fourier quasicrystals with unit masses | C. R. Math. 358 (2020) 1207–1211 | 2009.12810 | 10.5802/crmath.142 |
| OU20b | Olevskii, Ulanovskii | A Simple Crystalline Measure | preprint (2020) | 2006.12037 | — |
| LO15 | Lev, Olevskii | Quasicrystals and Poisson's summation formula | Invent. Math. 200 (2015) 585–606 | 1312.6884 | 10.1007/s00222-014-0542-z |
| ACV24 | Alon, Cohen, Vinzant | Every real-rooted exp. poly. is a restriction of a Lee–Yang poly. | J. Funct. Anal. (2024) | 2303.03201 | 10.1016/j.jfa.2023.110226 |
| AKKV25 | Alon, Kummer, Kurasov, Vinzant | Higher dimensional Fourier quasicrystals from Lee–Yang varieties | Invent. Math. 239 (2025) 321–376 | 2407.11184 | 10.1007/s00222-024-01307-8 |
| AV23 | Alon, Vinzant | Gap distributions of Fourier quasicrystals via Lee–Yang polynomials | preprint (2023) | 2307.13498 | — |
| Fav24 | Favorov | The crystalline measure that is not a Fourier Quasicrystal | preprint (2024) | 2401.01121 | — |
| Mey16 | Meyer | Measures with locally finite support and spectrum | PNAS 113 (2016) 3152–3158 | — | 10.1073/pnas.1600685113 |
| Dys09 | Dyson | Birds and Frogs | Notices AMS 56 (2009) 212–223 | — | — |
| Lag00 | Lagarias | Mathematical quasicrystals and the problem of diffraction | CRM Monogr. 13, AMS (2000) 61–93 | — | — |
| AF26 | Alpöge, Furman | More than 2/3 of the zeros … simple and on the critical line | preprint (2026) | 2608.13637 | — |
| AF26b | (companion) | A new proof that more than 2/3 … | preprint (2026) | 2609.02882 | — |
| — | (Weil→matrices) | Finite Hilbert–Pólya matrices from Weil's explicit formula | preprint (2026) | 2609.04908 | — |

---

## §6. Verification log (what was cross-checked, what was not)

- **Cross-checked ≥2 sources:** KS20 venue/DOI/construction (AIP + arXiv + AV23
  summary); OU20a statement (Numdam + arXiv + Adve-search corroboration); ACV24
  Thm 1.1 & Cor 1.4 (HTML body + abstract + JFA DOI + AV23 summary); LO15
  venue-correction (Springer + arXiv, **charter's "Annals" corrected to Invent. Math.
  2015**); Mey16 (PNAS DOI + EMS/ADS); Dys09 verbatim quotes (Exeter zeta archive
  transcription of Notices essay); AF26 abstract + Lemmas 3.1/3.2/Prop 4.1 (HTML +
  abstract); zeta density/gap facts (Riemann–von Mangoldt N(T) + average-gap sources).
- **NOT verified to full precision (flagged in-text):** verbatim *theorem numbers*
  in KS20 body (PDF binary, no HTML); AKKV25 "Thm 2.9" number (secondary summary
  only); any literal "RH ⇔ dual-comb temperedness" theorem (does not appear to exist
  as a citable result — treated as program conjecture); the **"Adve" authorship** of
  any 1-D characterization (unconfirmed — the 1-D iff is ACV+OU+KS).
- **Tooling note:** `WebFetch` returns arXiv **PDFs as binary** (unreadable); use
  `arxiv.org/html/<id>` or `arxiv.org/abs/<id>` for text. B2/B4 should pull KS20 and
  AKKV25 PDFs to a local reader to lock the remaining theorem numbers before citing.
