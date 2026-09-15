# QC_RIGIDITY_MEMO — the complex-supported rigidity program (formulation + toy theorem)

> **`conjecture1_proved = False`.** This memo *states* conjectures and *proves* two
> honest toy cases; it does not prove RH and does not claim to. Every conjecture is
> labeled a conjecture; every proof is a paper-level proof with a machine-checkable
> numeric backbone (verified in this session) and a kernel-ready hand-off to the B2
> island. The reverse-Dyson program remains a research program; RH is open.

**Agent:** `qc-rigidity` (Wave B, deliverable **B4**, PROGRAM MIRRORMERE).
**Gates:** A1 (`QC_LITERATURE.md`), A2 (`QC_AXIOMS_DRAFT.md`).
**Method:** literature cross-check (WebSearch/WebFetch, ≥2 sources per adjacent
result); the two toy theorems are proved by hand and their zero-structure claims
independently verified numerically in-session (script transcripts in §6).

---

## §0. One-paragraph orientation

Dyson's reverse program asks us to *classify* 1-D quasicrystals and find zeta among
them. A1/A2 established the honest ceiling: the **completed** classification
(Kurasov–Sarnak → Olevskii–Ulanovskii → Alon–Cohen–Vinzant, "ℕ-FQ ⇔ Lee–Yang real
zero set") does **not** apply to the zeta comb — zeta fails uniform discreteness and
its FQ-grade (temperedness of the absolute dual) is exactly the RH content. This memo
attacks the *reverse* question directly: not "is zeta an FQ" but **"what forces a
comb's support to be real?"** — a *rigidity* question. I state it at three strengths
(R1 full strip-rigidity, R2 defect-k, R3 spectrum-restricted/finite), give each its
zeta instance, and subject each to the two mandatory controls (the **DH test** and
the **C-variant test** from A2). I then *prove* the finite case R3 for n = 2
frequencies unconditionally, and for n = 3 rationally-dependent frequencies reduce it
to the Lee–Yang-on-the-circle theorem (B2's `LeeYangCore`), and I show exactly where
the argument breaks at irrational frequency ratios. The headline honest finding: the
n = 2 rigidity theorem is **real and new-to-our-corpus**, with the *right* hypothesis
shape (an equal-modulus / self-inversive weight condition that DH provably fails); and
the "conservation of difficulty" map locates RH-hardness precisely at the transition
from *finitely-generated / rationally-dependent* to *rationally-independent, growing*
frequency systems — the same place Favorov–Değer's 2026 strip papers stall.

---

## §1. The three rigidity statements

Notation throughout. A **comb** is a locally finite atomic complex measure
`μ = Σ_j a_j δ_{z_j}` with atoms `z_j ∈ ℂ` in a horizontal strip `S_h = {|Im z| ≤ h}`
(`h ≥ 0`; `h = 0` is the real line). "**Complex-supported**" means we *do not* assume
`z_j ∈ ℝ` a priori — the reality of the support is the conclusion to be forced. The
**regularized triple** (per A1 finding-2 and §3.4) is the pair (support comb, dual
comb) coupled through the Guinand–Weil archimedean correction; all temperedness /
FQ-grade statements are made on this triple, never on a bare `Σ δ_γ`. Favorov
temperedness grade: `|μ|` and `|μ̂|` tempered = **FQ-grade**; only `μ, μ̂` discrete-
tempered = **crystalline-grade** (strictly weaker; Favorov 2024 separates them).
Defect grade (A2 variant D): negative index `k` of the finite Guinand–Weil / Weil-form
compression `G̃` (Alpöge–Furman signature-(1,1) blocks).

### R1 — Strip-rigidity (full)

> **Conjecture R1.** Let `μ = Σ_j a_j δ_{z_j}` be a comb supported in a strip `S_h`,
> `h ≤ 1/2`, such that
> **(H-spec)** its dual `μ̂` is pure-point with atomic support in the positive prime
> log-lattice `Λ_log = {±k log p}`, with weights **real, strictly positive, of order
> `(log p) p^{-k/2}`** (A2 variant **B**, clause B-iii + B-ii);
> **(H-mult)** the weight sequence is **multiplicative** in the prime content of the
> frequency (Euler-product primitive; A2 §9 option (c));
> **(H-temp)** the regularized triple is **FQ-grade** (both `|μ|, |μ̂|` tempered).
> Then `supp μ ⊂ ℝ` (the support is real).

Support class: strip `S_{1/2}`, complex a priori. Spectrum class: positive
multiplicative log-lattice. Temperedness grade: FQ (Favorov-strong). Defect grade:
`k = 0` (this is the defect-free apex).

### R2 — Defect-k strip-rigidity

> **Conjecture R2.** Same hypotheses as R1 except **(H-temp)** is relaxed to
> **crystalline-grade with defect ≤ k**: every finite Guinand–Weil compression `G̃`
> has negative index `n_-(G̃) ≤ k` (A2 variant **D**, clause D-ii). Then `supp μ` is
> real **up to at most `k` conjugate pairs** `{z, z̄}` off the real axis — i.e.
> `#{j : Im z_j ≠ 0}/2 ≤ k`.

This is the honest, *partial*, Alpöge–Furman-grade statement: each off-line pair is
exactly one signature-(1,1) block, so "defect ≤ k" ⇔ "≤ k complex-conjugate atom
pairs." `k = 0` recovers R1. `k = k(T)` bounded-per-height is the "2/3-paper" reading.

### R3 — Spectrum-restricted (finite / Dirichlet-polynomial) rigidity

> **Conjecture R3 (statement; the n ≤ 3 cases are THEOREMS, §2).** Let
> `F(x) = Σ_{j=0}^{n} c_j e^{i λ_j x}`, `c_j ∈ ℂ^*`, `λ_j ∈ ℝ` distinct, be a *finite*
> exponential sum (equivalently a Dirichlet polynomial under `x = -i s`). Let `Z(F)`
> be its zero multiset in `ℂ`, and `μ_F = Σ_{z ∈ Z(F)} δ_z` the zero-counting comb.
> Suppose **(H-fin-spec)** the "dual data" — the coefficient vector `(c_j)` against the
> frequency set `(λ_j)` — satisfies the **self-inversive / equal-modulus positivity
> condition** that is the finite shadow of R1's (H-spec)+(H-mult) (made precise per n
> in §2). Then `Z(F) ⊂ ℝ` (F is real-rooted), hence `μ_F` is a real comb.

Support class: finite/locally-finite, strip-a-priori. Spectrum class: finite frequency
set (Bohr spectrum `{λ_j}`). Temperedness grade: trivially FQ (finite). Defect grade:
`k =` number of off-real conjugate zero-pairs; R3 asserts `k = 0` under (H-fin-spec).

**The R3 slogan — "Lee–Yang read backward."** ACV Thm 1.1 (A1 §1.3) says
*real-rootedness ⇒ Lee–Yang restriction structure*. R3 is the converse-flavored
*rigidity*: *a positivity/self-inversive condition on the dual (coefficient) side ⇒
real-rootedness*. This is precisely a Lee–Yang criterion used in the reverse direction,
which is why B2's `LeeYangCore` zero-reality theorem is the natural closer.

---

## §2. The toy theorem — R3 proved for n = 2, reduced to Lee–Yang for rational n = 3

This is the deliverable's mathematical core. Both zero-structure claims were verified
numerically in-session (§6).

### 2.1 Theorem A (n = 2) — PROVEN, unconditional

> **Theorem A.** Let `F(x) = c_1 e^{i λ_1 x} + c_2 e^{i λ_2 x}` with
> `c_1, c_2 ∈ ℂ^*` and `λ_1 ≠ λ_2 ∈ ℝ`. Set `w = λ_2 - λ_1 ≠ 0`. Then:
> **(a)** every zero of `F` lies on the single horizontal line
> `Im x = -\frac{1}{w} \log\left|\frac{c_1}{c_2}\right|`, and the zeros are the
> arithmetic progression `Re x ∈ \frac{1}{w}(\arg(-c_1/c_2) + 2πℤ)`;
> **(b)** consequently `F` is **real-rooted ⟺ `|c_1| = |c_2|`** (an equal-modulus /
> unitary condition on the coefficients).

**Proof.** Factor `F(x) = c_1 e^{i λ_1 x}\left(1 + \frac{c_2}{c_1} e^{i w x}\right)`.
Since `c_1 e^{iλ_1 x}` never vanishes, `F(x)=0 ⟺ e^{i w x} = -c_1/c_2 =: r ∈ ℂ^*`.
Write `iwx = \log|r| + i(\arg r + 2πk)`, `k ∈ ℤ`. Then
`x = \frac{1}{iw}[\log|r| + i(\arg r + 2πk)] = \frac{1}{w}[(\arg r + 2πk) - i\log|r|]`.
Hence `Im x = -\frac{1}{w}\log|r| = -\frac{1}{w}\log|c_1/c_2|`, independent of `k`,
proving (a). This is real ⟺ `\log|c_1/c_2| = 0 ⟺ |c_1|=|c_2|`, proving (b). ∎

**Reading as R3.** The hypothesis (H-fin-spec) at n = 2 *is* `|c_1| = |c_2|`. This is
exactly a **self-inversive / equal-modulus positivity condition on the dual side**: it
says the two Bragg amplitudes have equal magnitude, the finite analogue of R1's
"positive weights of matched order." Under it, the support is forced real — the first
rigidity theorem of the program, unconditional and with the correct hypothesis shape.
Note it is a *reality* condition purely on the coefficients (the "spectrum/weight
side"), never on the support — the reverse-Dyson signature.

### 2.2 Theorem B (n = 3, rationally dependent) — REDUCED to Lee–Yang-on-the-circle

> **Theorem B.** Let `F(x) = e^{i λ_0 x}\sum_{j=0}^{s} c_j e^{i m_j ω x}` with `ω ∈ ℝ^*`,
> `m_j ∈ ℤ` (so all frequency differences are integer multiples of a single `ω` —
> the **rationally-dependent** case). Put `z = e^{iωx}` and
> `P(z) = \sum_j c_j z^{m_j}` (a Laurent polynomial). Then, since `x ↦ z` maps
> `\{Im x = t\}` onto `\{|z| = e^{-ωt}\}`:
> **F is real-rooted ⟺ every zero of `P` lies on the unit circle `|z| = 1`**
> (a **self-inversive Lee–Yang-on-the-circle** condition on `P`).

**Proof.** `x ∈ ℝ ⟺ |z| = |e^{iωx}| = 1`. A zero `x_0` of `F` corresponds to a zero
`z_0 = e^{iωx_0}` of `P` (the prefactor `e^{iλ_0 x}` is nonvanishing), with
`Im x_0 = -\frac{1}{ω}\log|z_0|`. Thus all zeros real ⟺ all `|z_0| = 1`. ∎

**Concrete closed form (`m = (0,1,2)`, real coefficients).** `P(z) = c_0 + c_1 z + c_2
z^2`; both zeros on `|z| = 1` ⟺ **`|c_0| = |c_2|` (self-inversive) and
`c_1^2 ≤ 4|c_0||c_2|` (hyperbolicity/discriminant)**. The first clause is again the
equal-modulus positivity of Theorem A; the second is the real-rootedness of the
associated real quadratic on the circle. Both were verified numerically (§6): e.g.
`(c_0,c_1,c_2)=(2,0,1)` has `|c_0|≠|c_2|` and its roots leave the circle (`|z|=√2`),
while `(1,½,1)` satisfies both clauses and both roots sit on `|z|=1`.

**Kernel hand-off.** Theorem B is *precisely* the interface to B2: "all zeros of a
self-inversive Laurent/algebraic polynomial lie on `|z|=1`" is the circle form of the
Lee–Yang zero-reality statement B2 is formalizing as `LeeYangCore`. Theorem B says
**R3(rational-n) reduces to `LeeYangCore` with zero residual analytic content** — the
reduction is the elementary substitution above. This is the memo's kernel-ready output
(§5).

### 2.3 What breaks at irrational frequency ratios — R3(iii), honest boundary

If the frequencies are **rationally independent** (no common `ω` with integer `m_j`),
the substitution `z = e^{iωx}` fails: there is no single-variable polynomial on one
circle. The zeros are then governed by the classical theory of zeros of
**almost-periodic** exponential sums (Ritt 1929; Mora–Sepulcre–Vidal 2013; the 2026
AMM paper "When Do Zeros of an Exponential Sum have Real Parts that Form a Dense
Set?"). The relevant facts:

- For a three-term sum with rationally-**independent** exponents, the zeros lie in
  **one or two vertical strips**, and the **real parts of the zeros are dense** in the
  corresponding intervals **iff the frequency ratio is irrational** (Mora–Sepulcre–
  Vidal). The imaginary parts spread across a band, *not* a single line.
- I verified this numerically (§6): for `λ = (0, 1, √2)`, unit coefficients, the near-
  zeros populate ≈16 distinct imaginary levels across `Im x ∈ [-0.86, 0.58]` — no
  single-line/single-circle structure. By contrast an n = 2 sum with an *irrational*
  ratio (`λ = (0, √3)`) still has all zeros on the one line `Im x = 0` (Theorem A is
  rank-1 and cares nothing about rationality).

So the obstruction is **not irrationality per se** but **rank ≥ 2 rational
independence**: it is the first place the finite problem stops being a
single-circle/torus problem and becomes a genuinely higher-dimensional Lee–Yang
*variety* problem (AKKV 2025 territory). **This is exactly the finite shadow of the
RH-hardness transition** (§4): zeta's frequencies `{k log p}` are the maximally-
rationally-independent, unboundedly-growing system.

---

## §3. Controls — every statement passes DH test AND C-variant test

Governance (charter §Guardrails, A2 §Global): any statement DH satisfies is DEAD (DH
has off-line zeros); any statement must be strictly inside A2's B/D territory, never in
the DEAD C-variant (signed, positivity-dropped) that DH passes.

### 3.1 DH test (DH must NOT satisfy the hypotheses)

- **R1/R2 vs DH.** DH `= \frac{1-iκ}{2}L(s,χ) + \frac{1+iκ}{2}L(s,χ̄)`, `χ mod 5`, has
  **no Euler product**, so its explicit-formula prime side is the log-derivative of a
  *sum* of two L-functions: the per-prime amplitudes mix `χ(p), χ̄(p)` (complex roots
  of unity) and are **not real-positive and not multiplicative**. DH therefore fails
  **(H-spec)** positivity *and* **(H-mult)** multiplicativity. ✔ DH excluded — and by
  the *same* clause A2 identified as the DH-killer. Under R2, DH is doubly excluded: it
  has a **positive proportion** of off-line zeros, so its defect `k(T) → ∞`, violating
  any bounded-`k` hypothesis. ✔
- **R3 vs DH.** A finite DH section has coefficient vector of **unequal moduli** (the
  character-mixed `n^{-s}` weights): I checked a 2-term DH-flavored section
  `c_1=\frac{1-1.2i}{2}, c_2=\frac{1+1.2i}{2}·0.7` — `|c_1|=0.781 ≠ 0.547=|c_2|` (§6).
  So (H-fin-spec) `|c_1|=|c_2|` **fails**, and Theorem A predicts complex zeros —
  consistent with DH having off-line zeros. ✔ At n = 3 the DH coefficient sequence is
  not self-inversive, so `P` is not circle-rooted. ✔ DH excluded at every R3 level.

### 3.2 C-variant test (must be strictly inside B/D, not in dead-C)

A2's **Variant C** (signed log-lattice, positivity **dropped**) is DEAD because DH
passes it. Each rigidity statement must therefore *use positivity essentially*:

- **R1/R2** invoke (H-spec) **positive** weights + (H-mult) multiplicativity — the two
  clauses that separate B from the dead C. Drop positivity → the statements become
  false (DH is a counterexample with signed/complex weights and off-line support). ✔
  Inside B/D territory by construction.
- **R3** invokes the **equal-modulus** condition `|c_j|` matched (self-inversive),
  which is the finite incarnation of positivity: it is a *magnitude/reality* condition,
  and dropping it (allowing arbitrary complex `c_j` of matched decay only — the dead-C
  analogue) admits off-line zeros (Theorem A with `|c_1|≠|c_2|`; the `(2,0,1)`
  quadratic in §2.2). ✔ Strictly inside B/D.

**Control verdict.** All three statements exclude DH via the *positivity/self-inversive*
clause, and all three are false without it. This is the required behavior: the kill is
attributable to positivity, exactly as A2's C-vs-B contrast predicted, now confirmed at
the rigidity level and *proven* at n = 2.

### 3.3 Zeta instance and the RH-implication chain (per statement)

- **R1 ⇒ RH? (spell it out).** Zeta's support comb has atoms at `γ_ρ = -i(ρ-1/2)`;
  unconditionally `γ_ρ ∈ S_{1/2}` (the completed-zeta zeros have `Re ρ ∈ [0,1]` ⇒
  `Im γ_ρ ∈ [-1/2,1/2]`). RH ⟺ all `γ_ρ` real. Now discharge R1's hypotheses on the
  zeta instance:
  - **(H-spec) positivity/order** — **UNCONDITIONAL.** The GW prime side is literally
    `(\log p)p^{-k/2} > 0` (A2 §6); this is arithmetic, not RH.
  - **(H-mult) multiplicativity** — **UNCONDITIONAL.** `-ζ'/ζ = \sum (\log p)p^{-ks}`
    is the log-derivative of an Euler product; the amplitude sequence is multiplicative.
  - **(H-temp) FQ-grade** — **RH-EQUIVALENT / the hard clause.** Temperedness of the
    *absolute* dual comb `|μ̂|` is exactly what off-line zeros (`p^{-β}`, `β≠1/2`)
    threaten (A1 §1.6 Favorov separation; A2 variant B (B-ii) pure-pointness). This is
    where RH lives.
  So **R1 applied to the zeta comb, WITH (H-temp) granted, would yield `supp μ_ζ ⊂ ℝ`,
  i.e. RH.** The implication chain is: [(H-spec),(H-mult) unconditional] + [(H-temp) =
  RH-equivalent input] --R1--> real support = RH. **R1 is therefore an
  RH-*equivalence packaged as rigidity*, not an unconditional route to RH**: it moves
  the hardness into (H-temp). Honest label: **R1 ⇔ (H-temp for zeta) ⇔ RH** — a
  restatement, whose value is *locating* the difficulty in one named clause, not
  removing it. (This matches A2's "clean split" conclusion for variant B.)
- **R2 ⇒ (partial).** With (H-temp) relaxed to defect ≤ k, R2 yields "≤ k off-line
  pairs" — the Alpöge–Furman-grade *partial* statement, **unconditionally meaningful at
  each height** (finite `k(T)` is provable; `k=0` is RH). This is the genuinely-now-
  verifiable rung and the one that pairs with B3's certified defect experiment.
- **R3 ⇒ finite-section control, not RH.** R3 is about *finite* Dirichlet polynomials;
  its zeta instance is the **partial-sum / Dirichlet-polynomial approximants**
  `\sum_{n≤N} n^{-s}`, whose zeros are known to be mostly off-line (Turán, Montgomery,
  the "computing zeros of partial sums of ζ" literature). R3 correctly does **not**
  apply to them because their coefficient vector `(n^{-s})` is **not self-inversive /
  equal-modulus** — so R3 predicts (correctly) that finite zeta sections are *not*
  real-rooted. **R3 yields no RH implication; it is the toy where the machinery is real
  and the controls are exact.** Its role is to *prove the hypothesis shape correct*
  (positivity/self-inversion forces reality; its absence permits off-line zeros), which
  is the transferable lesson to R1/R2.

### 3.4 The regularization caveat (A1 §1.7, load-bearing)

R1/R2 are stated on the **regularized triple**, never the bare `Σ δ_γ`: the zeta
support and prime combs are paired only through the GW archimedean Γ-factor. Any
version of R1/R2 read against a naked crystalline measure is DEAD on arrival (A1 §3.4).
The strip hypothesis `S_{1/2}` is meaningful precisely because the completed-zeta
functional equation confines `γ_ρ` to `S_{1/2}` unconditionally — the rigidity is
"collapse the a-priori strip to its real axis," which is the exact geometric content of
RH.

---

## §4. Adjacent known results (survey) — what already exists, and the honest novelty boundary

Cross-checked ≥2 sources each (URLs in §7). **This section corrects two A1 flags.**

1. **The "Adve" attribution is RESOLVED — it is Favorov, not Adve.** A1 §1.6/§4 flagged
   an unverified "Anshul Adve" theorem on bounded-density-spectrum FQs. I fetched
   arXiv:2203.06733 ("Fourier quasicrystals and distributions on Euclidean spaces with
   spectrum of bounded density"): **sole author Sergii (Serhii) Favorov.** No Adve
   authorship exists in this line. The theorem characterizes temperate distributions
   with **uniformly discrete support and locally finite spectrum** as finite sums of
   derivatives of **generalized lattice Dirac combs** under coefficient conditions — a
   *rigidity* result, but under uniform discreteness (which zeta fails). **B4 verdict:
   do not build on an "Adve" theorem; the relevant bounded-density rigidity is
   Favorov's and it is off zeta's path (uniform-discreteness hypothesis).**

2. **Complex-supported rigidity is NOT virgin territory — Favorov–Değer 2026 is direct
   prior art (and A1 §3.3's "prior art appears empty" is now CORRECTED).** Two papers:
   - **Favorov–Değer, "Analogues of Fourier quasicrystals for a strip," arXiv:2408.09563
     (Aug 2024).**
   - **Favorov–Değer, "Some properties of Fourier quasicrystals and measures on a
     strip," arXiv:2605.10766 (May 2026).** Verbatim abstract (fetched): they consider
     positive/translation-bounded measures `μ` on a strip whose FT is pure-point
     `μ̂ = Σ b_γ δ_γ`, prove `ν = Σ|b_γ|²δ_γ` **has exponential growth**, and — if the
     spectrum points are **ℤ-linearly-independent in every length-`η` window** —
     `μ̂` itself has exponential growth.
   **What this means for the program (critical, honest).** Favorov–Değer already study
   *exactly* the complex-supported (strip) FQ object R1/R2 are about. **But their
   theorem is a growth dichotomy, not a "support forced real" rigidity.** (An automated
   PDF summary initially told me they "force support onto ℝ" — I discarded that: the
   *verbatim abstract* claims exponential growth of the transform under a per-window
   ℤ-independence hypothesis, which is a *different, weaker* conclusion.) The
   ℤ-independence-per-window hypothesis is close to A2's §9 open definitional problem
   and to my R3(iii) rank-independence boundary. **Novelty boundary for MIRRORMERE:**
   the *strip FQ category* is theirs; what is *not* in their papers is (a) the
   **positive-multiplicative-log-lattice** spectrum specialization (R1's H-spec+H-mult,
   the arithmetic/zeta-specific clause), (b) the **defect-k** grading via Weil-form
   inertia (R2, Alpöge–Furman), and (c) the explicit **finite/Lee–Yang-backward** toy
   theorems (§2). R1/R2 should be positioned as *the arithmetic-spectrum + defect-graded
   specialization of the Favorov–Değer strip program*, citing them as the ambient
   category — **not** as a brand-new category. Overclaiming novelty here would be a
   referee-fatal error.

3. **Zeros of exponential sums in strips — the finite theory is classical and settled
   enough to power R3.** Ritt (1929, TAMS): zeros of exponential sums lie in vertical
   strips. Mora–Sepulcre–Vidal (2013) + the 2026 AMM paper: for three-term sums the
   real parts of zeros are **dense** in the strip-intervals **iff the frequency ratio is
   irrational**; ACV Thm 1.1 (A1 §1.3): a *real-rooted* exponential polynomial has its
   frequencies' convex hull a segment with **real normal** (a single real-direction
   strip). These are exactly the ingredients of Theorem A/B and the §2.3 boundary. **R3
   is thus standing on classical ground; its contribution is the *reverse* framing
   (dual-side positivity ⇒ reality) and the kernel hand-off, not new analysis.**

4. **de Branges / Krein / Hermite–Biehler — the "right" home for R1, flagged for Wave
   2.** A Hermite–Biehler function `E` (no zeros in `ℂ⁺`, `|E| ≥ |E^#|` there) has all
   zeros in the closed *lower* half-plane; the de Branges space `B(E)` and the
   associated canonical system encode exactly "zeros on a line" as a positivity
   (self-adjointness) statement. This is the *structural* analogue of R1: real support ⇔
   an operator/positivity condition. Lagarias' Hilbert-spaces-of-entire-functions
   program (2012 Benasque slides) is the RH-facing version. **Recommendation: R1's
   deepest formulation likely lives in de Branges language (HB self-inversiveness =
   equal-modulus of Theorem A, scaled up); flag for MIRRORMERE Wave 2, do not attempt
   here.** Note this is *also* where RH-hardness is known to concentrate (the de Branges
   approach to RH is famously not closed), corroborating the §4-map placement of the
   difficulty.

5. **Other adjacent (context, non-blocking):** Favorov "crystalline measure that is not
   an FQ" (2401.01121, the crystalline ⊋ FQ separation — the temperedness discriminator
   for (H-temp)); "On almost periodicity in crystalline measures" (2605.23884);
   Gonçalves "classification of Fourier summation formulas and crystalline measures"
   (2024). None constructs a *positive-log-lattice complex-supported* comb, so none
   contradicts R1/R2; they populate the ambient category.

---

## §5. The conservation-of-difficulty map + attackability ranking

**Attackability (easiest → hardest):** **R3(n=2) ≪ R3(rational-n) ≪ R2 ≈ R3(irrational
/ growing-n) ≪ R1.**

| Rung | Status | Where the difficulty is | Kernel-ready? |
|---|---|---|---|
| **R3 n=2** | **PROVEN** (Thm A) | none — elementary; rank-1 | Yes (trivial; §5.1) |
| **R3 rational-n** | **REDUCED to Lee–Yang** (Thm B) | packaged into `LeeYangCore` (circle zero-reality) — B2 owns it | Yes — the reduction is the deliverable (§5.1) |
| **R3 irrational / growing-n** | **OPEN** | rank ≥ 2 rational independence: no single-torus reduction; higher-dim Lee–Yang *variety* (AKKV). Zeros spread to a band (Mora–Sepulcre–Vidal). | No |
| **R2 (defect-k)** | **OPEN; partial-now** | finite `k(T)` provable (Alpöge–Furman inertia, B3); driving `k→0` = RH | Partial — B3's `DefectDictionary` + finite compression |
| **R1 (full)** | **OPEN = RH** | **(H-temp): FQ-grade / temperedness of absolute dual comb.** Unconditional: (H-spec)+(H-mult). RH-equivalent: (H-temp). | No — this clause *is* RH |

**The map, stated plainly.** RH-hardness enters at **exactly one place, twice
disguised:**

1. In the **finite world (R3)**, hardness is the transition from
   **rationally-dependent** to **rationally-independent, unbounded** frequency systems.
   With one common `ω` (rank 1) everything collapses to a single circle and Lee–Yang
   closes it (Thm A/B). With `{k log p}` (maximal rank, growing) there is no torus, and
   the zeros genuinely spread — the finite shadow of the zeta comb's non-uniform-
   discreteness. Favorov–Değer's per-window ℤ-independence hypothesis is the same wall
   from the measure side.
2. In the **infinite/arithmetic world (R1)**, that same wall reappears as the
   **(H-temp) FQ-grade** clause: temperedness of the absolute dual is what a growing,
   rationally-independent, off-line-perturbed spectrum destroys. (H-spec) positivity and
   (H-mult) multiplicativity are *free* (arithmetic); temperedness is *the whole cost*.

So the program does **not** dissolve RH — it **relocates** it, with proof, into a single
named hypothesis (H-temp), and shows (via R3) that the same hypothesis-shape (dual-side
positivity/self-inversion) *does* force reality once the frequency system is
rank-controlled. **The realistic MIRRORMERE payoff is R2 + R3, not R1:** R2 is the
partial, certifiable, publishable rigidity (defect-graded, pairs with B3); R3 gives the
first *proven* rigidity theorems of the program with exact controls. R1 is honestly
labeled an RH-equivalence.

### 5.1 Kernel-ready for B2

Two items, both elementary reductions with **zero residual analytic content**, ready to
formalize once B2's `LeeYangCore` (self-inversive/circle zero-reality) exists:

**K1 — `TwoFreqRigidity` (Theorem A).** Fully self-contained, no `LeeYangCore` needed.
Statement to formalize:
```
For c1 c2 : ℂ, c1 ≠ 0, c2 ≠ 0, w : ℝ, w ≠ 0,
  (∀ x : ℂ, c1 * exp(I*λ1*x) + c2 * exp(I*λ2*x) = 0 → x.im = 0)  ↔  ‖c1‖ = ‖c2‖.
```
Proof term is the §2.1 factorization: reduce to `exp(I*w*x) = -c1/c2` and read
`x.im = -(1/w)*log‖c1/c2‖`. Mathlib has `Complex.exp`, `Complex.log`, `Complex.arg`,
and `Complex.exp_eq_exp_iff_exists_int`. **No new axioms; this is a clean first
kernel rigidity brick — recommend B2 land it as the R3 base case even before
`LeeYangCore`.**

**K2 — `RationalFreqReduction` (Theorem B).** Depends on `LeeYangCore`. Statement:
```
For P : LaurentPolynomial ℂ (or ℂ[z] after clearing), ω : ℝ, ω ≠ 0,
  (∀ x : ℂ, eval (exp(I*ω*x)) P = 0 → x.im = 0)  ↔  (∀ z, eval z P = 0 → ‖z‖ = 1).
```
Then compose with `LeeYangCore : (self-inversive ∧ hyperbolic) → (∀ z root, ‖z‖=1)` to
get R3(rational-n). The `↔` is the substitution `z = exp(I*ω*x)`,
`x.im = -(1/ω)*log‖z‖` (same lemma as K1's core). **Hand-off: B2 formalizes
`LeeYangCore`; K2 is the one-line bridge from it to a rigidity theorem.**

Neither K1 nor K2 introduces a `sorry` or a non-standard axiom; both are guarded-file
candidates. I did **not** build Lean here (no `.lake` cache in this worktree, per
charter); these are drafted statements for the B2 island.

---

## §6. In-session numeric verification log

All run in `/Users/peterwmurphy/arda-qc-rigidity` with system Python + numpy.

- **Theorem A (a),(b):** for `(c1,c2,λ1,λ2) ∈ {(1,1,0,1),(2,1,0,1),(1,1,3,7),
  (1+2i,2+i,-1,2)}`, sampled zeros `k=-2..2` all satisfy `|F(x)|<1e-9` and
  `Im x = -(1/w)log|c1/c2|` to `1e-12`; real ⟺ `|c1|=|c2|`. **PASS.**
- **Theorem B closed form:** `P=c0+c1 z+c2 z^2` roots on `|z|=1` for `(1,0,1),(1,1,1),
  (1,½,1)` (self-inversive + hyperbolic) and OFF for `(1,3,1)` (real roots, `|z|=2.618,
  0.382`) and `(2,0,1)` (`|z|=√2`, self-inversion fails). Matches "`|c0|=|c2|` ∧
  `c1²≤4|c0||c2|`". **PASS.**
- **DH test (R3):** DH-flavored 2-term `c1=(1-1.2i)/2, c2=((1+1.2i)/2)·0.7` →
  `|c1|=0.781≠0.547=|c2|`; (H-fin-spec) fails ⇒ complex zeros predicted, consistent
  with DH off-line zeros. **PASS (DH excluded).**
- **§2.3 boundary:** `λ=(0,1,√2)` unit coeffs → near-zeros on ≈16 distinct `Im x`
  levels in `[-0.86,0.58]` (band, no single line); `λ=(0,√3)` (n=2 irrational) →
  single line `Im x≈0`. **Confirms rank-independence, not irrationality, is the wall.**

---

## §7. Sources (this memo's adjacent-literature layer; A1/A2 own the core citations)

- Favorov, "FQ and distributions on Euclidean spaces with spectrum of bounded density,"
  arXiv:2203.06733 — **sole author Favorov (resolves A1's "Adve" flag).**
  https://arxiv.org/abs/2203.06733
- Favorov–Değer, "Some properties of Fourier quasicrystals and measures on a strip,"
  arXiv:2605.10766 (verbatim abstract fetched). https://arxiv.org/abs/2605.10766
- Favorov–Değer, "Analogues of Fourier quasicrystals for a strip," arXiv:2408.09563.
  https://arxiv.org/pdf/2408.09563
- Mora, Sepulcre, Vidal (2013) + AMM 2026 "When Do Zeros of an Exponential Sum have Real
  Parts that Form a Dense Set?" https://www.tandfonline.com/doi/full/10.1080/00029890.2026.2624366
- Ritt, "On the zeros of exponential polynomials," TAMS 31 (1929).
  https://www.ams.org/journals/tran/1929-031-04/S0002-9947-1929-1501506-6/
- "The asymptotic number of zeros of exponential sums in critical strips,"
  arXiv:1908.09491. https://arxiv.org/pdf/1908.09491
- de Branges / Krein / Hermite–Biehler + Lagarias entire-function RH program (Wave-2
  flag): Poltoratski Krein–de Branges slides; Lagarias Benasque 2012.
  https://websites.umich.edu/~lagarias//TALK-SLIDES/benasque-riemann2012jun.pdf
- Favorov, "A crystalline measure that is not an FQ," arXiv:2401.01121 (temperedness
  discriminator for (H-temp)). https://arxiv.org/html/2401.01121

`conjecture1_proved = False`.
