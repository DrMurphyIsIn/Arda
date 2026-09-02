<!-- ultrathink 6-agent primary-source campaign, 2026-08-30. Corrects the surface/Theorem-3.1/log2pi over-read. conjecture1_proved=False. -->

# The F_1 Hodge-index frontier: the single open lemma, verified and graded

*Synthesis as of 2026-08-28. All grades are primary-source-anchored; every UNVERIFIED item is flagged. This document pins the frontier of the Connes–Consani "surface positivity" route to the Riemann Hypothesis. It does not prove RH.*

---

## 0. Executive verdict

The task premise — that arXiv:2606.06604 constructs the surface **Spec Z ×_{F₁} Spec Z**, computes a diagonal self-intersection **Δ·Δ = log 2π**, and proves a Hodge-index **signature inequality** in a "Theorem 3.1" that drives RH — is **factually false on every specific**. It is a composite over-read stitched from three distinct papers. The genuine open lemma is not a smaller-than-RH target hiding in a 2026 paper; it is **global Weil positivity**, which is a *proven equivalent* of RH (a rename), not an attackable sub-lemma. Where the premise's "surface signature inequality" is even well-posed, supplying it is of RH-strength; where it is not yet well-posed, making it well-posed is *also* of RH-strength.

**conjecture1_proved = False.** (Stated in full at the end.)

---

## 1. What the 2026 "surface paper" actually proves: number vs. inequality — the over-read, corrected and verified

### 1.1 arXiv:2606.06604 is not a surface paper

**Verified against the abstract and HTML body** of Connes–Consani, *"On the Absolute Geometry of Spec Z"* (June 2026):

- **Object constructed:** the **absolute F₁-arithmetic CURVE** `(Spec Z)_{F₁}` — a **1-dimensional** object, obtained by pulling back the F₁-structure sheaf of the arithmetic site along a morphism to Spec(Z). Its C-points recover a **real analogue of the Fargues–Fontaine curve** and the complex **Tate curve** with modulus q = p^{−1}.
- **No fiber-product surface.** "Spec Z ×_{F₁} Spec Z" does not appear. UNVERIFIED-AND-ABSENT.
- **No diagonal self-intersection**, no "Δ·Δ = log 2π", no "intersection form", no "signature", no "Hodge-index." Text search on the extracted body returns **zero occurrences** of `self-intersection`, `diagonal`, `intersection`, `log 2π`, `signature`. The 8 occurrences of "Hodge" all refer to **p-adic Hodge theory** (Fargues–Fontaine, untilts) — a different "Hodge" from the Hodge-*index* theorem.
- **No "Theorem 3.1."** Section 3 runs Lemma 3.1 (a statement on dense embeddings of subgroups into local fields: K ≅ R or Q_p), Def 3.2, Prop 3.3, …, **Theorem 3.9**, …, **Theorems 3.16, 3.17** (the moduli/untilt classification realizing Scholze's tilting heuristic). **The prior "over-read of Theorem 3.1" flag is CONFIRMED: there is no Theorem 3.1 to over-read.**
- **No RH claim.** The paper does not claim to prove or imply RH.

**Grade for the premise's specific claim: FALSE / MISATTRIBUTED.**

### 1.2 Where the "square" and self-intersection material actually lives

The genuine "square / diagonal / intersection-number" apparatus is the **older "square of the arithmetic site"** program — Connes–Consani, arXiv:1502.05580, *Geometry of the Arithmetic Site*. **Verified:** the square is a **semi-ringed topos** whose structure sheaf is `Conv≥(N×N)` (the semiring of Newton polygons under convex-hull-of-union and Minkowski sum) — a **characteristic-one / tropical** object, **not a scheme over a field**. Frobenius correspondences `Fr_λ` (λ ∈ R_+^×) are realized as subobjects, and the RHS of the Weil explicit formula is *recovered* as an intersection-number expression **D·Δ**. This is CONSTRUCTED bookkeeping — the explicit formula re-expressed geometrically.

Crucially, in this lineage the diagonal self-intersection term is **divergent / unregularized**; Connes–Consani attribute the problematic term (the coefficient of f(1) in the explicit formula) precisely to *"the lack of a good definition of self-intersection of the diagonal."*

### 1.3 The "log 2π" figure: UNVERIFIED, and probably a conflation

The specific value **Δ·Δ = log 2π** could **not be located in any primary source** this session (alainconnes.org returned HTTP 403; AIM slide PDFs failed to parse). Two nearby *real* constants get conflated with it:

- **log 2** — the genuine, verified Riemann–Roch correction on the compactified curve (§2.2 below), *not* a self-intersection.
- the divergent scaling-site diagonal term (§1.2), which is *not* a clean proven number.

**Grade: the "= log 2π" figure is UNVERIFIED and, on the balance of evidence, a composite artifact — a NUMBER (if it exists at all), never an inequality.**

---

## 2. The Connes–Consani chain: proven pieces + the single open lemma, link by link

### 2.1 Link 0 — RH ⟺ Weil positivity (the equivalence, not a reduction)

**PROVEN (classical: Weil 1952; Bombieri, *Remarks on Weil's quadratic functional*).** RH ⟺ the Weil functional `W(f ⋆ f*) ≥ 0` for all admissible test functions. This is a **two-way equivalence**. Connes–Consani's own framing confirms the load-bearing direction verbatim (arXiv:2006.13771 abstract): the tools *"make sense in the general semi-local case, **where Weil positivity implies RH**."* Consequence: **any statement equivalent to global Weil positivity is exactly RH-strength** — it can be neither strictly weaker nor strict over-kill. This is why the "open lemma" is not smaller than RH.

### 2.2 Link 1 — Riemann–Roch / Serre duality on \overline{Spec Z}

**PROVEN — but curve-level** (arXiv:2205.01391, *Riemann–Roch for \overline{Spec Z}*). A genuine integer-valued Riemann–Roch with cohomologies and **Serre duality** on the Arakelov compactification of Spec Z, modeled on Weil's adelic function-field proof via Pontryagin duality; the Euler characteristic carries an explicit **+ log 2** correction (verified from abstract). This supplies the **linear (RR / functional-equation) half** of the analogy on a **1-dimensional** object. It is **not** a surface, carries **no intersection form**, and asserts **no signature inequality**.

### 2.3 Link 2 — Archimedean-place Weil positivity

**PROVEN — but single place, restricted support** (arXiv:2006.13771, Selecta Math 2021). A genuine *positivity inequality* (not merely a number) at the **single archimedean place**, via prolate spheroidal functions + Hermitian Toeplitz control of the Weil-minus-Sonin difference. In the 2026 survey this is **Theorem 7.1**: for g ∈ C_c^∞(R*_+) supported in [2^{−1/2}, 2^{1/2}] with Fourier transform vanishing at i/2 and 0, `W∞(g ⋆ g*) ≥ Tr(ϑ(g) S ϑ(g)*)` (S = projection onto the Sonin space) — verified verbatim from arXiv:2602.04022 §7.2. The paper itself flags that the **semi-local / global** extension is *not* done and *is* where RH sits.

### 2.4 Link 3 — Prolate / Sonin spectral realization

**PROVEN as an ultraviolet-asymptotic, single-place similarity** (arXiv:2310.18423, Connes–Consani–Moscovici). The self-adjoint prolate wave operator, restricted to the Sonin space, has discrete spectrum whose negative eigenvalues reproduce the **UV asymptotics of the squares of the zeros** (survey §7.6, verbatim). The survey's own hedge: this *"suggests that one has spectrally captured the contribution of the archimedean place"* — an **asymptotic**, at **one place**; it places **no** zero on the critical line.

### 2.5 Link 4 — Infrastructure (2026): Jacobian, absolute curve, real-FF dictionary

**CONSTRUCTED, no positivity.** arXiv:2602.15941 (*On the Jacobian of \overline{Spec Z}*, Picard/Jacobian structure) and arXiv:2606.06604 (absolute F₁-curve + real-Fargues–Fontaine + Tate-curve dictionary) are **infrastructure**, explicitly positioned as geometric support. Neither constructs a surface, an ample class, or a signature inequality.

### 2.6 The single open lemma, stated as precisely as the literature allows

> **OPEN LEMMA (RH-equivalent):** Global (semi-local, all-finite-primes) **Weil positivity** — equivalently, the **negative-definiteness of the intersection/trace form on the primitive (mean-zero) part** — holds.

The program has proven only proper *fragments*: single-place positivity (2.3), curve-level RR (2.2), UV single-place spectral realization (2.4). **The global positivity itself is unproven, and by Link 0 it is ⟺ RH.**

---

## 3. The F_q proof and the exact missing ingredient over Q

### 3.1 The F_q Hodge-index proof — PROVEN (Weil 1948; Deligne, Weil II)

For a smooth projective curve C/F_q, work on the genuine smooth projective **surface S = C × C**. The Frobenius graph Γ_Fr ⊂ C×C is a correspondence (a divisor class). The engine is the **Hodge index theorem**: the intersection form on NS(S) has signature **(1, ρ−1)** — positive on an **ample** class H, **negative-definite on the primitive part** H^⊥. Its corollary, the **Castelnuovo–Severi inequality** `Z·Z ≤ 2·deg₁(Z)·deg₂(Z)`, applied to `Z = m·Δ + n·Γ_Fr`, gives trace-positivity `Tr(Z∘Z') ≥ 0`, which specializes to the eigenvalue bound `|α_i| = √q`, i.e. RH for C. **The ample class is what converts sign data into trace-positivity.**

### 3.2 The four candidate obstructions over Q, graded

| # | Obstruction | Over F_q | Over Q / F₁ | Grade |
|---|---|---|---|---|
| (i) | Surface `Spec Z ×_{F₁} Spec Z` exists as a scheme | Yes (C×C is a scheme) | **Not constructed.** 2606.06604 builds only the 1-dim curve. The "square" that *does* exist (1502.05580) is a **semi-ringed topos** (Newton polygons), not a scheme with an NS lattice | **OPEN** (primary obstruction) |
| (ii) | Ample / Kähler polarization | Yes | No established ample cone; downstream of (i) | **OPEN** |
| (iii) | Signature of the intersection/trace form | PROVEN (1, ρ−1) via Hodge index | = Weil positivity; proven only at the archimedean place; global = RH-equivalent | **archimedean PROVEN / global OPEN & RH-equivalent** — the crux |
| (iv) | Finiteness (finite-dim cohomology) | Yes (dim 2g) | Infinitely many zeros → diagonal self-intersection **divergent**, needs regularization | **OPEN (technical), not the deep blocker** |

**Reading:** transfer is blocked *first* at (i) — no surface. The *essential* difficulty is (iii) — the signature/positivity, which is RH-strength. (iv) is a real setup complication (regularizing the divergent diagonal term) that the scaling-site program flags but which is not the crux. (ii) is vacuous until (i) is settled.

---

## 4. THE CRUX — is the open Hodge-index-signature lemma weaker-yet-sufficient (a), RH-equivalent (b), or not even well-posed (c)?

**Answer: (b), degenerating to (c) on the literal surface formulation. There is no reading in which it is (a).**

**Argument for (b) — it is a rename.** The skeptic's adjudication makes this airtight:
1. Weil's explicit-formula criterion is a *two-way* equivalence: **RH ⟺ W(f⋆f*) ≥ 0** (Bombieri).
2. Connes–Consani state the forward direction verbatim: semi-local **"Weil positivity implies RH"** (2006.13771).
3. "The intersection form has the right signature on the primitive part" is precisely the **geometric name** for "the Weil quadratic form is ≥ 0." Renaming the vocabulary does not change the content.

Therefore the signature inequality **is** global Weil positivity **is** RH. Because (1) is an *equivalence*, any statement equivalent to it is **exactly RH-strength** — so it **cannot** be (a) weaker-yet-sufficient. The only proven fragments are strictly *local* (one place) or *lower-dimensional* (one dimension); extending either to the global level *is* RH.

**Why (c) is the honest fallback on the surface wording.** "Negative-definiteness of the intersection form on the primitive part of NS(surface)" has **no referent** without a constructed **ample class** to separate the positive line from the negative-definite complement. Absent (i)+(ii), the phrase "signature" is **not well-posed**; making it well-posed (building the polarization) is itself of RH-strength (§3.2 (ii)/(iii)).

**Contrast with a real theorem next door (why the hope is seductive but unmoved):** the **Yuan–Zhang arithmetic Hodge index theorem** (*Math. Ann.*) *is* a proven signature theorem — but on a **genuine arithmetic surface** X → Spec O_K (a flat 2-dimensional scheme with "arithmetically ample" bundles), **not** on the F₁ square, and it does **not** encode zeta zeros as a Frobenius spectrum, hence does not yield RH. Its existence shows the machinery works where the object is real — and that the F₁ object is exactly the thing that is missing.

**This confirms the CRUX identically to the prior gate: the open lemma is RH-EQUIVALENT (a rename), not a weaker-yet-sufficient attackable target. Cite: the SKEPTIC adjudication (horn (b), fallback (c)); B2 §4.1; B3 §2; B4 headline.**

---

## 5. Attackability — is any sub-piece certificate/Telperion-shaped, or is it all deep geometry?

**Verdict: the crux is deep geometry, not a certificate/Telperion-shaped lever. Only peripheral infrastructure is incrementally attackable, and none of it is the signature inequality.**

- **The signature inequality itself:** NOT certificate-shaped. It is an infinite-dimensional positivity over all places / all admissible test functions, equivalent to RH. There is no finite SOS/moment certificate, no finite polytope, no Telperion emitter that discharges it — the same "arithmetic/integrality vs. smooth-certificate" no-go seen in the Laplacian/BG work applies in spirit: a global positivity co-extensive with RH has no finite-basis witness.
- **Peripheral, genuinely incremental (but NOT the lemma):**
  - Push **archimedean positivity → semi-local** (2006.13771 → the semi-local trace formula, survey §7.4). Load-bearing, but the moment it closes it *is* RH.
  - The **"Letter to Riemann" convergence route** (survey §6.6) names two sub-lemmas verbatim: (a) the smallest eigenvalue of the Weil quadratic form Q_W^λ is *"simple with even eigenvector"* (known for the prolate operator; not yet transferred), and (b) *"k_λ is a sufficiently good approximation of θ_x."* These are the most concrete finite-flavored fragments — but they are *approximation/spectral* analysis, not certificate-discharge, and they bound only the *approximants*, not ζ.
  - **Riemann–Roch on \overline{Spec Z}** (2205.01391) and the **Jacobian / Picard monoid** (2602.15941): real, provable, extendable infrastructure — but curve-level, not the surface positivity.

**Bottom line for tooling:** nothing here is a Telperion/certificate lane. It is topos theory + Arakelov geometry + spectral analysis of the explicit formula. The proven fragments are the honest deliverables; the crux is not a lever.

---

## 6. Honest odds and the single most concrete next step

**Odds.** This is a **decade-scale geometry program, not a lever.** The one object that would run the Weil argument (a polarized surface with an ample cone over F₁) does **not exist**, and constructing it — or, equivalently, proving global Weil positivity directly — is of full RH-strength. No 2020–2026 Connes–Consani paper narrows the gap below RH; the authors themselves disclaim a proof (survey 2602.04022 §8: *"whether this path leads to a proof of RH remains to be seen"*). Probability that the "open lemma" is a genuine attackable target strictly weaker than RH: effectively **zero**, because it is a proven RH-*equivalent*.

**Single most concrete next step (a paper to master, honestly).** Master **Connes's Feb-2026 survey, arXiv:2602.04022** — specifically §4.1 (the RH ⟺ semi-local positivity equivalence), §6.6 (the two named "remaining steps" sub-lemmas), §7 (the square-of-site intersection-number apparatus and Theorem 7.1 archimedean positivity), and §8 (the author's own disclaimer). It is the single primary source that (i) states every proven fragment verbatim, (ii) names the two most concrete open sub-lemmas, and (iii) fixes the honest boundary between "computed intersection number" and "unproven signature inequality." Master it *before* touching any sub-lemma, because it makes unmistakable that the load-bearing target is RH-equivalent — so effort should go to the *approximation sub-lemmas* (§6.6) or the *semi-local trace formula* (§7.4) as research contributions, **not** to a hoped-for weaker "Theorem 3.1 signature inequality" that does not exist.

---

## 7. Consolidated grading table

| Item | Source | Status |
|---|---|---|
| RH ⟺ Weil positivity | Weil 1952; Bombieri | **PROVEN equivalence** (⇒ open lemma is RH-strength) |
| Archimedean-place Weil positivity (Thm 7.1) | 2006.13771 / survey §7.2 | **PROVEN** — single place, restricted support |
| Semi-local / global Weil positivity (the open lemma) | survey §4.1, §7.4 | **OPEN ≡ RH** |
| Riemann–Roch / Serre duality on \overline{Spec Z} | 2205.01391 | **PROVEN** — curve-level (χ = deg + **log 2**), not the surface |
| Prolate / Sonin spectral realization | 2310.18423 / survey §7.6 | **PROVEN** as UV-asymptotic single-place similarity; places no zero on the line |
| Square-of-site intersection **number** D·Δ | 1502.05580; survey §7 | **CONSTRUCTED** (semi-ringed topos; numbers, not a signature form) |
| Hodge-index signature **inequality** on the square | — | **OPEN / RH-equivalent** — the crux |
| Ample / Kähler class on the F₁ square | — | **OPEN** — same problem as the crux |
| Surface `Spec Z ×_{F₁} Spec Z` as a scheme | — (2606.06604 builds a **curve**) | **OPEN / not constructed** |
| Arithmetic Hodge index (real signature theorem, wrong object) | Yuan–Zhang, *Math. Ann.* | **PROVEN** — but on arithmetic surfaces X→Spec O_K, does **not** yield RH |
| "2606.06604 builds the surface, Δ·Δ = log 2π, Thm 3.1 signature ineq" | 2606.06604 | **FALSE / MISATTRIBUTED** — curve only; no surface/self-int/Thm-3.1/Hodge-index/RH |
| "Δ·Δ = log 2π" specific value | — | **UNVERIFIED** — likely a conflation of log 2 (RR) with the divergent scaling-site term |
| RH proven anywhere in the corpus | — | **NO.** Author: *"remains to be seen"* (survey §8) |

---

## 8. Unverified items (flagged honestly)

- **"log 2π"** for any diagonal self-intersection — not located in any primary source (alainconnes.org 403; AIM slides unparseable). Treat as UNVERIFIED and probably a composite artifact.
- Exact wording of 2606.06604 **§5 "Outlook"** — truncated in fetch; UNVERIFIED (does not affect the graded findings, which rest on the verified body).
- Internal theorem *numbering* of 2006.13771 / 2205.01391 / 2310.18423 — content corroborated via the survey; the papers' own internal numbers were not re-extracted.
- Bombieri Clay exposition and arXiv:1509.05576 body — did not OCR through fetch; the mathematical statements are textbook-standard, but exact verbatim strings are UNVERIFIED.

---

**This pins the frontier; it does not prove RH. conjecture1_proved = False.**

Primary sources: [2606.06604 — Absolute Geometry of Spec Z](https://arxiv.org/abs/2606.06604) · [2006.13771 — Weil positivity, archimedean place](https://arxiv.org/abs/2006.13771) · [2205.01391 — Riemann–Roch for \overline{Spec Z}](https://arxiv.org/abs/2205.01391) · [2310.18423 — prolate/Sonin (Connes–Consani–Moscovici)](https://arxiv.org/abs/2310.18423) · [2602.15941 — Jacobian of \overline{Spec Z}](https://arxiv.org/abs/2602.15941) · [1502.05580 — Geometry of the Arithmetic Site](https://arxiv.org/abs/1502.05580) · [1509.05576 — An Essay on the Riemann Hypothesis](https://arxiv.org/abs/1509.05576) · [2602.04022 — Connes 2026 survey](https://arxiv.org/pdf/2602.04022) · [Yuan–Zhang, Arithmetic Hodge Index Theorem, Math. Ann.](https://link.springer.com/article/10.1007/s00208-016-1414-1)