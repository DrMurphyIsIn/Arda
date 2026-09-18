# QC_TORUS_MEMO — the infinite-torus formulation of the arithmetic-FQ class

*(PROGRAM MIRRORMERE, Wave-3 rung W3c `qc3-torus`, research memo.
`conjecture1_proved = False` throughout. This is a **formulation** memo — it states
definitions, relates them to the finite instruments already built, and labels every
non-definitional claim as CONJECTURE. It proves no new theorem and does not prove or
claim RH.)*

Companion docs (required context): `QC_AXIOMS_DRAFT.md` (variants A–D, the v2 W3a
B-mult appendix, the v3 W3c B-mult-twisted appendix — the finite-checkable shadow of
this memo), `QC_LITERATURE.md` (ACV Cor 1.4 finite-torus classification;
Favorov–Değer strip-FQ corrections; Alpöge–Furman inertia instrument),
`QC_RECURRENCE_MEMO.md §3` (the Kronecker-flow dynamics frame — the *same* torus read
dynamically), `QC_PROGRAM.md` (the three pillars). Roadmap slot: W3c ("the pillar-2
extension, framed; NOT RH-hard on its face; the deepest open formulation problem").

---

## §0. One-paragraph map

ACV (Cor 1.4) classify the ℕ-valued Fourier quasicrystals as restrictions of a
Lee–Yang polynomial from a **finite torus** `(S¹)^n` along a ℚ-independent winding
`x ↦ (e^{ix ℓ_1},…,e^{ix ℓ_n})`, with spectrum in the finitely generated group
`ℤ⟨ℓ⟩`. Zeta's upstairs object is not a finite torus but the **infinite torus**
`𝕋 = ∏_p S¹` (one circle per prime), and its Euler product is literally a product
over that torus's factors. This memo formulates the "**arithmetic FQ**" class as
*restriction-from-`∏_p S¹`* of a measure with **multiplicative** (product-over-primes)
structure, pulled back along the **Kronecker winding** `t ↦ (p^{−it})_p`. Each finite-
torus ACV clause has an infinite-torus counterpart; the B-mult-twisted clause of
`QC_AXIOMS_DRAFT` (v3) is the finite-checkable *shadow* of "the upstairs measure is a
product over primes." The stack of axioms — involution dictionary (functional
equation), B-mult-twisted (Euler product), temperedness (growth) — is assembling the
**Selberg class in diffraction coordinates**; the classification target "arithmetic FQ
⟺ automorphic L" is the **quasicrystal shadow of Langlands**. Everything here about
"⟺ automorphic L" is CONJECTURE; the definitions and the finite-instrument
correspondences are what this memo makes precise.

---

## §1. The restriction-from-`∏_p S¹` formulation

### 1.1 The infinite torus and the Kronecker winding

**Definition (the torus).** Let `𝕋 = ∏_p S¹` be the compact abelian group indexed by
the primes, `S¹ = ℝ/ℤ` (or `{z:|z|=1}`; we use multiplicative coordinates
`z=(z_p)_p`, `z_p ∈ S¹`). `𝕋` is the **Bohr/Kronecker compactification** of the line
associated to the frequency set `{log p}`: its Pontryagin dual is the free abelian
group `⊕_p ℤ = ℚ_{>0}^×` (finite integer vectors of prime exponents), the character
attached to `n=∏ p^{a_p}` being `z ↦ ∏_p z_p^{a_p}`.

**Definition (the Kronecker winding).** The map
\[ w : ℝ → 𝕋, \qquad w(t) = (p^{-it})_p = (e^{-i t\log p})_p, \]
is a one-parameter subgroup ("winding line"). Because `{log p}` are **ℝ-linearly
independent** (unique factorization), `w(ℝ)` is **dense** and the translation flow
`τ·z = w(τ)z` is **minimal and uniquely ergodic** (Weyl), with Haar measure the unique
invariant measure. *(This is the spatial statement; `QC_RECURRENCE_MEMO §3` reads the
same `w` dynamically as the Kronecker flow — "the same torus seen spatially vs
dynamically.")*

### 1.2 The arithmetic-FQ class, stated

> **Definition (arithmetic Fourier quasicrystal — the W3c class).** A tempered atomic
> measure `μ` on ℝ is an **arithmetic FQ** if its dual comb `μ̂` is pure-point and
> arises as the **pullback along `w` of a multiplicative measure on `𝕋`**. Precisely,
> there is a **completely multiplicative unimodular** weight `t:{primes}→S¹∪{0}` (a
> value on each circle `S¹_p`, with `t(p)=0` at the finitely many ramified primes
> dividing a conductor `q`) such that the atoms of `μ̂` are exactly
> \[ \bigl\{\,(m\log p,\; (\log p)\,t(p)^m\,p^{-m/2}) : p\nmid q,\ m\ge 1\,\bigr\}, \]
> i.e. `μ̂` is the log-derivative of the Euler product `∏_{p\nmid q}(1−t(p)p^{−s})^{−1}`
> evaluated on the winding — one **circle-factor `S¹_p`** contributing the geometric
> per-prime family `{(m log p, (log p)t(p)^m p^{−m/2})}_m`. The **universal weight**
> `(\log p)p^{−m/2}` is prime-independent; the **twist** `t(p)^m` is the character
> coordinate on `S¹_p`.

This is a **definition**, not a theorem. Its two design choices are the ones W3a/W3c
adjudicated (`QC_AXIOMS §9`, v2 §W3a.0, v3 §W3c.0): the primitive is **multiplicativity
of the amplitude** (a per-generator/local condition), **not** a Diophantine separation
of atom locations (a global metric condition that degenerates as the log-primes fill in
densely, `QC_AXIOMS §9`). Multiplicativity is stable as the torus dimension `n→∞`
precisely because it is per-circle.

### 1.3 Clause-by-clause: finite torus (ACV) ⟷ infinite torus (W3c)

| ACV / finite-torus clause (`QC_LIT §1.3`) | Infinite-torus (W3c) counterpart | Finite-checkable shadow (instrument) | Definition or conjecture |
|---|---|---|---|
| Spectrum in a **finitely generated group** `ℤ⟨ℓ⟩`, `ℓ∈ℝ₊ⁿ` ℚ-independent (hyp (iv)) | Spectrum in `⊕_p ℤ` = dual of `∏_p S¹`; the **finite sub-torus** `(S¹)^{π(e^R)}` is the window `[−R,R]` truncation to primes `p≤e^R` | windowed atomic-spectrum clause (A-ii/B-ii); `zoo.check_atomic_spectrum_loglattice` | **definition** (the group is `⊕_p ℤ`; that it is the *right* group is the classification content) |
| `μ = μ_{p,ℓ}` from a **Lee–Yang polynomial** on `(S¹)ⁿ` | `μ̂` = pullback of a **product measure** `⊗_p ν_p` on `∏_p S¹` (one factor per prime) | **B-mult-twisted** clause (v3); `zoo.check_multiplicativity` (complex/unimodular) | **definition** of the class; "product ⟹ Lee–Yang/real-rooted upstairs" is CONJECTURE |
| Real-rootedness of `f(x)=e^{λ_0 x}p(e^{ixℓ})` (support real) | Support of `μ` real ⟺ the pulled-back Euler product is **zero-free off the critical line** (RH/GRH) | **defect-0** clause (D-ii, `k=0⟺`RH/GRH); Alpöge–Furman inertia instrument | **conjecture** (this is exactly the RH/GRH content — not moved by W3c, by design) |
| ℕ / unit masses (counting measure) | ℤ-mass atoms (zeros with multiplicity) | support-density clause (A-i/B-i); certified `N(T)` ladder | **definition** + certified data |
| `|μ|,|μ̂|` tempered (FQ, not merely crystalline) | temperedness of the pulled-back distribution and its dual | temperedness clause; Favorov crystalline⊋FQ separation | **definition**; its *ζ-grade* is RH-sensitive (`QC_LIT §1.6`, Face 2) |
| involution / self-inversive symmetry of the Lee–Yang polynomial (`z↦1/z̄` factor-wise) | the **self-inversive symmetry on each circle** `S¹_p` (`z_p ↦ z̄_p`), assembling to the functional equation `s↦1−s` | involution dictionary (W2a): functional-equation ⟺ self-inversive under `z=e^{iωx}`; `selfInversive_iff_hardyZ_real` (kernel) | **theorem** (W2a, finite instances) + **definition** (the assembly to `s↦1−s` on the infinite torus) |

**The single honest bridge that is NOT a definition:** "`μ̂` is a *product* over primes
`⊗_p ν_p`" (infinite-torus B-mult-twisted) is the exact upstairs statement whose
finite shadow the zoo checks. The zoo can only certify the shadow at finite window
`N` (composite-vanishing + per-prime unimodular generation up to `N`); the leap to "the
whole dual comb is a genuine product measure on `∏_p S¹`" is where **pure-pointness of
`μ̂`** (still RH/GRH-conditional) lives. So the formulation cleanly re-localizes the
hardness: the *product structure* (B-mult-twisted) is unconditional/arithmetic and
finite-checkable; the *measure-ness of the product's pullback* (pure-point `μ̂`,
defect-0) is the RH/GRH clause, unchanged.

### 1.4 Why "restriction from `∏_p S¹`" is not RH-hard on its face (roadmap claim)

For `Re s > 1` the Euler product converges and `ζ(σ+it)=𝒵(σ,(p^{−it})_p)` is a genuine
**continuous** pullback of a function on `𝕋` (`QC_RECURRENCE_MEMO §3`); the arithmetic-
FQ *definition* (§1.2) is a statement about the **amplitude sequence**, which exists
unconditionally as the von-Mangoldt-twisted coefficients `Λ(n)χ(n)` for any Dirichlet
character. Formulating the class, exhibiting its members (ζ, `L(χ)`), and rejecting non-
members (DH) are all unconditional — done in the zoo. The RH/GRH content enters **only**
when one asks whether a given arithmetic FQ's *support* is real (defect-0), which the
formulation deliberately isolates in one clause. Hence "NOT RH-hard on its face": the
formulation problem is a **definitional/classification** problem (which multiplicative
structures occur, and do they force automorphy), with RH quarantined to the defect
grade. This is the sense in which W3c is "the deepest open **formulation** problem," not
an RH attempt.

---

## §2. The Selberg correspondence

### 2.1 The dictionary (Selberg axioms ↔ diffraction clauses ↔ our instruments)

The **Selberg class `𝒮`** (Selberg 1992) is the set of Dirichlet series `F(s)=Σ a_n
n^{−s}` with: (S1) analytic continuation (`(s−1)^m F` entire, finite order); (S2) a
**functional equation** `Φ(s)=ω Φ̄(1−s̄)`, `Φ(s)=Q^s ∏Γ(λ_i s+μ_i) F(s)`; (S3) a
**Ramanujan bound** `a_n≪_ε n^ε`; (S4) an **Euler product** `log F(s)=Σ b_n n^{−s}`
with `b_n` supported on prime powers and `b_n≪ n^{θ}`, `θ<1/2`. The **primitive**
elements (not a product of two others) are conjecturally the automorphic L-functions
(Selberg's conjectures; the `GL(n)/ℚ` Langlands picture).

Read `F` through the GW/diffraction lens — `F`'s nontrivial zeros are `μ`'s support
atoms, `log F`'s prime-power coefficients are `μ̂`'s Bragg amplitudes — and each Selberg
axiom becomes a diffraction clause we have an instrument for:

| Selberg axiom | Diffraction clause (this program) | Our instrument (status) |
|---|---|---|
| **(S1)** Dirichlet series + finite-order continuation | comb **temperedness** (`|μ|,|μ̂|` tempered, finite order) | temperedness clause (`zoo.check_temperedness`, all objects); Favorov crystalline⊋FQ grade = Face 2 (BUILT: zoo clause + memo) |
| **(S2)** functional equation `Φ(s)=ωΦ̄(1−s̄)` | **involution / self-inversive** symmetry `s↦1−s` ⟺ `z↦z̄` per circle | **W2a involution dictionary**: `selfInversive_iff_hardyZ_real` + TwoFreq instance (**kernel**) |
| **(S4)** Euler product `log F=Σ b_{p^m}(p^m)^{−s}` | **B-mult-twisted**: amplitudes multiplicatively generated from a unimodular prime layer | **W3a/W3c** `multiplicativity` clause, complex/twisted (**mechanized**, Arb-trust; ζ & L(χ) PASS, DH FAILS) |
| **(S3)** Ramanujan `a_n≪n^ε` (⇒ `|b_p|` bounded) | Bragg **amplitude decay envelope** `|c(m log p)|≤c_+(log p)p^{−m/2}` | signed-decay clause (C-iii, `zoo.check_signed_decay`); the `|t(p)|=1` unimodular test in B-mult-twisted enforces the `GL(1)` case exactly |
| **growth / order** (the hardness carrier) | the **R1 temperedness clause** of the dual comb (RH-sensitive grade) | R1 (`QC_RIGIDITY_MEMO`, named + isolated); Face 2; **NOT** discharged (the deep clause) |
| **primitivity** (Selberg factorization) | **irreducibility** of the product measure `⊗_p ν_p` (not a convolution of two arithmetic FQs) | *no finite instrument yet*; DH is precisely a **non-primitive-shaped** object (a *sum*, breaking S4) — the zoo's DH-kill is the first shadow of "non-Euler-product ⇒ outside 𝒮" |

**What the table says in one line:** the axiom stack we have been building
(involution + B-mult-twisted + temperedness/decay) is, clause for clause, the
**Selberg class rendered in diffraction coordinates**. (S2)↔W2a is a kernel theorem in
finite instances; (S4)↔B-mult-twisted is mechanized and now class-verified (ζ and
`L(χ)`); (S1)/(S3) are the temperedness/decay clauses; the growth/R1 clause carries the
RH-hardness and is the one we have isolated but not discharged.

### 2.2 The classification conjecture (referee grade)

> **Conjecture (arithmetic FQ ⟺ Selberg element, W3c).** Let `μ` be a log-density
> symmetric ℤ-mass atomic measure on ℝ with pure-point dual comb `μ̂`.
> **(⟹)** If `μ` is an **arithmetic FQ** (§1.2: `μ̂` is the pullback along the Kronecker
> winding of a completely-multiplicative unimodular product measure on `∏_p S¹`, with
> temperedness and the self-inversive `s↦1−s` symmetry), then `μ` is the **zero-comb of
> an element `F` of the Selberg class `𝒮`** (indeed of degree 1, a Dirichlet
> L-function, when the twist is unimodular — the `GL(1)` case).
> **(⟸)** Conversely, the zero-comb of any `F∈𝒮` satisfying (S1)–(S4) is an arithmetic
> FQ in the sense of §1.2 (its Euler product supplies the multiplicative product
> structure; its functional equation supplies the self-inversive symmetry; (S1)/(S3)
> supply temperedness/decay).
> **Support reality:** the support of `μ` is real ⟺ `F` satisfies its Riemann
> Hypothesis (defect-0). The RH/GRH content is confined to this last clause.

> **Langlands-shadow remark (CONJECTURE, labeled).** Under Selberg's conjectures the
> **primitive** elements of `𝒮` are exactly the automorphic `L`-functions of cuspidal
> `GL(n)/ℚ` representations. So the classification conjecture's slogan is **"arithmetic
> FQ ⟺ automorphic L,"** with **primitive arithmetic FQ ⟺ cuspidal automorphic** — the
> quasicrystal shadow of the Langlands correspondence. The `GL(1)` fiber (Dirichlet
> characters, unimodular twist) is the part the finite instruments now decide; `GL(n)`,
> `n≥2` (non-unimodular Satake amplitudes) is Wave-4 (§3).

**What our finite instruments can and cannot decide about this (honest).**

- **CAN (mechanized / kernel):** exhibit members of the `GL(1)` class and reject non-
  members. The zoo certifies (Arb-trust) that ζ (trivial twist) and `L(χ)` (character
  twist) satisfy B-mult-twisted while DH — their non-multiplicative sum, a
  **non-Selberg** object because it violates (S4) — fails; W2a certifies (kernel) the
  functional-equation ⟺ self-inversive step in finite instances. So the **(⟸)**
  direction's ingredients and the **class membership** side are instrumented.
- **CANNOT (open, definitional):** (i) the leap "completely-multiplicative unimodular
  amplitude ⟹ genuine *Dirichlet character* `F=L(s,χ)`" (vs an exotic unimodular
  Euler-product sequence with no functional equation) — needs (S2), a conductor/finite-
  order hypothesis; (ii) the **(⟹)** direction as a *theorem* (that the product
  structure forces membership in `𝒮`), which is the ACV-analogue at `n=∞` and is
  **open**; (iii) **primitivity/Langlands** — no finite certificate (the primitivity
  row of §2.1 is empty); (iv) **support reality** (defect-0) — this is RH/GRH,
  explicitly not attempted.
- **Positioning vs literature (per `QC_LIT` corrections).** ACV (Cor 1.4) is the `n<∞`
  theorem this conjecture extends to `n=∞`; **Favorov–Değer** (arXiv 2605.10766,
  2408.09563) own the strip-FQ category as a **growth dichotomy** (NOT reality-forcing —
  the automated "reality-forcing" summary was discarded against the verbatim abstract,
  `QC_LIT §3`), so the W3c conjecture must be cited as their **arithmetic-spectrum +
  Euler-product specialization**, with reality-forcing remaining open and the
  Alpöge–Furman inertia instrument giving it the finite defect test. There is no cited
  theorem "arithmetic FQ ⟺ automorphic L"; it is a **program conjecture**.

---

## §3. Wave-4 feeders

### 3.1 A GL(2) object: the modular-form L-function `L(s,Δ)` (Ramanujan Δ)

Adding a `GL(2)` object to the zoo is the natural next falsification: it tests whether
B-mult-twisted (unimodular twist, the `GL(1)` shape) is itself *over-sharp* for the
higher-degree arithmetic class, the same way bare positivity was over-sharp for `GL(1)`.

`L(s,Δ)=Σ τ(n)n^{−s-11/2}` (normalized) has an Euler product `∏_p(1−α_p p^{−s}+
p^{−2s})^{−1}` with local roots `α_p,β_p`, `α_pβ_p=1`, `α_p=e^{iθ_p}` on the unit
circle by **Deligne's bound** (`|τ(p)|≤2p^{11/2}`, i.e. the normalized `a_p=2\cos θ_p ∈
[−2,2]`). So its prime-layer amplitude at `log p` is `b(p)=(\log p)(α_p^m+β_p^m)` —
**NOT unimodular**: `|α_p+β_p|=|2\cos θ_p|` ranges over `[0,2]`. B-mult-twisted (which
demands `|t(p)|=1`) would therefore **reject `L(s,Δ)`** — a false negative, because
`L(s,Δ)` *is* a genuine automorphic L-function. The honest fix (the work): replace the
scalar unimodular twist by the **Satake reading** — the per-prime datum is a
**conjugacy class in the dual group** (`SU(2)`/diagonal `diag(α_p,β_p)` with `α_pβ_p=1`,
`|α_p|=1`), and the generation law becomes `b(p^m)=(\log p)·\mathrm{tr}(\mathrm{Sym}^m
\mathrm{diag}(α_p,β_p))` — the `GL(2)` Hecke/Satake amplitudes. B-mult-twisted is the
`GL(1)` restriction (`1×1` Satake class = scalar `t(p)∈S¹`). One paragraph, honest:
mechanizing this needs (a) a certified `α_p` (Satake) enclosure per prime, (b) the
`Sym^m` trace recursion in the amplitude check, and (c) a decay-envelope update
(`|b(p^m)|` now grows like `m` via the trace, still within Ramanujan). It is a real
increment, not a rename — but it is the exact `GL(2)` analogue of the `GL(1)→`twisted
generalization W3c just did, and DH would still fail it (still not any Euler product).

### 3.2 Does the ACV finite-torus theorem admit a "profinite limit" attack? (assess)

ACV Cor 1.4 lives on `(S¹)^n`, `n<∞`; the arithmetic-FQ class lives on `∏_p S¹`, a
**profinite-shaped** (infinite product of compact groups) limit. The natural question:
can the `n<∞` classification be pushed to `n=∞` by a limit `(S¹)^{π(e^R)} ↑ ∏_p S¹`?

**Assessment (do not attempt now).** Two structural obstructions make this hard, and
one feature makes it tempting:
- **Obstruction 1 — the Lee–Yang condition is not obviously stable under the limit.**
  ACV's `p` is a Lee–Yang polynomial (no zeros in `𝔻ⁿ` nor `(ℂ∖𝔻̄)ⁿ`); the candidate
  `n=∞` object is the Euler product `∏_p(1−z_p)^{−1}`, which is not a polynomial and
  whose "Lee–Yang-ness" (zero-freeness of the *pullback* off the critical line) is
  **exactly RH/GRH**. So the limit does not stay inside the hypothesis class for free —
  the reality clause reappears as the limit's Lee–Yang condition, consistent with §1.3
  quarantining reality to defect-0.
- **Obstruction 2 — density vs uniform discreteness.** ACV objects have well-defined gap
  distributions and are generically uniformly discrete (`QC_LIT §1.6`); zeta's raw gaps
  →0 (density ~ log T). The finite-torus supports do **not** converge (as point sets) to
  a uniformly-discrete limit; the limit is a genuinely different (log-density) category,
  so a naive point-set limit of the ACV conclusion is false. The right limit is at the
  level of the **amplitude/measure on the dual `⊕_p ℤ`**, not the support.
- **Feature — the primitive is per-circle.** B-mult-twisted is a *local, per-`p`*
  condition (§1.2), so it *is* stable under `n→∞` (this is why W3c chose it over
  Diophantine separation). This is the one ingredient that survives the limit cleanly.

**Verdict:** a profinite-limit attack is a **legitimate long-horizon direction** but is
not a shortcut — it re-imports the reality clause as the limit's Lee–Yang condition
(Obstruction 1) and needs the measure-level (not support-level) limit (Obstruction 2).
It is properly a Wave-4+ research target, adjacent to de Branges/Hermite–Biehler (R1's
deep home, flagged NOT attempted in the roadmap). Recommendation: **do not attempt**;
record it as the structural statement of what the `n→∞` extension of ACV would require.

---

## §4. Honest ledger + relation to the built corpus

- **Definitions (this memo):** the torus `∏_p S¹`, the Kronecker winding, the
  arithmetic-FQ class (§1.2), and the Selberg-diffraction dictionary (§2.1). These are
  formulation, not theorems.
- **Theorems in the corpus feeding the dictionary:** W2a involution dictionary
  (functional-equation ⟺ self-inversive, kernel, finite instances); TwoFreqRigidity;
  the DefectDictionary/BraggDefect defect instrument (kernel). These instantiate the
  (S2) and defect rows.
- **Mechanized (Arb-trust, not kernel):** the zoo B-mult-twisted class verdict — ζ and
  `L(χ)` PASS, DH FAILS — instantiating the (S4) row and settling the class-not-
  description question at the finite-instrument level (`QC_AXIOMS` v3 §W3c.4).
- **Conjectures (labeled):** arithmetic FQ ⟺ Selberg element (§2.2); primitive ⟺
  automorphic (Langlands shadow); the ⟹ direction as a theorem; the completely-
  multiplicative-unimodular ⟹ Dirichlet-character step.
- **RH/GRH-hard, quarantined:** support reality = defect-0. Not moved by W3c, by design.
- **Not attempted (flagged):** de Branges/Hermite–Biehler; the profinite-limit attack
  (§3.2); full ACV converse formalization.

`conjecture1_proved = False`.
