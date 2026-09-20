# RH ROUTES A–D — the adversarially-verified roadmap

*2026-09-16. Produced by a 10-agent research campaign (5 route researchers + 5
adversarial skeptics; 1.36M tokens; every literature claim web-verified or marked
unverified; every corpus claim read against disk). Raw packages:
`telperion/docs/research/RH_ROUTES_RESEARCH_2026-09-16.json`. Corrections the
skeptics forced are applied inline and listed in §8 — several headline claims of
the first-draft reports were refuted and do not appear here except as corrections.*

**`conjecture1_proved = False`.** No route below proves RH. Each route *relocates*
RH into one named clause and instruments everything else. A roadmap with no wall
is dishonest; every milestone DAG below terminates in an explicitly-labeled
`rh-hard-wall` node. Difficulty classes: `mechanical` (codegen/throughput) →
`engineering` (real work, known shape) → `hard-known-shape` (serious mathematics,
known method template) → `open-research` (no known method, not known RH-hard) →
`rh-hard-wall` (provably or morally RH; the equivalence is named).

Corpus baseline (2026-09-16): ladder T=600,000 / 999,508 kernel-certified zeros;
`first_zero_kernel` (argument-free zero, all-rational-certificate); W3b
`rect_explicit_formula_bragg` (finite explicit formula in diffraction form,
unconditional); W3c Selberg dictionary (growth clause = the RH-hardness carrier);
W2b defect instrument (`offline_pairs_le_defect`); Li ladder λ₁–λ₂₀ certified +
pinned Li⟺RH reduction; polylog zero-free region; `RvMUnboundedMeanDensity`
residual (no unconditional proof anywhere, surveyed 2026-09-15).

---

## 1. THE WALL — one clause, graded identifications

All four routes terminate in the Selberg-dictionary **growth/temperedness clause**
(QC_TORUS_MEMO §2.1, the one S1–S4 row with no discharged instrument). Its
equivalent coordinates:

| Face | Wall form | Equivalence grade |
|---|---|---|
| Line (trivial) | all nontrivial zeros on Re = ½ (Mathlib `RiemannHypothesis`) | itself |
| Temperedness (A) | the **regularized** Guinand–Weil triple of the zeta comb is FQ-grade (defect-0) | R1 ⟺ (H-temp) ⟺ RH per QC_RIGIDITY §3.3; *precise statement queued* (QC_LITERATURE §1.7 grades it a program conjecture) |
| Positivity (B, D) | ∀n λₙ > 0 / W(g⋆g̃) ≥ 0 ∀ admissible g | Li 1997 + Bombieri–Lagarias 1999; corpus-pinned (`li_criterion_rh_iff`) |
| Heat-flow (C) | Λ ≤ 0 (with Rodgers–Tao Λ ≥ 0 ⇒ RH ⟺ Λ = 0) | Newman 1976 + de Bruijn 1950; RT Forum Math. Pi 8 (2020) e6 |
| Derivative (Speiser) | ζ′ ≠ 0 in 0 < Re s < ½ | Speiser 1935 |

**Correction (A-skeptic, load-bearing):** the naive membership statement — "the
dual comb on {±m log p} with amplitudes (log p)p^{−m/2} is tempered" — is
**unconditionally FALSE**: Σ_{n≤e^R} Λ(n)n^{−1/2} ~ 2e^{R/2} by PNT partial
summation, so |μ̂|-temperedness fails regardless of RH, and μ̂ carries an
absolutely-continuous archimedean (Γ′/Γ) component, so it is never pure-point
un-regularized. Only the **Guinand–Weil-regularized triple** (archimedean density
subtracted, paired test classes) can carry the membership statement. Authoring
that statement is itself open formulation work (Route A milestone A0,
reclassified `open-research`).

**Grading the "one clause in four disguises" thesis (E, post-skeptic):**
identical-by-construction for the rigidity face; classical named equivalences for
positivity/Λ/Speiser; *heuristic only* for the finite ladder reading. Since every
face is RH-equivalent, any cross-face "equivalence" routed through RH is vacuous
— the only non-vacuous unification content is finite-grade interderivability
(E5, `open-research`: one leg has a Rouché template, the "Li-prefix defect
signature" leg has no definition anywhere) and direct wall-to-wall reductions not
passing through RH (E11, `open-research`).

**Why finite certificates cannot reach any wall form** (kernel-or-literature
certified, all in-corpus): Euler-factor sections have zeros uniformly at
Im x = ½ (negative control `MM_euler_factor_section_offline`); partial sums have
zeros with Re s > 1 for all large N (Turán killed by Montgomery 1983); truncated
Euler products are zero-free entirely; window/defect/Li-prefix instruments are
compatible with an off-line zero whose signal enters only beyond any fixed
height/index; and for the Báez-Duarte face the floor is a theorem
(d²_N ≥ c/log N unconditionally). RH-content enters only at an infinite-N /
analytic-continuation / all-test-function quantifier. The house's three
refutation precedents (Obligation A kernel-refuted; StraightProgress trivially
true; the naive torus ladder false at every rung) are why this section exists.

---

## 2. ROUTE A — reverse-Dyson completion

**Terminal:** `zeta_FQ_iff_RH` (membership ⟺ RH — an *equivalence*, not an
implication route). Two halves: **A1** classification (arithmetic FQ ⟺ Selberg
element; extends the closed tame loop KS20→OU20→ACV24 to log density +
infinitely-generated spectrum ⊕ₚℤ, restriction-from-∏ₚS¹) and **A2** membership
(defect-rigidity: why a multiplicative comb cannot carry nonzero defect — the
leakage mechanism computed concretely on DH, b(6) = +1.9364).

**Design invariant (forced by the refutation precedents):** every intermediate
statement must be **defect-graded** — the un-graded (defect-0) class has no
certifiable member without proving that member's own GRH, so no finite exhibit of
the target class exists (the "un-graded classification trap").

| id | class | scale | deps | milestone |
|---|---|---|---|---|
| A0 | **open-research** (↓ from engineering, skeptic) | months | — | The honest regularized membership statement (the naive clause list is unconditionally false, §1) |
| A1a | hard-known-shape | weeks–months | — | KS forward theorem at small torus dimension, formalized (tame anchor; d=2 = `twoFreq_realRooted_iff` already kernel). *Statement not yet authorable — the island keeps FQ abstract; queued* |
| A1b | engineering | weeks | — | GL(2) Satake extension of B-mult-twisted (L(s,Δ) joins the zoo; falsification value: current clause REJECTS it) |
| A1c | open-research | months–years | A1b | Primitivity instrument (the empty dictionary row; only shadow = the DH kill) |
| A1d | open-research | years | A0, A1b | GL(1) fiber theorem: unimodular completely-multiplicative + FE ⇒ degree-1 Selberg element (both endpoint classifications exist: KP Acta 1999 degree ≤ 1) |
| A1e | open-research | decade+ | A1a, A1c, A1d | Arithmetic FQ ⟺ Selberg element, all degrees. Bounded below by the Selberg degree conjecture — which has moved exactly one unit interval (1<d<2, Kaczorowski–Perelli, *Annals* 173 (2011); d∈[0,1] Acta 182 (1999)) in thirty years; even finite-dimensional n>1 FQ converse open (Lawton–Tsikh) |
| A2a | **mechanical** (↓ from engineering, skeptic) | days | — | Defect-exactly-1 witness: *already proved* — `defect_eq_offline_pairs` (R2Rigidity.lean:209) and `bragg_defect_eq_one` (BraggDefect.lean:209) exist in-kernel. **Synthetic-2×2 caveat ANSWERED 2026-09-19:** `offline_pairs_le_defect` itself was always fully general (any `RCLike`, any `Fintype`, any Hermitian `A`); the caveat bites only on the `BraggDefect` instantiations, where `f` is a free real and the 29-zero amplitude appears only in a docstring. `QuadrupleDefect.sumPairBlock` extends the block to arbitrary ambient dimension `d`, arbitrary on-line count `m`, arbitrary off-line count `k`, with `defect ≤ k` unconditional (`defect_sumPairBlock_le`) and `defect = k` under independence + orthogonality (`defect_sumPairBlock_eq`). The extension is **free in size, NOT free in the separation hypothesis** — `orthogonality_is_load_bearing` shows the on-line channel can absorb an off-line one entirely (`defect = 0` at `k = 1`). Scope note: `bragg_defect_eq_one`'s single synthetic pair is ONE σ-pair, i.e. half a functional-equation quadruple |
| A2b | engineering | weeks | — | Leakage dictionary as kernel lemmas: completely-multiplicative amplitude ⇒ zero composite Bragg amplitude + the certified DH instance. *Trivial-direction trap flagged: the Λ-support direction is rfl-grade; the content is the log-derivative coefficient functional — statement queued* |
| A2c | open-research | months–years | A2a, A2b, A4 | Defect-in-N instrumentation (torus ladder T3): certified defect under completion sequences — MEASURE, never claim |
| A3 | hard-known-shape | months | **A4-grade zero-counting** (skeptic: the ∅-dependency was wrong — every corridor template consumes N(T+1)−N(T) = O(log T)) | Corridor bound \|ζ′/ζ\| = O(log²T) on zero-avoiding edges |
| A4 | hard-known-shape | months | — | `RvMUnboundedMeanDensity` unconditional + in-kernel (see E6 probe) |
| A5 | **rh-hard-wall** | — | A0, A1e, A2c, A3 | Defect-0 membership of the regularized triple ⟺ RH. Refused decomposition (precedent-mandated) |

**Quadruple caveat — RESOLVED 2026-09-19, and it corrected the W2b gloss**
(`MM_W2B_QUADRUPLE_AUDIT_2026-09-19.md`; artifact `QuadrupleDefect.lean`, axiom-clean).
The caveat was right to fire. Kernel results: (i) `DefectDictionary`'s counter `p` counts
σ-orbits (σρ = 1−ρ̄), and a genuine off-line zero (Re ≠ ½, Im ≠ 0) has a **4-point quadruple
splitting into exactly 2 σ-orbits**, so one off-line zero costs **p = 2**
(`offline_quadruple_sigma_pair_count`); degenerations kernel-checked (real off-line zero ⇒ p = 1,
`quad_real_offline`; on-line ⇒ p = 0, `quad_online_card`). (ii) The **witness dimension per
quadruple is NOT determined by the quadruple** — it is `dim span{y₁,y₂} ∈ {1,2}` — and the
reflection-degenerate evaluation relation `v(ρ̄) = conj v(ρ)` (forced by a node set pointwise
invariant under τ ↦ −τ) makes it **1**: `quadruple_witness_dimension_not_determined` gives two
`Fin 4` configurations with the same on-line channel and two nonzero off-line channels each,
defects 1 and 2. Consequence: `defect ≤ p = 2q` is unconditional, `p ≤ defect` requires the
`NegativeWitness` and **can fail on genuine off-line data**, and the W2b node title/readback were
corrected accordingly (the readback's "Vandermonde-type test vectors keep them linearly
independent" was unproved and is false in general). Residual named obligation:
`QuadrupleChannelIndependence`. A **convention trap** is now named: a half-sum (Im > 0) compression
gives p = 1 per quadruple on the same matrix, so at most one convention can satisfy `defect = p`;
`DefectDictionary` does not fix the convention. **Never-run check:** AKKV
stealthy-hyperuniformity (Invent. Math. 2025) consistency against the zeta comb.

**Assessment (post-skeptic):** A2a/A2b/A3/A4 land with high confidence; A1a ~75%;
A1d perhaps 15–25%/decade (needs a converse-theorem-to-diffraction transplant
nobody has attempted); A1e <5%, generational. The realistic publishable arc:
"the reverse-Dyson program, instrumented" (A2a + A2b + A2c-partials + A1a/A1b).
Verified anchors: KS20 arXiv:2004.05678; OU20 2009.12810; ACV24 2303.03201;
KP degree classification (Acta 182 / Annals 173); Favorov–Değer 2605.10766
(growth dichotomy, *not* reality-forcing); Gonçalves–Vedana 2504.02741 (general
summation-formula classification, no arithmetic clause); Lawton–Tsikh 2403.08659;
Alpöge–Furman arXiv:2608.13637 (Aug 2026; proof credited to Claude, Lean 4 in
anthropics/formal-math `zeta23`; **verified 2026-09-17**): Theorem A(i)
N₀ˢ(T,2T) ≥ (2/3 − o(1)) N(T,2T) unconditionally — **≥** 2/3 simple and on the line
as a liminf, 0.6725 with the Montgomery–Taylor window (the title's "more than"), 5/6
distinct; prior records 5/12 (PRZZ 2020), 0.6603 (Wu 2015); independently re-proved
by Lamzouri arXiv:2609.02882. The "RH ⟺ n₋ = 0 for every finite compression" gloss
is NOT a statement in the paper: it paraphrases the Weil criterion (AF §1.2) plus
Bombieri's (2000) observation, quoted in AF §1.3/§7.1, that a finite truncation's
negative index counts the off-line pairs *seen by that truncation* — cite Bombieri
2000 for it. The signature-(1,1)-per-off-line-pair language is AF item (Z)

---

## 3. ROUTE B — positivity (Weil / Li)

**Terminal:** ∀n λₙ > 0 (⟺ RH; Li 1997, strict) / W-positivity on all admissible
test functions (Bombieri–Lagarias 1999). Corpus face:
`∀ n, 0 ≤ (taylorCoeff riemannXi n).re` via the pinned `li_criterion_rh_iff`.

| id | class | scale | deps | milestone |
|---|---|---|---|---|
| B1 | mechanical | days–weeks | — | Ladder throughput: certified λ-prefix to n ≈ 10³ + honest cost model + negative-control twin. *Cost-model honesty: certified prefixes are morally forced by on-line verification — they are instrumentation, not evidence* |
| B2 | **hard-known-shape** (↓ from engineering, skeptic) | months | — | λ₁ hypothesis-free in-kernel: a TAYLOR COEFFICIENT of log ξ (derivative object), not a function value — `first_zero_kernel`'s template does not cover it |
| B3 | engineering | 1–3 months | — | One kernel-checked Weil–Gram window PSD certificate (Zhu-shaped one-stroke reduction). *Statement not authorable yet — basis/window/tail-budget must be pinned first (skeptic); precision warning: λ_min collapses at the Landau–Widom rate* |
| B4 | **mechanical, with significance warning** (skeptic) | rides the ladder | B3 | Defect-zero on the certified window: near-true by construction (every certified on-line pair contributes a square channel); value is wiring MIRRORMERE inertia onto ANDÚRIL data, not evidence |
| B5 | hard-known-shape | 3–9 months | zero-counting (as A3) | The corridor bound (shared node) |
| B6 | hard-known-shape | 6–18 months | B5 | The T→∞ Weil form as a kernel identity (test-class choice determines the statement; queued until B5) |
| B7 | hard-known-shape | 4–12 months | B6 | Bombieri–Lagarias bridge formalized: (i) finite-multiset positivity core (authorable NOW → `RH_bl_finite_multiset`); (ii) the analytic layer — **admissibility gap flagged**: BL's gₙ are neither band-limited nor compactly supported; the B6→B7 edge needs its own test-class extension |
| B8 | hard-known-shape | 6–12 months | — | Unconditional archimedean trend: the λₙ floor as an all-n theorem (Coffey/Lagarias split; constants must be pinned before authoring) |
| B9 | open-research | 1–3 years | B4, B6, B8 | Growing-support partial positivity past Yoshida/Connes–Consani's 2L ≤ log 2 — doubly-exponential certification cost (Landau–Widom); "grow L" has no known method |
| B10 | **rh-hard-wall** | — | B1, B2, B7, B9 | The uniform tail: all-n / all-support ⟺ RH. *The hcomp exhaustion seam was moved OUT of the wall by the skeptic (opposite-direction inflation): its hypotheses are BL 1999 + classical GW limit passage — known unconditional mathematics awaiting formalization, i.e. hard-known-shape inside B6/B7* |

**Why finite fails, quantitatively** (all verified): Freitas-type delocalization —
a single off-line zero forces infinitely many negative λₙ but the first negativity
is pushable arbitrarily far; the BL identity holds for arbitrary symmetric
multisets (finite faces carry zero zeta-specific content); window certification
cost is doubly exponential in support (Zhu 2608.24827: −ln λ_min(L) ~ Landau–Widom);
the totally-positive tail budget buys ~1 bit per doubling of certified height
(Groskin 2607.02828). **Route-unique value: falsifiability** — `li_neg_refutes_rh`,
`bragg_below_floor_refutes_rh`, and defect-counting give one-directional payloads:
a single certified negative validly refutes RH.

**Corpus errata found here:** `BraggFloor.lean` has rungs 0 and 6–19 only (1–5
missing — the truncation depth cannot clear its own floor at small n);
RvMBraggBridge = 5 theorems + 1 def (not 7); hypothesis-aggregation at scale
(B1 at N=1000 ⇒ ~1000 simultaneous Arb hypotheses) needs a packaging discipline
that does not yet exist.

---

## 4. ROUTE C — de Bruijn–Newman (Λ ≤ 0)

**Terminal:** Λ ≤ 0. With Rodgers–Tao Λ ≥ 0 (Forum Math. Pi 8 (2020) e6 — note:
a corpus doc miscites this as Annals; erratum §8), RH ⟺ Λ = 0: **RH holds with
zero slack under heat flow**. The route's unique honesty property: its
distance-to-RH is a single certified real number.

**The cost curve (corrected 2026-09-17, see `RH_ROADMAP_CLAIMS_VERIFICATION_2026-09-17.md`):**
the Polymath15 barrier (Thm 1.2 of arXiv:1904.12438, Res. Math. Sci. 2019) converts
RH verified to height X/2 in the strip σ ≥ (1+y₀)/2, plus a certified zero-free
canopy at time t₀ and a certified barrier at X, into Λ ≤ t₀ + y₀²/2. Sound anchors:
P15 itself (X ≈ 6·10¹⁰, t₀ = y₀ = 0.2 ⇒ Λ ≤ 0.22) and P15 Table 1 row 2 +
Platt–Trudgian (BLMS 2021, height 3·10¹²) ⇒ Λ ≤ 0.2, the current published record.
Two 2026 computer-assisted claims exist at the same height — Gomila Λ ≤ 0.1787854
(X = 6.000000185827·10¹², t₀ = 129/800, y₀² = 87677/2.5·10⁶; a GitHub audit
repository with a 22-page write-up independently checked by Romik, **not journal-
reviewed**) and Gordon Λ < 0.158 (partial Lean audit conditional on analytic inputs,
not reviewed) — neither is an anchor. The cost curve should be calibrated on P15's
own 12-row conditional Table 1 (§10), which gives Λ·ln T ≈ 5.8 → 5.0 as Λ goes
0.21 → 0.10 (T = assumed verification height): T ≳ exp(C/ε) with C ≈ 5–6, slowly
decreasing, consistent with P15's heuristic Λ ≤ O(1/log T) and Tao's "exp(C′/Λ₀)"
remark; a C fitted through the 2026 points measures numerics quality, not curve
shape. Inverted: ε = 0.1 needs T ≈ 4.5·10²¹ (P15's own figure); ε = 0.01 needs
T ~ 10²²⁰⁺. P15's ninth thread warned of the limits of the Euler-mollifier bounds
near 0.22 at X ≈ 6·10¹⁰, not of a failure below 0.1; the published table certifies
the analytic hypotheses down to Λ = 0.10 conditionally. Unconditional baseline:
Λ < ½ (Ki–Kim–Lee, Adv. Math. 222 (2009)) — any certified bound must beat ½ to be
non-trivial, 0.2 to beat the published record (0.158 to beat the unreviewed one).

| id | class | scale | deps | milestone |
|---|---|---|---|---|
| C1 | **engineering** (↓ from mechanical, skeptic) | weeks | — | Lehmer-pair instrument on the *certified* inventory — the current emitter reads python-flint ordinates (n ≤ 1400), NOT ladder data; consecutiveness requires Turing-method completeness wiring; C_n tail needs an unconditional counting bound |
| C2 | **hard-known-shape** (↓ from engineering, skeptic) | months | — | DBNDefs: Φ, H_t, and H₀ = Ξ/8 — a genuine representation theorem (Mellin ↔ Fourier via Jacobi theta, two IBPs with dominated-convergence justification). *Discipline: do NOT define Λ before C3 (sInf ill-posedness trap)* |
| C3 | hard-known-shape | 1–3 months | C2 | de Bruijn 1950 formalized: t ≥ ½ ⇒ real zeros; Λ exists, Λ ≤ ½. First formalization anywhere |
| C4 | hard-known-shape | 1–2 months | C2, C3 | RH ⟺ all zeros of H₀ real (authorable NOW in AND_ladder grammar); Λ-form follows from C3 |
| C5 | hard-known-shape | 2–4 months | C1, C3 | Csordas–Smith–Varga criterion: certified Lehmer pair ⇒ Λ ≥ −ε kernel theorem (the CSV quality threshold must be re-verified against the 1994 paper — neither session checked it) |
| C6 | engineering | 2–6 weeks | C2 | H_t verified evaluator via the P15 A+B−C effective approximation (never direct quadrature); Γ-factor + finite-Dirichlet-sum = exactly the EM/Stirling object class |
| C7 | hard-known-shape | 6–18 months | C2, C3, C6 | P15 effective estimates + barrier argument formalized (~80pp; the route's one big gamble; Ki–Kim–Lee's asymptotic zero-free region is a load-bearing hidden dependency; the A+B−C validity floor was demonstrated near X = 6·10¹⁰ — G4-scale reuse needs re-derivation, not citation) |
| C8 | engineering | months post-C7 | C4, C7 | Certified Λ ≤ c riding the ladder. *Honesty correction (skeptic): every bound is hypothesis-CARRYING at the Arb enclosure seam (li_rung precedent) — "kernel-certified" claims must say so*. Projected: G1 ~0.36*; G4 ~0.24–0.25*; G5 ~0.17–0.18* (*single-anchor extrapolation) |
| C9 | hard-known-shape | 1–2 years | C2, C3 | (Optional) Rodgers–Tao formalized — the two-sided squeeze. Track, don't staff: consumes pair-correlation infrastructure absent from Mathlib |
| C10 | **rh-hard-wall** | — | C8 | Λ ≤ 0: exp(C/ε) height per rung; RT guarantees zero slack at the limit; the marginality memo's method-class no-go (flow-robust certificates would prove false statements for t < 0) says the arithmetic content must enter non-robustly — outside everything this route emits |

**Assessment:** the best instrument-fit route in the corpus (owns both
consumables: ladder + verified evaluator), with clean firsts available (first
formalized DBN theory, first certified Λ bound) and **no hidden falsity at the
rungs** — every Λ ≤ c is provably strictly weaker than RH. P(route proves RH) ≈ 0;
P(published record-rigor artifact | C7 staffed) 60–75%.

---

## 5. ROUTE D — spectral (Hilbert–Pólya / Connes / Berry–Keating)

**Terminal (corrected by both researcher and skeptic):** not "find the operator" —
bare operator existence is *vacuous* (RH ⇒ diagonal realization; certified by the
cooked-spectrum control D4a). ALL content lives in the completion/positivity
clause, and **the merge with Route B's wall is exact, not analogical**: Li's λₙ
are the Weil form on the test family attached to (1−(1−1/s)ⁿ); B certifies the
wall on a countable subfamily, D on band-limited subfamilies — the same Hermitian
form whose negative inertia `offline_pairs_le_defect` counts.

External state (verified): Connes 1999 (math/9811068) = equivalence, not
mechanism; Connes–Consani 2006.13771 is *"a potential conceptual reason for
positivity"* at the single archimedean place (the "proves positivity" headline
was weakened by the skeptic against the abstract's own language); CCM
2310.18423 + 2511.22755 deliver provably self-adjoint FINITE operators whose
spectra match zeros *numerically*, with the convergence openly identified as the
RH content. BBM 2017 fails on self-adjointness (Bellissard's criticism);
**deficiency indices are intrinsically infinite-dimensional, so no finite shadow
of the BBM failure exists** (the researcher's proposed control was refuted as
vacuous). Conrey–Li 2000: the positivity conditions of de Branges' approach
provably FAIL for zeta — any D8/D9 de Branges work must carry this. The only
face ever cashed (Weil/Deligne, function fields) used positivity via
Hodge-index/Frobenius purity with no Spec-ℤ substrate; Deninger's program
remains a program.

| id | class | scale | deps | milestone |
|---|---|---|---|---|
| D1 | engineering | days | — | Trace reading of the Bragg bridge (finite trace identity packaging → `MM_rect_trace_reading`) |
| D2 | engineering | 1–2 weeks | D1 | Primes-side Weil–Gram matrix. **Correction (skeptic): the bridge has NO archimedean Γ term** — it is stated for uncompleted ζ with edge remainders; the Weil form's archimedean/digamma term must be added from the RvMArch machinery, it is not free |
| D3 | **hard-known-shape, reformulated** (skeptic REFUTED as stated) | months | D2 | ~~Band-limited~~ Weil positivity below certified height: **Paley–Wiener obstruction** — admissible test transforms must be analytic in \|Im\| ≤ ½ to see off-line zeros; band-limited compact support is incompatible. Needs the strip-analytic admissible class formulation first |
| D4 | **engineering** (↓ from mechanical: the BBM sub-item is vacuous and dropped) | days–weeks | D1 | Negative-control battery: cooked-spectrum triviality marker (→ `MM_spectral_cooked_control`) + Euler-factor rung control (exists) |
| D5 | hard-known-shape | months | — | Certified Weyl law = RvM with explicit remainder (the conjectural operator's Weyl law; also the `MM_rvm_unbounded_mean_density` discharge path; statement authored at E6-gate time to match the port candidate) |
| D6 | hard-known-shape | months–quarter | D1, D5 | Corridor bound + full Guinand–Weil in Lean (shared with B5/B6/E7/E8) |
| D7 | **split by skeptic**: evidence-grade matching = engineering; a-priori ε(N) = **open-research bordering wall** (CCM's own abstract: convergence known only numerically — no method template exists) | quarters | D2, D4, D10 | Certified finite-rank arithmetic operator vs. zero data. Certification substrate gap: CCM operators use prolate spheroidal functions — non-rational entries |
| D8 | hard-known-shape | weeks–months | D1 | Hermite–Biehler finite dictionary (with the Conrey–Li failure carried as a named boundary) |
| D9 | open-research | years | D6 | Semilocal trace formula formalized (Mathlib functional-analytic substrate insufficient today; adeles exist, automorphic L-functions do not) |
| D10 | engineering | weeks | D5 | Certified GUE pair-correlation instrument over the ladder (Odlyzko's experiment at certified trust — explicitly evidence-grade, Montgomery's theorem itself assumes RH) |
| D11 | **rh-hard-wall** | — | D3, D6, D7, D8, D9 | Operator-with-completion ⟺ Weil positivity ⟺ RH (merged with B10) |

**Posture:** thinnest route; its terminal is a coordinate change on the wall. Our
marginal contribution to anyone's spectral proof: ~zero. Staff D5/D6 (real,
bounded, cross-route); D1/D2/D4 as cheap layers; D7 behind a design memo; D9
unstaffed. What would change this: a rigorous CCM convergence proof for any
infinite subsequence (the largest RH event since 1974).

---

## 6. SHARED INFRASTRUCTURE — the instrument × route matrix

| Instrument | A | B | C | D | Status |
|---|---|---|---|---|---|
| Certified zero ladder (T=600k → 10⁶ → …) | A2c data | B4 windows | **C8 fuel** (the barrier consumes height) | D3/D7/D10 data | live, climbing |
| Defect instrument (inertia suite) | **A2 core** | B4 = same form | — | D11 = same form | kernel |
| Bragg bridge (finite explicit formula) | A3/A5 substrate | B3/B6 engine | — | **D1 trace reading** | kernel, T→∞ blocked |
| EM/Stirling/DIntv verified evaluator | — | B2 (insufficient alone) | **C6 engine** | — | kernel |
| Li ladder + pinned reduction | — | **B1/B10 spine** | — | D11 via λₙ | kernel (Arb-carrying) |
| Corridor bound \|ζ′/ζ\| = O(log²T) | A3 | B5 | (C7 analog) | D6 | **UNPROVED — the unique four-consumer blocker** |
| RvM unconditional (superlinear count) | A4 | B5 dep | C1 dep (C_n tails, completeness) | D5 | **UNPROVED — five consumers** |
| first_zero_kernel trust template | — | B2 target | C6 target | — | kernel |

**The critical path is not route-specific:** RvM unconditional (E6 probe → else
native A4) → corridor bound (E7) → limit explicit formula (E8). E8 = the
unconditional Guinand–Weil identity at all heights in diffraction form — the
strongest honestly-reachable paper event short of a wall, and load-bearing for
A(A3/A5), B(B6/B7), D(D6). **E8 is hard-known-shape, not engineering** (skeptic):
beyond the corridor bound it needs conditional-convergence bookkeeping (symmetric
zero pairing), and the m-hub/limit-passage pattern applies.

**The E6 probe (highest-value single action):** two external Lean artifacts may
discharge `RvMUnboundedMeanDensity` — the zeta-23-lean line and
cc-chen-tech/riemann-pnt-lean4 (claims a formalized RvM formula). **Go/no-go
gate, not a promise** (the skeptic's "zeta-23-lean does not source RvM" note was itself
WRONG — the 2026-09-17 probe found `Zeta23/RvM/` proves RvM in-repo and Theorem A
supplies the distinct-ordinate input; verdict CONDITIONAL-GO, see `E6_PROBE_2026-09-17.md`): clone → build → `#print axioms`
→ statement-match under the comparator harness → **dependency-closure audit**
(conditional/axiom-carrying uncle theorems disqualify). If it lands: a named
open-research residual becomes an engineering port, W2c completes, E7 unblocks.
If not: A4 native, hard-known-shape, ~2 quarters.

## 7. SEQUENCING — 12–24 months, with tripwires

**Now (parallel):** ① E6 probe (days–weeks, go/no-go). ② A2a wiring (mechanical
— theorems already exist). ③ C2→C3→C4 (the DBN foundations: first-anywhere
formalizations, no wall risk, statement C4 authorable in AND-grammar now).
④ B1 λ-prefix + cost model (mechanical, with its negative-control twin).
⑤ D1/D4 cheap layers (this PR registers their statements).

**Next (gated):** corridor bound E7 (after RvM resolves) → E8 limit formula →
B6/B7 BL bridge → D5/D6 complete. C7 (P15 formalization) is the one big
staffing decision — commit only with a design memo pricing the Ki–Kim–Lee
dependency and the mollifier-era constants risk. A1b zoo extension when W3c
tooling is warm.

**Decision points:** external H_t/RS formalization appears → C7/A3 costs
collapse, re-prioritize W4a. Mathlib lands automorphic L-functions → A1
horizon shortens. CCM convergence proof for any subsequence → drop everything,
verify. E5 fails on a witness class → the one-clause thesis is refuted at
finite grade; reorganize as a route portfolio.

**Falsification tripwires (armed; the program's unique decade-scale non-negligible
payoff is a certified *refutation* if RH is false):** a certified λₙ < 0
(`li_neg_refutes_rh` wired); a persistent band N(T) deficit confirmed by an
off-line winding-1 box; a genuine-data negative defect window; a certified
Bagchi-recurrence lower bound; Lehmer-pair quality → 0 trend on certified
consecutive pairs.

## 8. CORRECTIONS LEDGER (what the skeptics changed)

Report-level (applied above): raw dual-comb temperedness unconditionally false
(e^{R/2} growth) → regularized triple, A0 reclassified; A2a already-proved
(mechanical); A3/B5 hidden zero-counting dependency; A–F ">2/3" → "≥ 2/3";
Alpöge–Furman compression-equivalence gloss unverified; B2 Taylor-coefficient ≠
function-value (hard-known-shape); B4 near-true-by-construction (mechanical,
significance-warned); hcomp seam de-walled (known unconditional mathematics);
B "formalization first" claims downgraded to unverified negatives (PNT+ line
unchecked); C1 not mechanical (wrong ordinate source; completeness + C_n tails);
C2 representation theorem (hard-known-shape); C cost-curve second anchor is an
unreviewed blog (single-anchor extrapolation); C8 bounds are Arb-hypothesis-
carrying; D2 missing archimedean term; D3 refuted as stated (Paley–Wiener);
D4 BBM finite shadow vacuous; D7 a-priori ε(N) has no method template;
CC 2020 "proves positivity" → "potential conceptual reason"; E3/E5
open-research (blocked on queued statements/undefined signature); E8
hard-known-shape; zeta-23-lean RvM sourcing refuted (probe, not port);
Titchmarsh 9.6(A) page-unverified; Λ < ½ (Ki–Kim–Lee) baseline was missing.

**2026-09-17 verification pass** (`RH_ROADMAP_CLAIMS_VERIFICATION_2026-09-17.md`):
§4 cost curve rewritten — Gomila 2026 is a Romik-checked GitHub audit repo, not a
blog, still unrefereed; a second unreviewed claim (Gordon, Λ < 0.158) exists;
calibrate C on P15 Table 1 (C ≈ 5–6, not 4.7–5.0); ε = 0.1 ⇒ T ≈ 4.5·10²¹, not 10²⁰;
the "ninth thread warns below ~0.1" sentence was unsupported. §2 Alpöge–Furman
passage refined — "≥ 2/3" confirmed as Theorem A(i); the finite-compression gloss
is Weil + Bombieri 2000, not an AF statement. §6 E6 — the skeptic's zeta-23-lean
sourcing refutation was wrong (RvM is in-repo); the discharge input for
`RvMUnboundedMeanDensity` is Theorem A (distinct ordinates), not the RvM formula alone.

Corpus errata (for the million-line session): RH_MARGINALITY_LEHMER cites
Rodgers–Tao as *Annals* — actual venue Forum of Mathematics Pi 8 (2020) e6;
RH_CLOSURE_ROUTES_ASSESSMENT §2.3 misstates Zhu; BraggFloor rungs 1–5 absent
(header claims 0–19 coverage); RvMBraggBridge count is 5 theorems + 1 def;
quasicrystal AxiomGuardQC anchor count differs from the "26 anchors" prose;
`MM_rvm_unbounded_mean_density` is kind `lemma` (one report said milestone).

## 9. REGISTRY ACTIONS (this PR) + AUTHORING QUEUE

**Registered as draft** (blind read-back before open; kinds/statuses per
convention): mirrormere — `MM_recurrence_deficit_eq_excess` (E4a),
`MM_offline_disjoint_discs` (E4b), `MM_speiser_box_probe` (E9/W4c pilot box —
NOT the Speiser wall), `MM_rect_trace_reading` (D1, dictionary-grade),
`MM_spectral_cooked_control` (D4a); rh — `RH_bl_finite_multiset` (B7-i),
`RH_li_rung0_kernel` (B2 anchor).

**Deliberately NOT registered — the statement is the work** (three of the plan's
ten nodes were dropped during authoring for exactly the discipline the plan
mandates): `MM_leakage_composite_zero` (the non-trivial content is the
log-derivative coefficient functional; the Λ-support direction is rfl-bait)
— **registered 2026-09-20**, status `draft`, once the statement had actually
been authored and proved: see `examples/quasicrystal/lean/LeakageNode.lean`
and the new `leakage_dictionary` emitter kind; grant awaits blind read-back,
`MM_ks_forward_smallN` (the island's FQ vocabulary is deliberately abstract; a
concrete faithful statement is W3c-formulation work), `RH_rvm_explicit_remainder`
(author the statement AT the E6 gate to match the port candidate; a ball-based
count here would miscount conjugates). Standing queue (unchanged + new): corridor
bound (effective-constant form), W_temp precise statement, A0 regularized
membership, T3 defect rungs, B3 window basis, B6 test class, B8 constants,
C-island Λ definition (post-C3 only), D3 strip-analytic class, D7 design memo.

**Rejected proposals** (recorded with reasons): duplicate defect witness; invalid
kinds (`instrument-lemma`, `cert_family`, `wall`, `conjecture`); bare-literal
statements that would fail blind read-back (LehmerPair-shaped); band-limited D3
(refuted); process-nodes (E6 gate); two-slug entries.

---

*Provenance: every claim above traces to
`research/RH_ROUTES_RESEARCH_2026-09-16.json` (5 reports + 5 adversarial
reviews); literature marked verified was fetched this session; corpus claims were
read against disk. The three in-house refutation precedents governed every
classification. `conjecture1_proved = False`.*
