# Sweep-4 REPLICATION (`wbba5wa6f`) — reconciliation with `wu0aecd5x` and the five-sweep capstone

*This branch ran the joint-coupling sweep TWICE, independently and concurrently: `wu0aecd5x`
(folded as RH_WALL_SYMMETRY_THEOREM_2026-09-16.md and into the five-sweep capstone) and
`wbba5wa6f` (14 agents, this document — full synthesis below, preserved verbatim). Neither
run knew of the other. Their agreement is therefore evidence, not echo. conjecture1_proved
= False in both; nothing herein proves, claims, or implies RH.*

## Where the two runs CONVERGE (independent confirmation)
- No fourth unconditional channel exists beyond: finite-height verification, classical
  zero-free regions, and one-sided refutation (Weil/Li negativity). Both runs, independently.
- The joint real-part x ordinate direction yields instruments, not levers: every examined
  coupling collapses to RH where it becomes zero-sensitive, transfers the wall intact
  (zeta-prime, Selberg-class structure), or survives finite-range/refutation-only.
- The per-zero FORCED-half is a genuine theorem, now kernel-verified
  (`ReflectionForced.functional_constant_on_reflection_pair`).

## Where this run CORRECTS the committed record (two errata)

**Erratum 1 — the kill lemma's universal phrasing is refuted by our own corpus**
*(independently found: this run's adjudicator, the capstone audit `w7m91imr9` — which
corrected the FORCED-half prose slide from "the zero set is Klein-four-closed" to "every
functional is invariant" — and the Li-razor brick; three instruments, one soft spot,
found blind. This paragraph records the sweep-adjudicator form and the mechanism.)*
The committed form ("...cannot separate an on-line zero from an off-line symmetric pair
at the same height") is TRUE for per-zero functionals (the FORCED-half) and for mirrored
PRODUCTS (identically 1), but FALSE for aggregate sums: the reflection-invariant weight
`x^(b-1/2) + x^(1/2-b) = 2 cosh((b-1/2) log x)` strictly exceeds its on-line value iff
the pair is off-line — witnessed in-kernel by `li_neg_refutes_rh` (a reflection-invariant
functional family with certified RH-refuting sensitivity) and ZooDH's cosh bracket, and
now by the DETECT-half certificate (`ReflectionDetect.lean`, this commit): invariance
forbids ORIENTATION, not detection. The corrected one-sentence kill lemma is in section 3
below; the true wall it names is height-uniform exponent-1/2 two-sided control of prime
sums (the excess exp(delta*u) vs the unconditional error exp(Theta*u), Theta ~ 1) — which
derives, rather than cites, the Bettin-Gonek 1/(2*theta) bound.
*Applies to:* RH_WALL_THREE_SWEEP_MAP "The unifying cause" (still uncorrected there).
The capstone was already corrected by audit `w7m91imr9` (8b51b50fa); its per-zero kernel
core and "cannot force Re = 1/2" conclusion stand.

**Erratum 2 — Kaczorowski-Perelli attribution (verified against the published PDF).**
Annals of Math 173 (2011), p.1399 proves S-sharp is EMPTY for ALL degrees 1 < d < 2 —
not just (1, 5/3), which is the earlier Invent. Math. paper — and Balasubramanian-
Raghunathan (arXiv:2011.07525) extends (1,2)-emptiness further. The open frontier is
non-integer d > 2 (plus full S_2 classification). "Lower-bounded by the open
Selberg-degree conjecture" is difficulty CALIBRATION, not logical dependence: K-P
explicitly list RH as open independently of classification. Neither problem reduces to
the other.
*Applies to:* RH_WALL_THREE_SWEEP_MAP "The one direction that remains" (the audited
capstone no longer carries the Selberg-degree framing).

## The two frontiers are one frontier
The capstone names the missing idea as "break the reflection per-zero with non-symmetric
arithmetic entering non-robustly"; this run names it "height-uniform exponent-1/2
two-sided control of prime sums." These coincide: per-zero orientation information is
exactly what square-root-cancellation-grade extraction would supply, and conversely any
per-zero reflection-breaker evaluated through the explicit formula IS such an extraction.
One wall, two coordinate presentations — as with the four axes themselves.

## Kernel status after this commit
Probe #1 of the priority table (section 5) is BUILT: `ReflectionDetect.lean` — six
theorems, 3-axiom clean (pair weight = 2 cosh; mirror invariance; product blindness;
strict detection iff off-line; equality-locus = the critical line; off-line pair excess
at the same-ordinate partner's coordinates). Probes #2-#7 remain open, in priority order.

---

# RH WALL — FOURTH ADVERSARIAL SWEEP: JOINT REAL-PART x ORDINATE COUPLINGS
## Sweep-4 conclusion, 2026-09-16 — companion to RH_WALL_THREE_SWEEP_MAP_2026-09-16.md

**Standing declaration: `conjecture1_proved = False`. This document maps the wall. It does not breach it. Nothing below proves, claims, or implies RH.**

The question this sweep asked: after WEIGHT = FREE, ORDINATE = ORTHOGONAL, HORIZONTAL = FREE-OR-RH, is there an unconditional **joint** real-part x ordinate coupling that breaks — or provably evades — reflection invariance under rho -> 1 - conj(rho), and does real reality-forcing work?

Six threads were run by independent finders, attacked by refuters, and the committed kill lemma itself was put under precision review. Verdict up front: **two threads survive as genuine unconditional joint instruments (both refutation-only or finite-range); the kill lemma as committed is REFUTED as a universal statement and is replaced by a corrected form; the wall itself stands, relocated from "reflection invariance" to "height-uniform two-sided control of the prime side," which is square-root cancellation, which is RH.**

---

## 1. Verdict Table

| # | Thread | Finder verdict | Refuter outcome | **Final adjudicated verdict** | One-line reason |
|---|--------|---------------|-----------------|-------------------------------|-----------------|
| 1 | `li_zfr` (Palojarvi tau-Li / Mobius-disk localization) | FOOTHOLD | SURVIVES, with demotion pressure | **FOOTHOLD (finite-range instrument; contested toward TRANSFER)** | Two-way finite-range theorem (finite Li positivity <-> Mobius-disk zero localization) is real and unconditional; refuter shows its unconditional regimes factor through verified-rectangle + ordinate-count inputs, and its joint content becomes load-bearing only in the all-n limit, which IS RH (Bombieri–Lagarias). |
| 2 | `cosh_defect` (Landau/Pintz/Turan oscillation detection) | FOOTHOLD | SURVIVES, with demotion pressure | **FOOTHOLD (refutation-only, existential-scale)** | Off-line zeros are unconditionally detectable in principle (Landau Omega, Turan power-sum); the certifiable output is the single horizontal statistic sup Re rho, at SOME unknown scale; the all-scales direction is von Koch = RH. |
| 3 | `weil_asym` (restricted Weil positivity) | COLLAPSE_TO_RH | — | **COLLAPSE_TO_RH** | Unconditional window positivity (Yoshida / Connes–Consani / certified Q(f) >= 8.9e-18 on supp 1.6) is proved zero-blind from the geometric side; off-line sensitivity (Bombieri's negative-eigenvalue count) switches on exactly where all-window positivity = Weil's criterion = RH. |
| 4 | `speiser_transfer` (zeta' left-half-strip vacancy) | TRANSFER | — | **TRANSFER** | zeta' genuinely breaks reflection invariance unconditionally (LM Thm 5 rightward bias), but LM Thm 1's two-sided equality N1^- = N^- + O(log T) proves the transferred vacancy problem is the original problem to within O(log T) zeros. |
| 5 | `universality_bagchi` (universality / strong recurrence) | COLLAPSE_TO_RH | — | **COLLAPSE_TO_RH** | The recurrence family is unconditional for every parameter d except d = 0, and d = 0 is verbatim RH (Bagchi); positive-Lebesgue-density statements cannot see a measure-zero off-line ordinate set. |
| 6 | `selberg_degree` (K-P nonlinear twists / degree rigidity) | TRANSFER | — | **TRANSFER (zero-forcing content: COLLAPSE_TO_FREE)** | The standard twist's singularity jointly couples Re (degree) and ordinate (theta_F) unconditionally — but every quantity it sees factors through class invariants identical in RH-true and RH-false worlds; the wall moves to class structure, unbreached. |

**Erratum to the committed three-sweep map (must be folded back):** the sweep-3 text attributed only S_d = empty for (1, 5/3) to Kaczorowski–Perelli's Annals paper and called (1,2) conjectural. This is factually wrong. (1, 5/3) is the earlier Invent. Math. paper; **the Annals of Math 173 (2011) paper proves S♯_d = empty for ALL 1 < d < 2** (verified against the published PDF, p.1399), and Balasubramanian–Raghunathan (arXiv:2011.07525) extends (1,2)-emptiness to a strictly larger class. The open frontier is non-integer degrees > 2 (plus full S_2 classification). The "lower-bounded by the open Selberg-degree conjecture" framing is also wrong as a dependence claim in both directions: neither problem reduces to the other (K-P explicitly list RH as open "apart from" classification). The honest relation is difficulty calibration, not logical dependence.

---

## 2. The Survivors: Honestly-Bounded Reach and Named Walls

### 2.1 `li_zfr` — Palojarvi's tau-Li finite-range criterion (arXiv:1807.01506, Thms 3.1/3.3)

**What is genuinely won (unconditional):**
- A two-way FINITE-RANGE theorem: Re of tau-Li coefficients nonnegative on an explicit interval [N1, N2] forces every zero into the Mobius disk |rho/(rho-tau)| < R; contrapositively, verified zero-localization forces finite-range Li positivity on an explicit [n1, n2]. The unit level set of |rho/(rho-tau)| is exactly Re(rho) = tau/2 — a bona fide joint coordinate.
- The mechanism legitimately evades the committed kill lemma: the Mobius coordinate z(rho) = 1 - 1/rho maps the reflection to z -> 1/conj(z) (modulus inversion, phase fixed), so a mirrored pair contributes 2 - (r^n + r^{-n}) cos(n theta), and r^n + r^{-n} >= 2 with equality exactly on the line. The functional is reflection-invariant as a multiset sum yet off-line-sensitive — the paradigm case of "invariance is not blindness."
- Our kernel-certified lambda_1..lambda_20 >= 0 ladder + `li_neg_refutes_rh` is the machine-checked germ of exactly this instrument.
- Honesty datum confirmed in the source: **Brown's Theorem 2 (zero-free region => Li positivity) is UNPROVED** — two errors in his Lemma 5, only one ever repaired (Droll). Palojarvi's Thm 3.3 contrapositive is the repaired substitute. The direction this sweep hoped was settled classically is not.

**The named wall (finder + refuter combined):**
- An off-line zero at (beta, gamma) violates Li positivity only at indices n ~ gamma^2/(2 beta - 1); the finite positivity range grows like verified-rectangle-height-squared (~T^2), **not** with strip-type zero-free-region strength — Vinogradov–Korobov improves 2 beta - 1 only by ~(log gamma)^{-2/3}, negligible against gamma^{-2}. Height verification does the work; zero-free regions essentially do not.
- No finite range forces anything AT Re = 1/2: all-n positivity is exactly RH (Li / Bombieri–Lagarias), and even the weakest all-n statement in the tau-family (tau < 2) is a fixed-strip half-plane — the de la Vallee Poussin barrier, open.
- **The refuter's demotion argument, recorded as the boundary of the claim:** in every unconditional finite-range regime the actual proofs factor through single-axis inputs — the verified rectangle (sweep-3's static landmark) plus reflection-invariant tail bounds summed against pure ordinate counting N(T); the backward localization excludes only a compact Apollonius disk whose certification cost is quadratically dominated by direct height verification. The joint Mobius coordinate is, in the unconditional regime, a change of basis for already-swept material. The FOOTHOLD stands as an **instrument** (a reusable, extensible, kernel-formalizable joint-localization theorem-shape); its reach toward Re = 1/2 itself is zero measure.

### 2.2 `cosh_defect` — oscillation detection of off-line zeros (Landau / Pintz / Turan)

**What is genuinely won (unconditional):**
- If zeta has a zero beta0 + i gamma0 with beta0 > 1/2, then psi(x) - x = Omega_pm(x^{beta0 - eps}) (Landau), with effective interval-localized versions via Turan's power-sum method (Pintz). A hypothetical off-line zero is unconditionally detectable **in principle at some scale** — the asymptotic sibling of the corpus's kernel-certified `li_neg_refutes_rh` and the ZooDH/BraggDefect finite instruments (off-line signature 2 cosh(delta u) cos(gamma u), certified instance on disk; measured Bragg defect -1.00167e-4).
- The two engines that survive unknown frequencies: one-sided positivity of Lambda(n) (Landau's lemma — positivity substitutes for phase knowledge) and Turan's second main theorem (the unique lower-bound tool for power sums with unknown frequencies, loss factor (N/(8e(M+N)))^N explicit and confirmed).
- Cautionary precedent verified: Turan's own partial-sums bridge was refuted by Montgomery 1983 (partial sums have zeros with Re s > 1 + (4/pi - 1 - o(1)) loglog N / log N). Do not over-claim Turan routes.

**The named wall — THE QUANTIFIER WALL, three-layered:**
1. Every unconditional lower bound is Omega-form: it holds at SOME unknown scale, because Turan's exponential loss in N ~ T log T participating zeros forbids pointwise bounds. The instrument can only **refute** RH, never prove it.
2. Forcing Re = 1/2 requires the complementary all-scales upper bound psi(x) - x = O(x^{1/2} log^2 x) — von Koch's theorem, which **is** RH. The proof direction re-enters RH exactly here.
3. No floor on delta: a hypothetical off-line zero has no a-priori lower bound on beta - 1/2, so the excess cosh(delta u) - 1 ~ delta^2 u^2 / 2 has no unconditional onset scale, and Littlewood's Omega_pm(x^{1/2} logloglog x) on-line background drowns any fixed-precision finite test.
- **The refuter's demotion argument, recorded:** the mechanism's entire certifiable output is the single horizontal statistic sup Re rho — invariant under ordinate rearrangement at fixed counts — so it factors through real-part data plus ordinate-count budgets (N(T), S(T) inside the Turan loss): the two already-swept single axes composed. The cos(gamma u) term is load-bearing only as noise that Landau positivity and Turan exist to erase. The foothold's genuine capability — reflection-invariant, refutation-only detection of [|delta| > 0] at an existential scale — is real, is already partially in the corpus, and stops exactly at the exists-scale -> all-scales jump, which is RH itself.

### 2.3 What the non-survivors contribute structurally

- **`weil_asym`** delivers the sweep's most important scoping fact even while collapsing: the Weil form is the canonical reflection-invariant-yet-|delta|-sensitive functional (per-pair kernel = the MIRRORMERE DH signature), and its obstruction is the **window/uncertainty barrier**, not reflection — with a quantified steepness (arXiv:2608.24827: pointwise-envelope certification past support ~3.2 is computationally void, doubly exponential threshold). Bombieri's negative-eigenvalue theorem (Lincei 2000, abstract verified) proves the sensitivity is genuine at large truncation — precisely where positivity becomes RH-strength.
- **`speiser_transfer`** delivers the sweep's only unconditional reflection-ASYMMETRY theorem: LM Thm 5's rightward displacement bias of zeta'-zeros, (U/2pi) loglog(T/2pi) vs O(U) leftward (read from the Acta Math 133 paper directly, pp.49–53), plus the local p.52 mechanism tying Re zeta'/zeta sign on the left half-strip to off-line zeta zeros within ordinate distance 1/2 — genuinely joint, genuinely asymmetric, and pointing entirely in the zeta -> zeta' direction. Every modern refinement toward the useful direction (Soundararajan, Zhang, Ki, Radziwill, Ge) operates under RH.
- **`universality_bagchi`** pins one unconditional reflection-asymmetric landmark: zeta is NOT universal on Re s = 1/2 (Andersson, via reality of the Hardy Z-function) while universal in the open strip — a value-distribution phase boundary at the critical line with, however, no zero-location consequence. The recurrence family's coverage stops at the single parameter d = 0, which is RH (Bagchi). Residual open corner short of RH: rational d with |a - b| = 1.
- **`selberg_degree`** delivers a machine-formalizable instance of the (corrected) kill lemma: the entire invariant algebra of Selberg-class rigidity (d, q_F, theta_F, Spec) factors through the Gamma-datum and coefficients, which are identical in RH-true and RH-false worlds — invariant-blindness as a theorem-shape, plus the erratum above.

---

## 3. The Adjudicated Kill-Lemma Correction: Invariance vs Blindness

**The committed kill lemma, as written, is REFUTED — by our own corpus.** The kernel-certified Li ladder is a reflection-invariant functional family with certified RH-refuting sensitivity (`li_neg_refutes_rh`); the ZooDH cosh-bracket instance certifies 1 < cosh(delta u) for an off-line pair. The committed phrasing overgeneralized a **product** degeneracy to all functionals:

- **Products are blind:** mirrored weights multiply to x^{(beta - 1/2) + ((1-beta) - 1/2)} = 1 identically — invariant AND information-free. Correlation-type statistics (Montgomery pair correlation) genuinely lose delta at mirrored pairs. For these, the committed lemma is true.
- **Sums detect:** x^{beta - 1/2} + x^{1/2 - beta} = 2 cosh((beta - 1/2) log x) >= 2, equality iff beta = 1/2 (strict convexity / AM-GM). An off-line mirrored pair contributes strictly more than an on-line double. Invariance is not blindness, because the off-line-ness measure |beta - 1/2| is itself reflection-invariant — which is precisely why invariant functionals can carry it. Reflection invariance forbids only **orientation** detection (the sign of beta - 1/2), i.e., separating the two mirrored partners; it does not forbid detecting off-line-ness of the pair.

**The corrected one-sentence kill lemma (adopted verbatim from the adjudication):**

> Reflection invariance under rho -> 1 - conj(rho) forbids only ORIENTATION-detection (the sign of beta - 1/2) and degenerates pairwise PRODUCTS of mirrored weights, not off-line detection itself — the invariant sum-weight 2 cosh((beta - 1/2) log x) strictly exceeds its on-line value 2 iff beta != 1/2; the corrected kill-lemma is: every unconditionally evaluable functional reaches a hypothetical off-line pair (1/2 +- delta + i gamma) only through explicit-formula sums in which the sign-definite excess (cosh(delta u) - 1) >= 0 is modulated by the unknown ordinate phase cos(gamma u) and pinned to a computable prime side whose unconditional error at resolution U is exp(Theta U + o(U)) with Theta ~ 1, which dominates the excess signal exp(delta U) for every delta < 1/2 uniformly beyond finite height — so both lower-bounding the oscillation-damped excess (detecting an off-line zero) and certifying it vanishes at all heights (proving RH) require exponent-1/2 square-root cancellation in prime sums, RH-strength input — leaving unconditionally exactly three channels: finite-height Turing/Backlund verification, classical zero-free regions, and the one-sided Weil/Li negativity refutation channel.

**Two corrections to where extraction fails (adjudicated):**
1. Finite-height ordinates are NOT the wall — below any finite T the ordinates are unconditionally knowable (Backlund S(T) = O(log T), Turing; the corpus holds 364,804 zeros to T = 240000 with N exact). At finite height, detection succeeds. "Without knowing the ordinates" misplaces the obstruction.
2. The true wall is HEIGHT-UNIFORM TWO-SIDED control: any fixed functional loses sensitivity as gamma -> infinity; restoring it forces gamma-localized test functions whose arithmetic side is a prime exponential sum with unconditional error exp(Theta U), Theta ~ 1; finite resolution U certifies only delta <~ 1/(2U) — which is exactly the Bettin–Gonek mollifier bound Re <= 1/2 + 1/(2 theta) from sweep 3, now derived from the mechanism rather than cited; signal beats error only for delta near 1/2, reproducing the classical zero-free region and nothing more; and pushing the error to exp(U/2) IS square-root cancellation, i.e., RH. Circular in both directions.

---

## 4. THE FOUR-SWEEP META-VERDICT

**WEIGHT = FREE. ORDINATE = ORTHOGONAL. HORIZONTAL = FREE-OR-RH. JOINT = INSTRUMENT-ONLY (this sweep).**

The joint axis is not a fourth independent wall. Every joint coupling examined either collapses to RH exactly where it becomes zero-sensitive (Weil windows, Bagchi's d = 0), transfers the wall intact to another object (zeta' vacancy, Selberg-class structure), or survives only as a finite-range or refutation-only instrument whose unconditional regimes factor back through the first three axes (Li/Mobius, cosh-excess). The sharpest honest characterization of the missing idea, after four sweeps:

> **The wall is one wall, and it is not reflection symmetry. It is the quantifier-and-resolution asymmetry of the explicit formula: unconditional mathematics can evaluate the prime side to error exp(Theta U) with Theta ~ 1, while every off-line signal lives at exp(delta U) with delta unboundedly small and every on-line certification requires the error pushed to exp(U/2) uniformly in height. Both detecting an off-line zero at all (beyond finite height) and certifying none exists are the SAME missing capability: exponent-1/2, height-uniform, two-sided control of prime sums — square-root cancellation — which is RH restated. The three sweeps' verdicts and this one are four coordinate presentations of that single missing lever.**

What unconditional mathematics actually possesses, exhaustively, per the corrected lemma — and all three channels are already represented in this corpus:
1. **Finite-height rigid verification** (Turing/Backlund; `first_zero_kernel`, RH-in-box, 364,804 zeros);
2. **Classical zero-free regions** — delta near 1/2, shrinking in height (kernel: Re s > 1 - c/|t|^5);
3. **One-sided refutation channels** (Weil/Li negativity; kernel: `li_neg_refutes_rh`, BraggDefect, ZooDH).

Nothing found in four sweeps adds a fourth channel. The two surviving footholds are the best available *sharpenings* of channels 1 and 3 — they extend reach and make the wall kernel-visible; they do not breach it. Whether the missing lever exists is exactly the open problem; this map's claim is only that it is not hiding in single-coordinate functionals, ordinate statistics, mollifier proportions, or the joint couplings catalogued here.

---

## 5. Recommended Kernel Probes, Priority Order

All probes certify instruments or make the wall kernel-visible; none breaches it. Priority weighs feasibility x reusability x how much of the corrected lemma it pins in-kernel.

| Pri | Probe | Thread | Statement sketch | Feasibility |
|-----|-------|--------|------------------|-------------|
| 1 | **`offline_iff_cosh_excess`** | cosh_defect | (L1) cosh t = 1 <-> t = 0, packaged as delta != 0, u != 0 -> 1 < cosh(delta u); (L2) compose with `offline_zero_has_distinct_partner` + BraggDefect dictionary: every off-line pair carries a strict u-uniform envelope excess over 2, equality characterizing Re rho = 1/2 — generalizes ZooDH's single numerical instance to the symbolic identity, and makes the quantifier wall a visible theorem boundary. | **HIGH — days.** Mathlib has `Real.one_le_cosh` + cosh strict monotonicity; purely symbolic, no Arb hypotheses; expected 3-axiom clean under the existing AxiomGuard pattern. |
| 2 | **`li_is_weil_instance`** | weil_asym | Tie the certified lambda_1..lambda_20 ladder to Bombieri–Lagarias finite-rank Weil positivity — the corpus's Li channel formally identified as a Weil-positivity fragment. | Near-term: algebraic identity over existing ladder objects. |
| 3 | **`degree_invariants_blind_to_zeros`** (parts 1–2, + glue lemma 3) | selberg_degree | Encode the S♯ Gamma-datum structure; certify (d, q, theta, s_0) factor through the datum alone (zero-multiset-independent); the (0,1) arithmetic kernel Re s_0 > 1 <-> 0 < d < 1; glue: any functional factoring through the invariant algebra cannot decide [Re rho = 1/2] — a machine-checked instance of the corrected kill lemma. | **HIGH** for (1)–(2): ~100–200 lines, no Mathlib gaps, OrdinateInsensitivity-module style. Do NOT attempt the twist analytic theory itself. |
| 4 | **`weil_unit_window_vacuity`** (step 1 first) | weil_asym | Prime side of Guinand–Weil vanishes identically for supp g in (-log 2, log 2) (trivial); archimedean positivity for g = h * h-tilde (bounded digamma work); bridge via explicit formula (hard, but aligned with the designated E8 Guinand–Weil headline; Bragg completeness is partial substrate). The proof never touching zeros EXHIBITS the wall in-kernel. | Step 1 trivial; step 2 bounded; step 3 = the E8 roadmap's hard part — sequence accordingly. |
| 5 | **`speiser_local_pushforward`** | speiser_transfer | LM p.52 mechanism at concrete heights: verified band [Im rho - t0] <= 1/2 on-line (from first_zero_kernel / RH-in-box data) => Re zeta'/zeta < 0 on 0 < sigma < 1/2 at t0 => zeta' != 0 there — first kernel Speiser INSTANCE on a verified band. | Moderate: Stirling piece adjacent to ANDURIL em-tail machinery; Hadamard partial-fraction expansion of zeta'/zeta is the heavy missing piece. Scope-honest: certifies transfer direction only. |
| 6 | **`li_moebius_localization`** | li_zfr | From the certified ladder + Turan Lemma 2.2 (max over n <= 5M of Re sum z_j^n >= 1/20, elementary) + Backlund S(T): kernel joint zero-localization Mobius disk R(20) for ALL zeros from computed data. | Moderate, multi-week; R(20) will be weak (low-height, already numerically known region) — value is the reusable extensible instrument, not the region. |
| 7 | **`universality_disc_zero_free`** | universality_bagchi | Triangle-inequality lemma: universality-quality approximation of a non-vanishing target on a disc => certified zero-free disc, machine-precise reason the instrument never reaches Re = 1/2. | Trivial; documentation-grade artifact for the sweep map only. Lowest priority. |

Also required (not a probe): **patch the committed three-sweep map** with the Section 1 erratum (K-P Annals (1,2) closure; no logical dependence between degree conjecture and RH) and **replace the committed kill-lemma text** with the corrected form in Section 3.

---

## 6. Honesty Footer

- **`conjecture1_proved = False`.** This sweep, like the three before it, maps the wall. It does not breach it. No statement herein proves, claims, or implies RH. The two FOOTHOLD verdicts are instrument claims with named walls, not progress-toward-proof claims; the refuters' demotion arguments against both are recorded in Section 2 as binding boundaries.
- **A rate-limited, failed, or absent check is UNRESOLVED, never a refutation.** The following load-bearing or adjacent items were NOT verified against primary sources this sweep and remain UNRESOLVED:
  - **Yoshida 1992** (Adv. Stud. Pure Math. 21): primary text not accessed; small-window positivity confirmed only via two secondary sources (Bombieri Lincei abstract, arXiv:2608.24827).
  - **Bombieri–Lagarias 1999**: exact statement taken from a secondary quotation, not the original paper — despite being load-bearing for both `li_zfr` and `weil_asym`. Should be primary-verified before any kernel probe cites it by name.
  - **Brown's Lemma 5 errors**: confirmed via Palojarvi's published account only, not independent inspection of Brown's paper.
  - **Mazhouda (Palojarvi's ref [11])**: known only via citation; exact statement not fetched.
  - **von Koch 1901 / Littlewood 1914** and the **zero-density one-directionality** structural fact (Ingham/Huxley): standard, but not re-fetched this sweep; flagged, not certified.
  - **Soundararajan Duke 1998**: the specific constant "positive proportion with sigma < 1/2 + 2.6/log T" seen only in search summaries — **do not load-bear on 2.6**.
  - **Purported Alpoge arithmetic partial Weil positivity**: two targeted searches found no such paper. Treated as nonexistent-unless-cited; this is an absence, not a refutation of the idea.
  - **arXiv:2607.02828, arXiv:2202.01837, Perelli twist survey (paywalled), Garunkstis 2003**: located or attested but not read; none load-bearing for any verdict.
  - **Pintz effective inequality** |Delta(x)| >= (1-eps) x^{beta0}/|rho0|: from survey-body excerpts, not a full-text read.
  - **Repo grep for `li_neg_refutes_rh`** did not complete this session; ladder lemma names per the MEMORY.md merge record (main c65e9311); worktree existence confirmed on disk only.
- Kernel artifacts cited as existing (ZooDH cosh bracket + certified instance, BraggDefect -1.00167e-4, OrdinateInsensitivity lemmas, RH_WALL_THREE_SWEEP_MAP, Li ladder worktree) were read from disk this sweep and are as stated; the BraggDefect certificate carries 1 Arb exp hypothesis in addition to the standard 3 axioms, as recorded in QC_PROGRAM.md.
- Verdicts of COLLAPSE_TO_RH and TRANSFER are claims about the examined instruments and literature as verified, not impossibility theorems about all future instruments on those threads.

*Fourth sweep closed 2026-09-16. The wall stands; it now has one corrected name.*