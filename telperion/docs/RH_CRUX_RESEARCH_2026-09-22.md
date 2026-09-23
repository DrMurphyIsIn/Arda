# RH crux research: eight lenses on the wall

*Team report for the workflow `rh-crux-research` (run `wf_6c4fbedf-c32`, launched 2026-09-22 and resumed 2026-09-23) and its arithmetic-geometry rerun `rh-crux-arith-geometry-rerun` (run `wf_ccfd2420-544`). Written 2026-09-23 on branch `cl/crux` of the `arda-cl-crux` worktree (HEAD `62f392c7c`). The companion report `RH_AXIOM_ISOLATION_2026-09-22.md` (the class-P run) is cited wherever the two runs meet.*

*`conjecture1_proved = False`. The Riemann Hypothesis is open. Nothing below proves it, reduces it, or moves any clause of the wall. Every mathematical claim carries one of the tags defined in section 0.4. A claim that no referee or skeptic has seen is labeled as such.*

---

## 0. Honesty preamble

### 0.1 What success meant here

The team was asked for genuinely new, correct mathematics near the crux: a reformulation that is not a relabeling, a new invariant, a no-go theorem about a class of methods, a provable special case, or a structural bridge. Two failure modes were fatal by design:

1. **Circularity, or relabeling.** The new object's key property is equivalent to RH by a short argument, so nothing was gained.
2. **Negative-control failure.** The argument never uses the Euler product, so it goes through verbatim for the Davenport-Heilbronn function D (same functional-equation shape, zeros off the line) or for an Epstein zeta function with off-line zeros. Such an argument is refuted.

An idea counted only if it survived three hostile referees (circularity, D negative control, literature and novelty) with at most one kill. A build counted as verified only if a skeptic re-ran it and failed to refute it.

### 0.2 What happened, in one paragraph

Eight lenses each returned their single best idea. Four were killed (Lee-Yang, total positivity, probability and rigidity, data discovery). Four survived (spectral operator, meta-barriers, dynamics and ergodic theory, arithmetic geometry). The first three survivors were built. All three builds are kernel-checked, none was refuted by its skeptic, and this writer re-elaborated all five of their Lean files (section 3.5). The arithmetic-geometry lens survived only in a separate rerun that had no build phase. No lens produced a route to RH, and none claimed one. What the team did produce is: no-go theorems about classes of methods, three of them kernel-checked; a sharper negative-control zoo, including controls that carry an Euler product and so cannot be dismissed the way D can; a quantitative calibration of the Connes-Consani-Moscovici / Connes-van Suijlekom (CCM/CvS) truncated-Weil pipeline on D; and a list of overclaims caught, some of them in the program's own ledger. By the brief's own standard this is modest new mathematics, mostly negative, and no progress on the wall.

### 0.3 The one idea worth carrying away

*HEURISTIC as a principle. Every instance cited is a theorem or a computation carrying its own tag.*

**Nonnegative von Mangoldt coefficients see real singularities and nothing else.** If Λ_F ≥ 0, then log F is a Dirichlet series with nonnegative coefficients. By Landau's theorem its abscissa of convergence is a real singularity, and F has no zeros to the right of it. For a single Euler factor, written in T = p^{-s}, Pringsheim's theorem gives the same conclusion: every local zero lies to the left of a real local pole. Every rigorous use of positivity this team found is an instance of that one fact.

- **The pole shadow** (THEOREM-kernel-checked in genus one; the general degree is direction D1 below). A local Euler factor with an off-line zero and nonnegative weights carries a real pole at least as far right as the zero. If the factor has no pole in Re s > 1/2, local RH is forced (`pole_shadow`, `local_rh_of_positivity`).
- **The fake zoo** (section 5.4). Every Euler-product control with Λ ≥ 0 and off-line zeros has a real singularity at or to the right of those zeros: a double pole at s = 1, a pole lattice at Re s = 0.861, periodic poles on Re s = 1, poles at 1 ± θ. Every Dirichlet-series control without such a singularity violates Λ ≥ 0 somewhere.
- **Perron-Frobenius** (Lee-Yang lens; THEOREM-paper-proof, confirmed by its circularity referee). Λ ≥ 0 makes the pole-free truncated Weil operator stoquastic. Its simple positive ground state is aligned with the pole vector (squared overlap 0.987 to 0.998, computed). Positivity controls the pole mode. The zeros live in the second level.
- **ζ itself.** Its rightmost real singularity is the pole at s = 1. So positivity alone gives Re ρ ≤ 1, and with the 3-4-1 inequality the de la Vallee Poussin region: the known ceiling.

The Euler product's other rigorous face is the independence of prime phases (probability lens). It yields density statements, such as the Jessen function φ_ζ = 0 and the Bohr-Landau bound N(σ, T) = o(T) for σ > 1/2. Those cannot see a single zero. No lens found a third way for the Euler product to act. This agrees with the dossier's heuristic that arithmetic enters unconditional objects only in capped, aggregate or super-RH form. What is new is the local sharpening (the pole shadow) and a single explanation of every construction in the zoo.

### 0.4 Tags and trust classes

- **THEOREM-kernel-checked**: proved in the Lean 4 kernel, with every `#print axioms` line within `[propext, Classical.choice, Quot.sound]` and no `sorry`; the artifact and a hash prefix are given.
- **THEOREM-paper-proof**: a written proof that survived a hostile referee, or a classical theorem cited as such.
- **CONJECTURE-with-evidence** and **HEURISTIC**: as named.
- **COMPUTED**: floating-point or high-precision numerics, not interval-certified.
- **Arb-certified**: rigorous ball arithmetic, outside the kernel.
- **Writer's sketch (unrefereed)**: an argument first written in this report. Nobody else has checked it.

### 0.5 Provenance, and what this writer re-checked

1. **The synthesis payload was truncated.** The data relayed to this writer was cut at 8,000 characters (dossier), 90,000 (judged ideas) and 30,000 (builds), in mid-sentence inside the dynamics lens. The full records were recovered from the workflow journals: `~/.claude/projects/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/subagents/workflows/wf_6c4fbedf-c32/journal.jsonl` (84 journal lines; the results among them are the dossier, 7 ideas, 21 referee verdicts, 3 builds and 3 skeptic verdicts) and `.../wf_ccfd2420-544/journal.jsonl` (the arithmetic-geometry idea and its 3 verdicts, also committed as `telperion/research/crux_arith_geometry/result_and_referees.json`). The full dossier is also at `/private/tmp/claude-0/crux-arith-geometry/DOSSIER.md`. Every quotation below was matched verbatim against the journals; only nested quotation marks were changed to single quotes.
2. **Upstream truncation.** The workflow gave each referee only the first 14,000 characters of its idea, each builder the first 16,000 characters of idea plus reports, and each skeptic the first 8,000 characters of the build record. Several ideas were longer (the Lee-Yang record is about 26,000 characters), so some statements were never refereed (section 7.1).
3. **Lean re-run, 2026-09-23.** All five build files were re-elaborated with `leanlock.sh lake env lean` on their pinned islands. Every run exited 0 with no errors and no warnings, and every `#print axioms` line is within the standard three (table in section 3.5). A token grep finds the forbidden words only in backticked docstring prose.
4. **Arithmetic spot checks.** This writer recomputed the golden-fake and formal-curve integers (section 3.5). The builds' Python numerics were reproduced by the skeptics, not by this writer.
5. **Independence.** Generators, referees, builders, skeptics and this writer are all subagents of one session. Their independence is self-attested, as the dossier already says of the program's audits.

---

## 1. The crux in one page

*Condensed from the team dossier. Module names in parentheses.*

**What is kernel-proved.** The analytic critical path: unconditional Riemann-von Mangoldt (E6Bridge2), a corridor bound |ζ'/ζ| ≤ C log²T on zero-avoiding segments (E6Bridge3), and the Guinand-Weil explicit formula for smooth compactly supported tests (E6Bridge4). On top of it, the wall is pinned by theorem:

- Weil's criterion in both directions: RH ⟺ Re weilForm(autocorr g) ≥ 0 for every Weil test g (E6Bridge9).
- The wall in two real parameters. With F(c, λ) = Re Σ_ρ m(ρ)(γ − c)² e^{−2λ(γ−c)²}, RH ⟺ F ≥ 0 for all c and all λ > 0, and F = arch − prime, with no zeros in the statement (E6Bridge10).
- Free regions: F ≥ 0 for every c when λ ≤ 3/2000 (E6Bridge30), and whenever |c| ≥ 2π e^{primeAbs(λ)+1/2} (E6Bridge16).
- Effective O2, which needs an on-line spacing floor that provably cannot be dropped (E6Bridge14); the Theta face (E6Bridge17).
- The Li face: Li's criterion (upstream), the Bombieri-Lagarias identity (E6Bridge27), and the ladder "zeros on the line to height T give rungs n + 1 ≤ 2π(T − 1/2)" (E6Bridge29). This gives rungs 0..25128 at height 4000, Arb-conditional, and rungs 0..4 with no hypothesis.
- Zeros to height 640000 lie on the line, conditional on 640 Arb band certificates.

**The wall is three clauses.**

- **(I) A5 = B10 = D11**, one clause in three coordinate systems: Weil positivity for all tests, Li positivity for all n, and the Hermitian form with completion whose negative inertia counts off-line pairs. Its logical form is a bare Π-statement. The honest HAVE/NEED is "there is L0 such that for all g supported in [−L0, L0]" against "for all L, for all g".
- **(II) C10: Λ_dBN ≤ 0** (de Bruijn-Newman). With Rodgers-Tao this is RH ⟺ Λ_dBN = 0, a margin statement on an infimum. It is not formalized here.
- **(III) The residual diagonal** R = {(c, λ) : |c| > T − D, λ > λ0, |c| < envelope(λ)}. It is bounded at fixed λ and unbounded as λ → ∞. Every certifying mechanism factors through certified zeros (finite height) or archimedean dominance (small width).

**What cannot work.** The functional equation alone decides nothing. The FE-uniformity barrier is sound but empty, and survives only as the rule "a lemma with FE-uniform hypotheses cannot be the last step". The Euler product plus a smooth integer count caps at de la Vallee Poussin (Diamond-Montgomery-Vorhauer). Reflection-invariant functionals cannot orient a zero within its pair. Zhu's compact-window theorem: one-stroke pointwise-envelope certificates need frequency cutoffs near 2π exp(4e^L), and the spectral margin collapses (measured). Any c-uniform prime-side bound for Gaussian windows caps at λ = 0.0115. The Li face buys rungs only linearly in the verified height, and an off-line zero is invisible until n ~ t²/δ. The negative controls are D (Arb-certified off-line zero 0.8085171825 + 85.6993484854i), Epstein zeta functions with off-line zeros, finite Euler sections, partial sums of ζ, and the spectral cooked control.

**The four tests applied to every idea.** (a) Is the key property RH-equivalent by a short argument? (b) Is the argument blind to the Euler product? (c) Does it consume only certified zeros or archimedean dominance? (d) Is it reflection-invariant per zero?

**The tool.** Telperion emits exact-arithmetic certificates as Lean, and the kernel checks them. Transcendental data enters only as named hypotheses. Instances certify instances. Every wall clause is universal, so the tool can check a genuinely new uniform argument but cannot manufacture one.

---

## 2. The eight lenses

### 2.0 Scorecard

Referee columns show the score (0 to 10) and whether the referee killed. An idea survives with fewer than 2 kills of 3; survivors are built in order of mean score, at most four.

| Lens | Best idea | Circularity | D negative control | Literature | Kills | Mean | Self-score | Outcome | Built |
|---|---|---|---|---|---|---|---|---|---|
| spectral-operator | Weil-Pontryagin window realization | 3, KILL | 5 | 5 | 1 | 4.33 | 4 | survives | yes, kernel (two islands) |
| meta-barriers | golden-fake barrier | 4 | 5 | 4 | 0 | 4.33 | 5 | survives | yes, kernel (two islands) |
| dynamics-ergodic | "Unitarity = PNT" | 3 | 5 | 2, KILL | 1 | 3.33 | 3 | survives | yes, kernel |
| arith-geometry | formal curves (Barrier III) | 4 | 4 | 3 | 0 | 3.67 | 3 | survives (rerun) | no |
| lee-yang | the Euler product as a ferromagnet | 3, KILL | 3, KILL | 3, KILL | 3 | 3.00 | 3 | killed | no |
| total-positivity | the Schoenberg-Toeplitz zero array | 3, KILL | 3, KILL | 3, KILL | 3 | 3.00 | 3 | killed | no |
| probabilistic-rigidity | barrier invisibility | 3, KILL | 4 | 2, KILL | 2 | 3.00 | 3 | killed | no |
| data-discovery | collision channels | 3, KILL | 3 | 3, KILL | 2 | 3.00 | 2 | killed | no |

### 2.1 Spectral / Hilbert-Polya / de Branges: the Weil-Pontryagin window realization (survives, built)

**The idea.** For a self-dual FE datum F (ζ, D, a Dirichlet L-function) and a window x > 1 with L = log x, take the truncated Weil form QW_x(f) = W_F(f* ∗ f) on L²[−L/2, L/2]. This is the CCM window, and only n ≤ x enter. Its negative index κ_F(x), the Pontryagin index, is finite and nondecreasing in x, and RH ⟺ κ_ζ(x) = 0 for all x. That last statement is Weil's criterion, and the idea flags it as a relabeling. The idea claimed five new things:

1. A Pontryagin version of the CvS real-zeros theorem: the eigenvector at an eigenvalue with κ eigenvalues below it has a Fourier transform with at most κ pairs of non-real zeros.
2. An annihilator lemma that uses only the functional equation: the truncated Polya kernel Φ_x satisfies |QW_x(Φ_x)| ≤ C x^6 e^{−2πx}. This explains the CCM near-kernel without the Euler product.
3. Detection without masking: a simple off-line zero ρ forces a negative square once x ≥ X(ρ) ≈ γ/4 + (1/π) log(1/|ζ'(ρ)|) + O(log(1/δ) + log(1/d) + log γ). There is no maximality hypothesis and no spacing floor.
4. A D calibration: D's window form turns indefinite near x = 31, and its (κ+1)-th eigenvectors locate D's certified off-line zeros.
5. CCM's missing "step 2" splits as [a Locator that uses only the functional equation] and [κ_ζ ≡ 0, which is RH].

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| Circularity | KILL | 3 | "This is a relabeling, killed as a reformulation." The load-bearing statement RH ⟺ κ_ζ ≡ 0 "is Weil positivity restricted to an exhausting family of windows." "The Pontryagin/de Branges formulation adds no new provable partial result about zeta, which is the kill condition." |
| D negative control | no | 5 | "This passes the negative-control test, but only because it is built to." The referee reproduced λ_1(31) = −1.87394e−31 and found that D's second off-line pair is resolved for x in (42, 46]. "The horizon in claim (3) is valid but far from sharp." |
| Literature | no | 5 | "kappa = number of negative squares, counting off-line pairs. This is KNOWN." (Bombieri 2000; the Krein-Langer theory; Suzuki's screw-function papers.) But: "What is genuinely new and valuable: the concrete Davenport-Heilbronn calibration of the CCM/CvS pipeline." |

**Outcome.** Survives with 1 kill of 3 (mean 4.33). Built; see section 3.2. In κ-language, the clause-(I) seam now reads: HAVE κ_ζ(x) = 0 for small windows (Zhu: tests supported in [−0.8, 0.8]); NEED κ_ζ(x) = 0 for every x; and, new in the kernel, κ_ζ(x) ≤ the number of off-line pairs.

**Salvage.**

- *D calibration of CCM/CvS* (COMPUTED; the negative eigenvalues certify indefiniteness if the matrix entries are accurate, but they are not interval-certified). Before its onset, the pipeline reproduces D's own zeros with CCM-grade accuracy (3.9e−27 at x = 30). The even sector turns indefinite for x in (30.5, 31], the odd sector for x in (31.5, 32]. The (κ+1)-th eigenvectors then locate D's off-line zeros. The ledger consequence: CCM/CvS super-accuracy is a functional-equation phenomenon and is not evidence for RH.
- *Annihilator lemma* (THEOREM-paper-proof; the numerics show the scaling poly(x) e^{−2πx} for ζ and poly(x) e^{−2πx/5} for D). It bounds a Rayleigh quotient only. Direction D2 upgrades it to an operator bound.
- *Detection lemma* (THEOREM-paper-proof for one simple zero, after symmetrizing into the even sector; constants not optimized; loose by about 3.5 times on D; the counting version still needs Gram control). See direction D3.
- *Pontryagin-CvS*, built in abstract form with a correction to the even-sector statement (section 3.2).
- *Locator* (CONJECTURE-with-evidence). The build found that the locating property belongs to a near-null cluster of eigenvectors, not to one eigenvector.
- Relabel tags to keep: κ_ζ ≡ 0 ⟺ RH; "step 2 ⟺ Locator and κ = 0" is a remark, not a no-go theorem.

### 2.2 Meta-mathematics / barriers: the golden-fake barrier (survives, built)

**The idea.** A relativization barrier whose model keeps the Euler product. The class P, the "positivity layer", consists of Dirichlet series with c(1) = 1, c ≥ 0 multiplicative, Λ_F ≥ 0, an entire order-1 completion γF symmetric under s ↦ 1 − s (with γ arbitrary, not Γ_ℝ), a simple pole at 1 with positive residue, F ≠ 0 on Re s ≥ 1, and a Chebyshev bound. It also includes the conclusions of every hypothesis-free lemma the corpus has proved about ζ: the dVP regions, LowHeightBox, no real zeros, Li rungs 0..4, E6Bridge30, the envelope, Zhu's window and the local density bound.

There are two models. Model 1 is the genus-one "formal curves" Z_{q,m}(T) = (1 − mT + qT²)/((1 − T)(1 − qT)). The formal Euler clauses give exactly the trivial bound |m| ≤ q; RH for the datum is m² ≤ 4q; the two first diverge at q = 5, where m = ±5 are the "golden fakes", with zeros at 1/2 ± log φ/log 5 plus a vertical lattice. Model 2 is the hybrid H = ζ(s)·Z_{5,−5}(5^{−s}), an ordinary Euler product with Λ_H ≥ 0 and completion ξ·(2cosh((s − 1/2) log 5) + √5).

The claimed Theorem B was that H lies in P and violates RH, so no argument assembled from P can prove RH, and a proof must live in the "rigidity layer": the exact Γ_ℝ completion, holomorphy on Re s = 1 except at s = 1, Ramanujan at every prime, or certified low zeros. The load-bearing open problem was a Beurling-FE fake.

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| Circularity | no | 4 | "VERDICT: the barrier is not circular and not a relabeling. Theorem B is false as stated." "THEOREM B IS FALSE AS STATED: H = zeta(s) * Z_{5,-5}(5^-s) is NOT a P-datum": the pole at s = 1 is double. On the Beurling-FE framing: "Calling it a potential 'genuine proof strategy' is self-deception and must be removed." |
| D negative control | no | 5 | "NEGATIVE CONTROL: PASSES." D is not a P-datum, and the model really keeps the Euler product. "DEFECT 1 (must fix; not fatal). THEOREM B is false as stated." Within this family the double pole is forced. |
| Literature | no | 4 | "VERDICT: SURVIVES, but only as a sharp internal negative control and a program-steering meta-result. It is not new mathematics near the crux." "Worth adopting as a gate; not worth a paper." |

**Outcome.** Survives with 0 kills (mean 4.33). Built; see section 3.3. The build proved the double-pole correction in the kernel, repaired the model (H4), and mapped the barrier's limits.

**Salvage.** The corrected barrier, stated for the corpus's pointwise and Gaussian layers, together with the pole shadow and the lattice limits, all kernel-checked (section 3.3). The Beurling-FE problem survives only in the sharpened form the build gives it (section 3.3, "does not"), and its NO branch contains RH.

### 2.3 Dynamics / ergodic theory: "Unitarity = PNT" (survives, built)

**The idea.** Lax-Phillips scattering on the modular surface X = PSL(2, ℤ)\H. The idea takes the Eisenstein scattering matrix to be φ = ξ(2s − 1)/ξ(2s), a normalization that the referees and the build corrected (section 3.4). The zeta zeros are the resonances s = ρ/2.

- *Instrument.* Group the zeros into functional-equation orbits. Then φ factors as a product of half-plane Blaschke factors, and φ is inner on Re s > 1/2 exactly when there are no uncancelled zeros with Re w > 1.
- *Realizability* (Lax-Phillips, Sz.-Nagy-Foias). Every inner function is the scattering matrix of an abstract Lax-Phillips system, so fakes with off-line zeros in the strip have complete unitary scattering theories.
- *Hecke-wave identity.* On the continuous spectrum, T_p = 2cos(log p·√(Δ − 1/4)).
- *Emergent unitarity.* No finite Euler truncation of φ is unimodular.
- *The no-go.* Every conclusion drawn from unitary scattering data follows from ξ ≠ 0 on Re w ≥ 1.
- *The exchange rate* (flagged as known relabelings): Lax-Phillips decay δ ⟺ horocycle rate ⟺ resonant Satake bound ⟺ ζ ≠ 0 on Re s > 1 − 2δ, and RH ⟺ δ = 1/4.
- *Companion, varying the base point.* If x and y are algebraically independent, E(x + iy, ·) has infinitely many zeros with Re s > 1. So the set of base points where RH holds is closed, null and nowhere dense.
- *Side finding.* The program's `arb_dh.py` winding count is not rigorous as written.

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| Circularity | no | 3 | "But almost everything in it is a relabeling or folklore, and the headline NO-GO is overstated. It should not ship with the tag THEOREM-paper-proof." Also: "The literal sentence 'channel data cannot be told apart from those of xi' is false, since phi_Lambda != phi_xi." Errors found: the scattering-matrix normalization; a common pole at s = 1/2 in "emergent unitarity"; 2i ∈ T_2(i) has class number 1. |
| D negative control | no | 5 | "This passes the negative control. It is a no-go theorem, not a route to RH, and walking it through Davenport-Heilbronn and Epstein comes out the way the theorem predicts. Its one real use of the Euler product is nonvanishing on sigma >= 1, and that use is load-bearing." Also: "The Birman-Krein positivity claim is false for the actual scattering matrix of the modular surface." |
| Literature | KILL | 2 | "KILL on novelty, not on correctness." The base-point companion is Proposition 1 of Strömbergsson-Södergren (arXiv:1305.1333, Math. Ann. 2017). The scattering side is Lax-Phillips, Pavlov-Faddeev, Sarnak 2004 and Gelbart-Lapid-Sarnak. |

**Outcome.** Survives with 1 kill (mean 3.33). Built; see section 3.4. The build made the no-go precise (`ChannelAxioms`) and proved the corrections.

**Salvage.** The kernel-checked channel no-go and its negative-control fake ξ·Q_{3/4+20i}. Contractivity of ξ(2s − 1)/ξ(2s), proved in the kernel. The fact that Birman-Krein positivity is exactly the σ = 1 slice of the rational face. Arb-certified Epstein off-line zeros at points of the Hecke orbit of i. The winding-count tooling fix. The design rule: a dynamical attack must use cusp-form or trace-formula data at the exact arithmetic point, or non-unitary resonant arithmetic, which is quasi-RH.

### 2.4 Arithmetic geometry: formal curves and Barrier III (survives in a rerun, not built)

**The idea.** Which ingredient of Weil, Deligne or Bombieri-Stepanov has no analogue over Spec ℤ? The lens answered with a complementary toy. A *formal curve* over F_q is a self-reciprocal P ∈ ℤ[T] of degree 2g such that Z(T) = P/((1 − T)(1 − qT)) is an honest Euler product ∏_d (1 − T^d)^{−a_d} with every a_d a nonnegative integer. Formal curves carry every zeta-level ingredient: exact FE, the Euler product, integer counts, a q-symplectic Frobenius lattice, a formal square, and an exact radical in the window-2g Toeplitz form. They lack every space-level object.

- *The family.* F(q, m): P = 1 + mT + (m² − q)T² + qmT³ + q²T⁴ is effective for 2√q < m ≤ m*(q), where m*/q → 2^{−1/3}. It has non-real off-line Frobenius eigenvalues at angles ±2π/3, and Re ρ_max = 1 − (log 2)/(3 log q) + o(1/log q).
- *The golden fake F(5, 5).* Re ρ = 0.79899, class number 76. The Weil bound holds at the first two Frobenius powers and fails at the third.
- *Barrier III.* Nothing uniform over (Euler product + exact FE + entire order-1 completion) proves RH, or even a zero-free strip.
- *The periodicity delimitation.* A Beurling system with all norms in q^ℤ cannot carry π^{−s/2}Γ(s/2).
- *Next target.* A "Beurling-Hamburger rigidity" conjecture.

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| D negative control | no | 4 | "NEGATIVE-CONTROL REFEREE: PASS, but only because the idea makes no claim about zeta." "'The polarization is the unique missing ingredient' is therefore a definition, not a finding." "Barrier III has a narrow scope." "The Connes corollary attacks a straw man." |
| Circularity | no | 4 | "The headline family is superseded by genus 1": genus one with a = q already has Re ρ ≈ 1 − 1/(q log q), which reaches 1 faster. "Statement 4 is a tautology dressed as a finding." On the delimitation: "The escape set is 'anything non-periodic', which is far larger." |
| Literature | no | 3 | "VERDICT: keep, low value (3/10). The math is correct and the key numbers check out. As a pure-math contribution it is mostly folklore." The Beurling-Hamburger claim is probably covered by Bochner 1951, Bochner-Chandrasekharan (Ann. Math. 1956) and Chandrasekharan-Mandelbrojt 1957; the referee did not confirm this. |

**Outcome.** Survives with 0 kills (mean 3.67), but only in the rerun: the main run's generator failed twice, the second time on the 128k output cap. The rerun had no build phase, so nothing here was built or skeptic-checked. All three referees independently reproduced the F(5, 5) integers, and so did this writer (section 3.5).

**Cross-reference.** The sibling class-P run proved on paper, by three routes, that a positive Beurling measure with ζ's exact conductor-1 FE is the integers (Collapse B / Theorem A; Step 3 is kernel-checked conditional on a pairing identity; novelty unverified). So this lens's "next target" is now a THEOREM-paper-proof in `RH_AXIOM_ISOLATION_2026-09-22.md`, subject to that report's caveats.

**Salvage.** A `FormalCurveControl` emitter (exact integers, kernel-cheap; section 6.3). Barrier III, always stated with the qualifier "arbitrary (q-periodic) completion". The periodicity lemma. The window-4 Toeplitz illustration for F(5, 5): the numerator lies in the kernel, yet the minimal eigenvalue is −8.22, and the Caratheodory-Fejer nodes sit at the wrong angles. That is a demonstration, not an obstruction to arXiv:2602.04022.

### 2.5 Statistical mechanics / Lee-Yang: the Euler product as a sign-problem-free ferromagnet (killed)

**The idea.** Split the truncated Weil form on [−a, a] (a = log λ) as Q_λ = P + H_λ.

- P = 2A(f)B(f) is the rank-2 pole kernel: +2⟨f, c⟩² on even f and −2⟨f, s⟩² on odd f, where c = cosh(x/2)·1_I and s = sinh(x/2)·1_I.
- H_λ = c0 + D_K − 2Π_λ is the pole-free Weil operator. Here D_K is the Markovian Dirichlet form of the archimedean kernel K(y) = e^{y/2}/sinh y, and Π_λ is prime hopping by log n with weight Λ(n)n^{−1/2}, for n < λ².

The claims:

- (A) Λ ≥ 0 is exactly the Beurling-Deny condition, so H_λ is stoquastic and has a simple, even, positive Perron-Frobenius "condensate" aligned with the pole vector.
- (A′) The condensate's Fourier transform is real-rooted, a proven Lee-Yang family. But its zeros sit near kπ/a, not at zeta zeros.
- (L) Landau's theorem, read as a Lee-Yang classifier: D and Epstein zeta functions must be frustrated.
- (B) Unconditional criticality: the second levels are within Cλ^B e^{−2πλ²} of 0 at every volume, and the pole strength t = 1 is rigid.
- (C) RH ⟺ "H_λ binds no second state" plus exact pole compensation. The idea itself flags this as a relabeling.
- (E) D's form turns negative between λ² = 33 and 55, at its off-line ordinates.

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| Circularity | KILL | 3 | "VERDICT: the load-bearing step is a relabeling of Weil positivity, and the idea says so itself in (C)." And: "Warning: Q = H + P is NOT stoquastic." P is antiferromagnetic on the even sector. |
| D negative control | KILL | 3 | "KILL as a route toward the crux. It fails the negative-control test on DH: the one place it uses the Euler product has no effect on the zeros, and every step that touches the zeros goes through for DH." Numerically, D's frustrated operator also has a simple, even, nodeless ground state at λ² = 3 to 20: "So being stoquastic is sufficient but not necessary for the Perron-Frobenius picture." |
| Literature | KILL | 3 | "Summary: the pieces that sit near the crux are already in print or follow in a few lines from published results. The one step that uses the Euler product produces a family the idea itself says is the wrong one." The parity split of P is Lemma 6.1 of Zhu, arXiv:2608.24827. |

**Outcome.** Killed, 3 kills of 3 (mean 3.00).

**Salvage.**

- The decomposition Q = H + P, with H stoquastic exactly when Λ ≥ 0 on n < λ² (THEOREM-paper-proof; Beurling-Deny plus Jentzsch; new only as framing). It is one of the rigorous instances in section 0.3.
- A self-contained proof, by the Krein-Pisarenko zero-reflection argument, that any simple ground state of a translation-invariant form on an interval has a real-rooted Fourier transform (THEOREM-paper-proof, per the circularity referee). This removes the dependence on the unread CvS Theorem 6.1. Build A proves a stronger version in the kernel by isotropy.
- Pole-strength rigidity: for t ≠ 1, H_λ + tP is not PSD for large λ (THEOREM-paper-proof; elementary and FE-uniform; not a Rodgers-Tao analogue).
- The D lesson (COMPUTED by the negative-control referee): "simple, even, nodeless ground state" is not an arithmetic signal.
- Claim (D), nodelessness of the CvS ground state, stays CONJECTURE, because Q is not stoquastic.

### 2.6 Total positivity / Laguerre-Polya: the Schoenberg-Toeplitz zero array (killed)

**The idea.** For h ≥ 0 put F_h(x) = [ξ(1/2 + h + √x) + ξ(1/2 + h − √x)]/2 = Σ b_j(h) x^j, where b_j > 0. Study the Toeplitz minors D_m(k; h) = det[b_{k+i−j}(h)]_{0≤i,j<m}. By dual Jacobi-Trudi these are rectangular Schur functions of the reciprocal roots, and by Aissen-Schoenberg-Whitney-Edrei, RH ⟺ F_0 ∈ PF_∞. The claims:

1. *Order-angle duality.* A quadratic factor at angle θ is PF_m iff θ ≤ π/(m+1). Hence *blindness*: PF_m certificates cannot see zeros at angle ≤ π/(m+1).
2. *A per-zero row criterion.* Row k oscillates in m iff roots k and k+1 form an off-line conjugate pair.
3. *An empirical detection law* m* = (π + Δ)/φ.
4. *An edge band where the Euler product enters.* A local de Bruijn lemma plus the effective dVP region make F_h PF_m up to a bound M_h that grows doubly exponentially as h → 1/2.
5. *The bounded-order corner is blind by construction.* This is the corner of Griffin-Ono-Rolen-Zagier and Katkova.

The D control was run directly. Row 44 of D's array first goes negative at m = 664, inside the predicted window (435.3, 872.7]. The neighbouring rows stay positive to m = 900, with agreement at 1500 digits.

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| Circularity | KILL | 3 | "VERDICT: this is a relabeling as far as RH is concerned. Most of the stated lemmas are correct, but the claimed THEOREM in statement 8 has a real gap, and none of the partial results adds any information about where the zeros are." The row criterion is Hadamard's 1892 Hankel theorem (qd theory), not a new use of Deift-Its-Krasovsky. |
| D negative control | KILL | 3 | "KILL as a step toward the crux. The load-bearing step fails the Davenport-Heilbronn (DH) negative control, and the rest of the proposal is either classical or a zero-by-zero restatement of RH." The Euler product enters only as the strip constant δ_max = 1/2. |
| Literature | KILL | 3 | "This should die as a headline contribution. Its three main claims are already in print or follow in one step from classical theorems." Katkova (CMFT 2007) already notes that her method cannot prove RH, because it uses only nonvanishing in the strip. |

**Outcome.** Killed, 3 kills of 3 (mean 3.00).

**Salvage.**

- *The edge band* (THEOREM-paper-proof; it is about F_h with h > 0, not about ξ). For 0 < h < 1/2, F_h is PF_m for m ≤ ⌊π/(2 arctan(√(1/4 − h²)/X_h))⌋ − 1, where X_h = max(T_ver, exp(c/(1/2 − h))) − 1/2. The Euler product enters only through the zero-free region.
- *The local de Bruijn identity.* |z+ih−w|²|z+ih−w̄|² − |z−ih−w|²|z−ih−w̄|² = 8yh[(x−u)² + y² + h² − v²], checked symbolically by one referee and numerically by another.
- *An erratum candidate.* Katkova's rectangle 0 ≤ Im s ≤ 14 gives PF_43 under her Theorem B indexing, since π/(2 arctan(1/28)) = 44.001; she states PF_44. This must be checked against her conventions.
- *Blindness*, as a no-go only for certificates that are global in the angle (THEOREM-paper-proof; Schoenberg 1955 plus Cauchy-Binet).
- *The Hadamard/qd row detector*, as a negative-control instrument (COMPUTED).
- *A Lean target:* the finite Schoenberg Theorem B.

### 2.7 Probability / random models / rigidity: barrier invisibility (killed)

**The idea.** Where does the Euler product show up in statistics?

1. *Phase-harmonicity.* log|∏_p (1 − X_p p^{−s})^{−1}| is pluriharmonic in Haar-random phases, so its mean is 0. A D-type two-term sum has a strict Jensen excess instead. This is the classical Jessen function, φ_ζ = 0 against φ_D > 0 on σ > 1/2. It is a density-level invariant, blind to a single zero. The three one-prime lemmas are kernel-checked in scratch.
2. *The Bohr-Jessen barrier law.* Write λ = κ log(T/2π) in the Gaussian-derivative coordinates. The random model of the prime side has Var = (32πλ²)^{−1}(1 + o(1)) and A/sd = (1/2)√(log(T/2π)/κ). So it crosses the archimedean barrier T^{1−1/(8κ)+o(1)} times per dyadic block. For κ > 1/8 it "predicts" Weil violations while matching every moment of order below 2/κ.
3. *An experiment.* On zero windows at T = 1e5, 3e5 and 6.3e5 (15,679 zeros; 372 of 372 Turing-band counts matched), the model reproduces the bulk law of F/A. Near the barrier the truth follows GUE, and the certified truth has 0 crossings where the model predicts 5.4, 186 and 1111.
4. *The residual (III) splits at c = 2π e^{8λ}.*

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| Circularity | KILL | 3 | "The decisive experiment KS5 proves nothing." With real zeros, F is a sum of nonnegative terms, so the 0 crossings, the GUE value P(F < 0) = 0 and the e^{−186} figure "are all automatic once zeros are real." The moment no-go is folklore, and the region split is overclaimed as a theorem. |
| D negative control | no | 4 | "NEGATIVE-CONTROL VERDICT: survives. That is only because the idea is a no-go / meta result and never claims a route to RH." The random model breaks the functional-equation coupling between the prime side and A (Gonek-Hughes-Keating). |
| Literature | KILL | 2 | "KILL. There are no internal errors, but nothing here is new in print and nothing gets closer to the crux." Parents: Hughes-Rudnick (mock-Gaussian behaviour), Gonek-Hughes-Keating, Diamond-Montgomery-Vorhauer. |

**Outcome.** Killed, 2 kills of 3 (mean 3.00).

**Salvage.**

- The barrier-law constants (THEOREM-paper-proof for the exponent, and about the model only). Both referees recomputed them. One correction: the fourth cumulant decays like λ^{−2}, not like e^{−c√λ}.
- The region split, as a dead-end map. Moment and random-model certificates for clause (III) are hopeless in Region II (T_cert < c < 2π e^{8λ}, nonempty iff λ > 1.44 at T_cert = 640000). HEURISTIC to paper sketch.
- The D control for the F functional: F_D(85.699, λ) < 0 for λ ∈ {0.5, 1, 2, 3}, reproduced by the referee.
- The three Jensen lemmas (scratch Lean, outside the skeptic filter), usable as negative-control bricks.
- A late fact: the κ = 1/2 Monte Carlo at T = 6.3e5, which the literature referee found empty, completed after refereeing. Across six replicates it shows 179 to 203 barrier violations per 3000-unit window (mean about 191), against the Rice estimate of 186. Nobody has reviewed it.

### 2.8 Experimental mathematics: collision channels (killed)

**The idea.** Hunt for a regularity of ζ that D violates even away from its off-line zeros. The honest outcome is that none was found. What the experiments produced:

- (A) D is exactly the even part of one Euler product's Hardy function: Z_D(t) = (√(1+κ²)/2)[Z_χ(t) + Z_χ(−t)] with χ mod 5, checked to 5.9e−16. Its 8 off-line pairs with γ ≤ 400 sit where the zero sets of L(χ) and L(χ̄) fail to interlace.
- (B) A two-zero collision rule: f(t+b) + f(t−b) keeps a zero pair of gap g real iff g ≥ 2b.
- (C) V_b = ξ(s+ib) + ξ(s−ib) has an exact FE and is built from ζ, yet it loses real zeros at positive density, with a loss curve that matches CUE (Δ(u) ~ (2π²/9)u³).
- (D) E_θ = ξ(s+θ)ξ(s−θ) has an FE, an Euler product and Λ(n)(n^θ + n^{−θ}) ≥ 0, yet every one of its zeros is off the line.
- Synthesis: off-line zeros arise from the collision of two constituents or from non-unitary splitting. A "unitary half-gap law" is RH itself for ζ, and the idea declares it circular.

**Referee verdicts.**

| Referee | Kill | Score | Decisive objection |
|---|---|---|---|
| Circularity | KILL | 3 | "This should be killed as a claim of new mathematics near the crux. It is worth keeping only as a set of negative-control fixtures." The claim that equality in the half-gap law is attained by E_θ presupposes RH. |
| D negative control | no | 3 | "FATAL for the headline SYNTHESIS". The two-channel picture "is refuted by Selberg zeta functions": a compact surface with an exceptional eigenvalue gives a third channel. |
| Literature | KILL | 3 | "This idea is killed as a contribution near the crux. Every structural claim in it is either the definition of something already known, folklore already in print, or elementary." |

**Outcome.** Killed, 2 kills of 3 (mean 3.00).

**Salvage.**

- *Three fixtures for the negative-control battery.* D with its 8 located off-line pairs; a referee re-confirmed two of them to 1e−32, with their reflected partners. V_b, a zeta-built FE object with positive-density off-line zeros. E_θ, the standard non-tempered Eisenstein example behind the Selberg class's Ramanujan axiom.
- *The referee's fourth control*, the Selberg zeta of a surface with an exceptional eigenvalue. It refutes the half-gap law as stated. A normalization remark by this writer (HEURISTIC reading of classical facts): with Λ ≥ 0 normalized as for ζ, the relevant object is the Ruelle zeta R(s) = Z(s+1)/Z(s). There the exceptional eigenvalue is a real *pole* of R at s_1 ∈ (1/2, 1), not a zero. That is the pole shadow again (section 5.4).
- *Lean corrections before the scratch file lands.* `eisShift_violates_RH_analogue'` carries the hypothesis `hzero : ∃ ρ, riemannXi ρ = 0`. `shifted_vonMangoldt_nonneg` proves that an expression is nonnegative, not the coefficient identity. `eisShift_eulerProduct` is about ζ·ζ, not ξ·ξ.
- *The dossier's untested non-self-dual lane is closed* (THEOREM-paper-proof, standard). Any L(s, π) with Λ(s, π) = εΛ(1 − s, π̃) has a zero set invariant under ρ ↦ 1 − ρ̄, so it supplies no new reflection-breaking.
- *V_b deficit universality*, kept as CONJECTURE-with-evidence. It is off the crux.

---

## 3. What was built and verified

Only skeptic-unrefuted builds count as verified. There were three builds, and none was refuted.

### 3.1 The three builds

| Build | Lean artifacts | Islands | `#print axioms` lines (writer's re-run) | Research directory | Skeptic |
|---|---|---|---|---|---|
| A. spectral-operator | `li_positivity/lean/Crux/Crux_spectral_operator.lean` (823 lines, sha256 `a74ec1dc3ce975ad…`); `rvm_bridge/lean/Crux/Crux_spectral_operator.lean` (335 lines, `bbacd4cea1dcd37a…`) | li_positivity: Lean v4.34.0-rc1, Mathlib `de5ce8a9`. rvm_bridge: Lean v4.33.0-rc2, Mathlib `51e6992e`, Zeta23 `fbdc36bb` | 32 + 22, all within the three | `research/crux_spectral-operator/` | not refuted |
| B. meta-barriers | `li_positivity/lean/Crux/Crux_meta_barriers.lean` (2035 lines, `a0edcb5478bd985c…`); `rvm_bridge/lean/Crux/Crux_meta_barriers.lean` (1478 lines, `90753c991b9ef9bb…`) | both | 161 (4 of them use no axioms) + 88 | `research/crux_meta-barriers/` | not refuted |
| C. dynamics-ergodic | `li_positivity/lean/Crux/Crux_dynamics_ergodic.lean` (1492 lines, `a8661de490b19f47…`; md5 matches the builder's `bb8ac941…`) | li_positivity | 94 | `research/crux_dynamics-ergodic/` | not refuted |

Paths are relative to `telperion/examples/` and `telperion/`. Every file is untracked on `cl/crux`. None is in a lakefile, a CI job or an AxiomGuard target.

### 3.2 Build A: the Weil-Pontryagin core

**THEOREM-kernel-checked, abstract, li_positivity (namespace `Crux.SpectralOperator`).**

- `chain_isotropic_line`, `chain_isotropic_circle`. Suppose multiplication by z is B-symmetric (on the circle, B-isometric) and E lies in the radical of B. Then the Jordan chains R = E/(z − α)^k attached to zeros α of E with ᾱ_i ≠ α_j span a totally B-isotropic subspace.
- `card_le_of_isotropic`, the Pontryagin inertia lemma. An independent, totally isotropic family whose span meets the radical only in 0 has at most κ members whenever `NegIndexLE B κ`.
- `pontryagin_cvs_line` (with `_lower` and `_pos`). The zeros of E in the open upper half-plane, counted with multiplicity, number at most the negative index of Q − λ. `no_upper_zeros_of_psd` is the case κ = 0: the CvS real-zeros theorem, with no discretisation and no Hurwitz argument, given the hypotheses listed under "does not".
- `iohvidov_krein_circle` (with `_outside`): the finite Iohvidov-Krein bound. `galerkin_pontryagin_cvs`: the same count for any Hermitian matrix with displacement structure (Ω_i − Ω_j)Q_ij = ℓ_i ḡ_j − g_i ℓ_j.
- `zeroSide_negIndexLE`: a nonnegative form plus k hyperbolic pair terms has negative index at most k. `detector_pair_term_le`: the detector's pair value −Re(X²)/(2δ²) is at most −|Ξ'|²/2 for a suitable real a. `isNegFamily_of_diag_dominant`: almost-orthogonal detectors, in Gershgorin form, give κ ≥ m.

**THEOREM-kernel-checked, about the real zeta Weil form, unconditional, rvm_bridge (namespace `CruxSpectralOperator`, importing E6Bridge9).**

- `weilSesq_hasSum`: B(f, g) = Σ_ρ m(ρ) f̂(γ_ρ) conj ĝ(conj γ_ρ). `weilSesq_deriv_symm`: B(f', g) + B(f, g') = 0.
- `weil_negIndex_le_offline`. Let S contain one member of each off-line pair {ρ, 1 − ρ̄}. Then any family of Weil tests spanning a negative-definite subspace has at most |S| members. `kappaWindow_le_offline` and `kappaWindow_mono` give the same bound window by window, and show that κ(x) is nondecreasing. If there are infinitely many off-line zeros, no such S exists and the bound says nothing. Under RH it says only κ = 0.
- `rh_iff_weil_negIndex_zero`: RH ⟺ κ = 0. It is recorded, and labeled as a relabeling of Weil's criterion.

**COMPUTED** (mpmath, 40 to 200 digits).

- New closed forms for the odd sector; there the ζ pole term is −8 b_j b_k, negative semidefinite. The displacement residual is at most 1.2e−40 in both sectors, for ζ and for D. Brute-force entries agree to 8e−25, and the even sector agrees with the idea's code to 3.7e−40.
- D's onset of indefiniteness. The even sector turns in (30.5, 31]: λ_1(31) = −1.8739357e−31, stable to 8 digits under changes of precision and quadrature, and more negative at N = 70 and 80. The odd sector turns in (31.5, 32]. By x = 60 each sector has κ = 2. The (κ+1)-th eigenvector of each sector locates both certified off-line zeros of D: 85.6993484854 + 0.308517182457i to 12 digits, and 114.16334 to about 1e−6. Eigenvectors κ+1 through κ+3 of both sectors carry these zeros.
- Finite Toeplitz and Hankel models: 0 violations among 51,755 eigenpolynomials, with the bound attained in 14,993 of them. The annihilator scaling behaves as stated. An independent Legendre discretisation agrees at x = 60.

**A correction to the idea** (COMPUTED; the kernel theorem explains it). The even-sector form of claim 2, "at most κ_even pairs of non-real zeros", fails for Galerkin truncations. For D at x = 40, N = 60, the even ground state has κ_even = 0 and a zero pair at ±27.5057i. The corrected statement is the one the kernel supports: first-quadrant zeros number at most κ_even, imaginary-axis zeros at most κ_even + κ_odd, and the full-space upper-half-plane count at most κ_full. The violations vanish under refinement (none at N = 70 or 80), so the even-sector statement for the untruncated operator is open.

**What it does not establish.** Anything about κ_ζ(x) = 0, which is RH. The Locator. The analytic half of detection. The functional-analytic glue: Paley-Wiener division, form domains, and eigenvalue counts against `NegIndexLE` via Courant-Fischer. These enter the abstract theorems as hypotheses. An interval certificate for D's onset. The annihilator lemma in Lean. Any priority for the continuous K > 0 statement, which sits in Krein-Langer and Kaltenbaeck-Woracek territory; no literature search was run.

**Skeptic.** "I found nothing that refutes the build. I re-ran both Lean files and the main numerics myself." Its caveats: the displacement vector g is fitted, not derived; the x = 31 onset is not interval-certified; for Galerkin matrices only the first-quadrant count is kernel-checked; the continuous statement is close to known Krein-school results.

### 3.3 Build B: the golden-fake barrier, corrected and bounded

**THEOREM-kernel-checked, li_positivity (namespace `CruxMetaBarriers`).**

- *Genus one.* `admissible_iff`: for q ≥ 2, the formal Euler clauses (N_1 > 0, a nonnegative degree-two place count, N_n ≥ 0 for all n) hold iff |m| ≤ q. `N_pos_of_abs_le` gives the positivity half for every q, via the Lucas identity t_n² − (m² − 4q)U_n² = 4q^n. `rh_int_iff_zeros`: RH for the datum holds iff m² ≤ 4q. `exists_admissible_not_rh_iff`: an admissible RH-violating datum exists iff q ≥ 5. `hasse_iff`: Hasse/Rosati positivity ⟺ RH, a relabeling at this level, as the proposal said. `N_eq_det`: N_n = det(A^n − 1), the toral-endomorphism model.
- *The fake's zero set.* `XiA_eq_zero_iff`: XiA(s) = 2cosh((s − 1/2) log 5) + √5 vanishes exactly at 1/2 ± log φ/log 5 + i(2k+1)π/log 5. Each zero is simple, off the line, and at height at least 1.952.
- *The hybrid passes the corpus's pointwise layer.* XiH = riemannXi·XiA is entire, symmetric and real. Exactly as ζ does (`zeta_pointwiseLayer`, `hybrid_pointwiseLayer`), it satisfies Box 1, Box 2 (LowHeightBox), no real zeros, the effective dVP region and the Li disk condition. Hence `pointwise_layer_does_not_imply_rh`. `hybrid_li_rungs` gives Li rungs 0..4 nonnegative; the identification of `hybridLi n` with the Li coefficient of XiH is paper-level.
- *The Euler side.* **Correction:** `Hlit_double_pole`. The proposal's hybrid ζ(s)·Z_{5,−5}(5^{−s}) has a double pole at s = 1, since (s − 1)²·Hlit → 11/(4 log 5); so it is not in the proposal's class. **Repair:** H4 = ζ(s)(1 + 5·5^{−s} + 5·5^{−2s})/(1 − 4·5^{−s}).
  - Its von Mangoldt weights at 5 are positive for every n (`w4_pos`).
  - It has a simple pole at 1 with residue 11 (`H4_simple_pole`), and its completion is XiH (`XiH_eq_completion_H4`).
  - It pays with a pole at log 4/log 5 = 0.861 inside the strip (`H4_pole_in_strip`); the completion factor vanishes there (`gammaH4_zero_in_strip`).
  - Ramanujan fails at 5 (`w4_even_ge`).
- *Limits.*
  - `pole_shadow`, and `local_rh_of_positivity`: positivity plus no local pole in Re s > 1/2 forces local RH.
  - `local_factor_periodic` and `local_zero_low_copy`: every zero of a polynomial local factor at p ≥ 2 has a copy with the same real part at height at most π/log 2 < 4.54.
  - `genus_one_low_offline_zero`.
  - `hybrid_zero_in_certified_box`: the hybrid has an off-line zero in [0.001, 0.999] × [0, 55/16]. That is exactly the box the corpus certifies zero-free for ζ (Arb-conditionally).

**THEOREM-kernel-checked, rvm_bridge (namespace `CruxMetaBarriersRvM`).** `fake_gaussian_nonneg`: the corpus's `gaussTest c λ` summed over all fake zeros has nonnegative real part for every c when 0 < λ ≤ 1/40 (numerically up to λ* = 0.182711). `XiHRZeroSide_eq`: the multiplicity-weighted zero side of ξ·XiA is ζ's `zeroSide` plus the fake side. Hence `XiHR_gaussian_positivity_small` (the E6Bridge30 conclusion, every c, λ ≤ 3/2000) and `XiHR_gaussian_envelope` (the E6Bridge16 sharp envelope for λ ≤ 1/40) hold for ξ·XiA. `fake_gaussian_negative`: at λ = 1/2 and c = π/log 5 the fake sum is negative. So only the proved widths are blind; the full Wall is not. The package is `gaussian_layer_barrier`.

**COMPUTED** (`golden_fake_numerics.py`: 14 checks, 0 failed).

- Admissible sets for q = 2..40. With only Λ ≥ 0 and a positive residue the range is [−(q+1), q]; the extra point m = −(q+1) has zeros on Re s = 1.
- λ* = 0.182711422586.
- The fake and the hybrid Li coefficients both first turn negative at λ_63 (1-based).
- 545,924 RH-violating genus-one data over prime powers q ≤ 2000; the highest "lowest off-line zero" is at height 1.95198.
- D is not multiplicative (b(6) = 1 ≠ b(2)b(3) = −κ²), and Λ_D(3) < 0.

**What it does not establish.** Anything about ζ: this is a relativization, and `BarrierScopeXR.barrier_silent` applies. That the corpus as a whole cannot prove RH: finite certificates, the pole axiom and the exact Γ_ℝ completion each exclude the hybrid. Several paper-level pieces: the Li identification, the Weil-window identity, the hybrid envelope for λ > 1/40, the general-degree pole shadow (direction D1), and integrality of all place counts. The "Theta 1.77" figure for H_{13,−8} was not checked.

**Skeptic.** "Everything I re-ran reproduced, and I found no overclaim that affects the substance of the result." One nit: the centre scan is capped at c ≤ 1500, so the builder's last negative centre at λ = 1, reported as 1388, should read "> 1387".

### 3.4 Build C: the channel no-go, made precise

**THEOREM-kernel-checked, li_positivity (namespace `CruxDynamicsErgodic`; 94 audited declarations).**

- *The channel no-go.* `ChannelAxioms Λ` bundles seven properties: entire; Λ(1 − w) = Λ(w); reality; the edge (no zero on Re w ≥ 1); contractivity ‖Λ(2s − 1)‖ ≤ ‖Λ(2s)‖ on Re s ≥ 1/2; unimodularity on the axis; weak Birman-Krein positivity. `channelAxioms_xi`: ξ satisfies them. `channelAxioms_mul_quadList`: the class is closed under multiplication by the FE quadruple of finitely many points of the open strip. `channel_axioms_do_not_imply_rh`: the fake ξ·Q_{3/4+20i} passes every axiom and vanishes off the line.
- *Contractivity of the real-ξ scattering matrix.* `xi_inner`: ‖ξ(2s − 1)‖ ≤ ‖ξ(2s)‖ for Re s ≥ 1/2, unconditionally. The fact is classical; the kernel proof, via LiCriterion's paired Hadamard factorisation and the gap |ρ + v̄|² − |ρ − v|² = 4 Re ρ Re v, is new. `xi_unitary`: equality on Re s = 1/2. `inner_forces_partner`: contractivity needs only zeros in the closed strip, because edge zeros cancel.
- *Birman-Krein.* `bk_of_inner`: FE, reality and contractivity force Re(conj Λ·Λ')(1 + 2it) ≥ 0. `bk_phase_identity`: logDeriv φ_Λ(1/2 + it) = −4 Re Λ'/Λ(1 + 2it). So Birman-Krein positivity is exactly the σ = 1 slice of the rational face.
- *The normalization correction.* `modScat_eq`: Λ(2s − 1)/Λ(2s)·(s − 1)/s = ξ(2s − 1)/ξ(2s). The true scattering matrix has the residual pole at s = 1 and is not contractive (|φ(3)| = 1.20, COMPUTED).
- *The exchange rate* (RELABELINGS, flagged). `zero_free_strip_iff_shift_contractive`: all zeros lie in |Re ρ − 1/2| ≤ h0 iff every Hermite-Biehler shift h > h0 is contractive. `rh_iff_all_shifts_contractive` and `rh_iff_resonances_on_quarter_line` use Mathlib's `RiemannHypothesis`. `cooked_quadruple_threshold`: ρ0 = 3/4 + 20i is seen by channel h iff h < 1/4.
- *The Hecke-wave scalar core.* `heckeEig_fun_of_laplace`: λ_n(s) = Σ_{ad=n} (a/d)^{s−1/2} is a function of s(1 − s), on unitary and resonant states alike. `finite_euler_blowup_on_axis`: every finite Euler truncation of the scattering matrix blows up on the axis at s = 1/2.
- *The Hecke-orbit correction.* 2i ∈ T_2(i), 3i ∈ T_3(i) and 4i ∈ T_4(i). h(−4f²) = 1 iff f ∈ {1, 2}, checked in exact integers for f ≤ 300. The local corrections at 2i and 3i have all their zeros on the line (`euler2_disc16_zeros_on_line`, `euler3_disc36_zeros_on_line`), so RH at 2i ⟺ RH at i.

**Arb-certified** (segment-enclosure windings, not kernel). Off-line zeros of Epstein zeta functions at points of the Hecke orbit of i: two at 3i (0.86509118… + 20.64734224…i and 0.80901668… + 42.11922059…i) and one at 4i (0.67374145… + 28.11787167…i). Also i√5 (0.93296969… + 15.66824953…i) and D (0.80851718… + 85.69934848…i). Every control box has winding 0. The idea's example 21i/20 (0.77598584… + 21.66552639…i) is COMPUTED only, not certified: Arb's Bessel-K on a ball of complex order blows up.

**Side finding** (confirmed independently by the sibling run's literature lane). `telperion/src/telperion/arb_dh.py:winding_number` samples only nodes, so its docstring claim of "a RIGOROUS zero count" is false as a method claim. The segment-enclosure routine `arb_winding.py` re-certifies the same D zero.

**What it does not establish.** The infinite form for every order-one Λ; only ξ, and ξ times finitely many quadruples, are covered. Lax-Phillips / Sz.-Nagy-Foias realizability. The operator form of the Hecke-wave identity. Sarnak's axis-regularity equivalence. Strict Birman-Krein positivity. Base-point genericity, which is paper only. A certificate for 21i/20. The title "Unitarity = PNT" overstates: contractivity needs only the closed strip, and the PNT content is the edge field.

**Skeptic.** "I found nothing that refutes the build. Everything reproduces, both the Lean and the computations."

### 3.5 This writer's re-verification

Each file was re-elaborated with `leanlock.sh lake env lean Crux/<file>` from its island directory on 2026-09-23:

| File | Exit | Axiom lines | Lines outside the standard three | Other output |
|---|---|---|---|---|
| li_positivity `Crux_spectral_operator.lean` | 0 | 32 | none | none |
| li_positivity `Crux_meta_barriers.lean` | 0 | 161 | none | none |
| li_positivity `Crux_dynamics_ergodic.lean` | 0 | 94 | none | none |
| rvm_bridge `Crux_spectral_operator.lean` | 0 | 22 | none | none |
| rvm_bridge `Crux_meta_barriers.lean` | 0 | 88 | none | none |

A whole-word grep of all five files for `sorry`, `admit`, `native_decide`, `opaque`, `implemented_by`, `extern` and `unsafe`, and for `axiom` declarations, finds only backticked or header prose.

Integer spot checks, recomputed independently:

- Golden fake: Re ρ = 1/2 + log φ/log 5 = 0.7989937, and first height π/log 5 = 1.9519813.
- F(5, 5): N_1..N_4 = 11, 41, 26, 801. a_1..a_7 = 11, 15, 5, 190, 748, 1845, 12320. Every a_d is an integer, at least 5, for d ≤ 40. The Weil-bound failure at the third power is (N_3 − q³ − 1)² = 10000 > 16·125 = 2000, and P(1) = 76.
- Katkova: π/(2 arctan(1/28)) = 44.00099.
- The height-640000 rung exchange: π/(2 arctan(1/1280000)) = 2010619.30.

### 3.6 Refuted builds, and refuted or corrected claims

**Refuted builds: none.** All three skeptics returned `refuted = false`.

Claims refuted, corrected or withdrawn during refereeing and building:

| # | Claim (lens) | Found by | What is actually true |
|---|---|---|---|
| 1 | "H = ζ·Z_{5,−5}(5^{−s}) is a P-datum" (meta) | all three referees; kernel `Hlit_double_pole` | Double pole at s = 1. The repair H4 has a simple pole, but also a pole lattice at Re s = log 4/log 5 inside the strip (kernel). |
| 2 | "H satisfies every hypothesis-free corpus conclusion" (meta) | build (`hybrid_zero_in_certified_box`) | False for finite certificates. True for the pointwise layer, Li rungs 0..4 (modulo the identification), E6Bridge30, and E6Bridge16 at λ ≤ 1/40. |
| 3 | "Every finite certificate is compatible with an off-line zero", read as a statement about Euler-product counter-models (meta, and the dossier's section 4) | build (`local_zero_low_copy`) | False for every lattice model: each has an off-line zero below height π/log 2 < 4.54. |
| 4 | "A NO answer to the Beurling-FE problem would be a proof strategy" (meta) | circularity referee | The NO branch contains RH, since ζ is in the class. |
| 5 | "Li λ_1..λ_61 > 0, first negative at 62" (meta) | referees; build numerics | Correct in 0-based rung indexing. In 1-based Li indexing, λ_1..λ_62 > 0 and λ_63 < 0. |
| 6 | Even-sector Pontryagin-CvS: "at most κ_even pairs of non-real zeros" (spectral) | build | Fails for Galerkin truncations. The corrected counts are first quadrant ≤ κ_even and imaginary axis ≤ κ_even + κ_odd. The untruncated case is open. |
| 7 | "The true ground-state decay is about e^{−10x}" (spectral) | circularity referee | Not uniform in x; the rate is about 6.8 at x = 40. |
| 8 | "D's form is PSD up to x ≈ 31" (spectral) | two referees | Positive Galerkin eigenvalues are only upper bounds. Only the negative side is certified, given accurate entries. |
| 9 | The detection horizon as the operative mechanism (spectral) | negative-control referee; build | It is a valid upper bound, loose by about 3.5 times on D. The counting version has a Gram-control gap. |
| 10 | "Q_λ = H + P is stoquastic", and the nodeless CvS ground state (Lee-Yang) | circularity referee | P is antiferromagnetic on the even sector. Claim (D) stays CONJECTURE. |
| 11 | Perron-Frobenius structure as the Euler product's signal (Lee-Yang) | negative-control referee (numerics) | D's frustrated operator has the same simple, even, nodeless ground state at λ² = 3 to 20. |
| 12 | "A pole-direction analogue of Rodgers-Tao" (Lee-Yang) | all referees | Elementary: Q(F_h) = 0 and P(F_h) = ±2κ_h². |
| 13 | The "decisive experiment", 0 against 186 crossings (probability) | circularity and literature referees | F ≥ 0 is automatic once the zeros are real, and Platt already verified far beyond. The match of the bulk law is expected. |
| 14 | The region split as a THEOREM (probability) | circularity referee | A fixed-κ asymptotic. At fixed λ the cut is heuristic. |
| 15 | The fourth cumulant decays like e^{−c√λ} (probability) | circularity referee | It decays like λ^{−2}. Only the T-exponent is asymptotically exact. |
| 16 | "The bounded-order large-shift corner is blind" as a THEOREM (total positivity) | circularity referee | It needs the unproved localization step, so it is HEURISTIC. |
| 17 | The row criterion needs Fisher-Hartwig / Deift-Its-Krasovsky (total positivity) | all referees | It is Hadamard's 1892 Hankel theorem. The forward direction is trivial; the converse needs a distinct-moduli hypothesis. |
| 18 | The "unitary half-gap law" and the two-channel synthesis (data) | negative-control referee | Refuted as stated by the Selberg zeta of a surface with an exceptional eigenvalue. |
| 19 | "Equality in the half-gap law is attained by E_θ" (data) | circularity referee | Presupposes RH. |
| 20 | `eisShift_violates_RH_analogue'` is "unconditional" (data, scratch Lean) | circularity referee; writer's grep | It carries `hzero : ∃ ρ, riemannXi ρ = 0`. That is dischargeable from the corpus's `exists_nontrivial_zero_above`, but the discharge has not been written. |
| 21 | "The Hecke orbit of i is i plus class-number ≥ 2 points" (dynamics) | two referees; build (exact integers) | It contains 2i, with h(−16) = 1, and RH at 2i ⟺ RH at i. |
| 22 | "−φ'/φ > 0 on the axis (Birman-Krein)" for the true scattering matrix (dynamics) | negative-control referee; build `modScat_eq` | True only for φ_ξ = ξ(2s − 1)/ξ(2s). The true φ has the residual pole at 1, and −φ'/φ(1/2 + ir) ≈ −3.908 at r ≈ 0. |
| 23 | "Poles from different primes are distinct" (dynamics) | referees | Every local factor has a pole at s = 1/2. The conclusion survives (kernel `finite_euler_blowup_on_axis`). |
| 24 | "The polarization is the unique missing ingredient" (arithmetic geometry) | referees | For formal curves this restates RH (Weil's two-line equivalence). |
| 25 | "Barrier III spares exactly Γ(s/2) or ℕ" (arithmetic geometry) | circularity referee | It spares every non-periodic feature. |
| 26 | The dossier's note "li_positivity = v4.32" | writer | The island's `lean-toolchain` is `v4.34.0-rc1`. |
| 27 | `arb_dh.py:winding_number` returns "a RIGOROUS zero count" (program tool) | Build C; sibling axiso-literature build | Node sampling cannot exclude an extra turn. The certified conclusion was re-established with segment enclosures. |

### 3.7 Outside the skeptic filter (not counted as verified)

- `/private/tmp/claude-0/crux-probabilistic-rigidity/RandomEulerLogability.lean`: three one-prime Jensen lemmas. The author compiled it on rvm_bridge. No skeptic saw it, and it is ephemeral.
- `/private/tmp/claude-0/crux-data-discovery/lean/EisensteinShiftControl.lean`: the E_θ control. The author compiled it on li_positivity. The literature referee could not find it under `/Users`. No skeptic saw it, and it has the defects listed in row 20 above.
- `/private/tmp/claude-0/crux-meta-barriers/lean/GoldenFake.lean` and `/private/tmp/claude-0/crux-dynamics-ergodic/lean/ResonanceEdge*.lean`: superseded by Builds B and C.
- Generator-phase numerics of every lens: computed, and in part reproduced by referees, but not skeptic-checked. This includes the total-positivity row-44 flip, the Lee-Yang frequency scans, the probability zero windows and the data-discovery CUE comparison.

---

## 4. The most promising directions, ranked

None of these is a route to RH. They are ranked by expected mathematical value near the crux times tractability. Following the ethos, directions that consume arithmetic D lacks rank first.

### D1. The pole shadow in every degree (uses arithmetic; reachable in the kernel)

**Where it comes from.** Build B proves in the kernel, for genus one, that positivity of the local weights forces every off-line local zero to be shadowed by a local pole at least as far right (`pole_shadow`). It also forces local RH when the local factor has no pole in Re s > 1/2 (`local_rh_of_positivity`). The build states the general case at paper level. Section 0.3 explains why this is the right shape.

**Next theorem.**

*D1a, the local Pringsheim lemma (kernel target).* Let L ∈ ℝ(T) be rational and not constant, in lowest terms, with L(0) = 1, and suppose every Taylor coefficient of log L at 0 is nonnegative. Then L has a pole at a positive real point r, r is the radius of convergence of log L, and every zero and every pole of L satisfies |T| ≥ r.

*D1b, finitely modified Euler products (writer's sketch, unrefereed).* Let S be a finite set of primes, let R_p ∈ ℝ(T) with R_p(0) = 1 for each p ∈ S, and put F(s) = ζ(s) ∏_{p∈S} R_p(p^{−s}). Suppose Λ_F(n) ≥ 0 for all n, and that F has a simple pole at s = 1 and no other pole on the real half-line (1/2, ∞). Then every zero of every R_p(p^{−s}) has Re s ≤ 1/2. Suppose further that γF is entire and γF(1 − s) = γF(s) for some γ holomorphic and zero-free on 0 < Re s < 1. Then every such zero with 0 < Re s < 1 lies on Re s = 1/2.

**Proof sketch.**

- (a) On [0, r), L(T) = exp(Σ c_k T^k) is at least 1 and increasing. Pringsheim's theorem makes T = r a singularity of log L, so r is a zero or a pole of L. It cannot be a zero, so it is a pole, and no zero or pole lies inside the disk of convergence. The genus-one kernel proof avoids Pringsheim with a power-sum argument. In general degree, the same route needs a Turán-type lemma on Cesàro means of unimodular power sums.
- (b) Λ_F ≥ 0 says exactly that log(R_p(T)/(1 − T)) has nonnegative coefficients for each p ∈ S. Define σ_p by p^{−σ_p} = r_p, and let σ* be the largest σ_p. At s = σ*, the factor with σ_p = σ* has a pole. ζ(σ*) is finite and nonzero, because ζ has no real zeros in (0, 1) or in (1, ∞). Every factor with σ_q < σ* is finite and nonzero there. So F has a pole at σ*. That contradicts the hypothesis unless σ* ≤ 1/2, or σ* = 1, which would make the pole at 1 at least double. So local zeros satisfy Re s ≤ σ_p ≤ 1/2.
- (b, completion clause) A local zero with Re s = σ ∈ (0, 1/2) comes with its whole lattice σ + i(t0 + 2πk/log p). All but finitely many of these are zeros of γF, since a pole of another local factor can cancel at most one point of the lattice. The functional equation reflects them to a lattice on Re s = 1 − σ > 1/2, where only ζ can vanish. Then ζ would have at least cT zeros with real part 1 − σ up to height T, contradicting Bohr-Landau: N(σ', T) = o(T) for σ' > 1/2.

**Status.** D1a is THEOREM-paper-proof (classical Pringsheim; genus one is kernel-checked). D1b is a writer's sketch, unrefereed; its novelty is unverified, and the Selberg-class literature on local factors should be checked first.

**Why it is not a relabeling.** It constrains finitely many local factors and says nothing about the zeros of ζ. It holds whether or not RH does.

**Arithmetic D lacks.** An Euler product over the rational primes (D has none: b(6) ≠ b(2)b(3)); Λ ≥ 0 (Λ_D(3) < 0); a pole at s = 1 (D is entire); and the density theorem N(σ, T) = o(T). D violates the last: its off-line zeros have positive density in suitable strips inside 1/2 < Re s < 1 (Voronin; equivalently φ_D > 0 in the Borchsenius-Jessen theory used by the probability lens).

**What it buys.** It closes the lattice front of the barrier ledger with a theorem: no finitely modified Euler product that satisfies positivity, the pole axiom and a strip-regular completion can serve as a counter-model. Lattice constructions are then excluded in three independent ways:

1. by D1;
2. by `local_zero_low_copy`, since certification to height 4.54 already rules them out;
3. by the periodicity obstruction, since they cannot carry Γ(s/2).

A barrier against arguments that use positivity together with the pole axiom would need a global, non-lattice Euler product with an off-line zero. None is known, and a proof that none exists would contain RH. Expected value: modest. The Lean work is modest too, since the genus-one proof is the template, and it turns a paper claim of the build into a theorem and gives the ledger a clean rule.

### D2. The near-radical lemma: the functional-equation half of CCM/CvS, as a theorem

**Where it comes from.** Build A's calibration on D: the CCM/CvS pipeline reproduces D's own zeros with CCM-grade accuracy until the form turns indefinite, and after that the near-null eigenvectors carry D's off-line zeros. The spectral lens's annihilator lemma bounds only the Rayleigh quotient of the truncated Polya kernel. As its negative-control referee noted, that does not control eigenvectors once κ > 0. The fix is to bound the operator, not the form.

**Next theorem (writer's sketch, unrefereed).** Let F be a self-dual FE datum with Polya kernel Φ_F, so that Φ̂_F = Ξ_F. Put L = log x and Φ_x = Φ_F·1_{[−L/2, L/2]}, and let A_x be the self-adjoint operator of the closed semibounded window form QW_x^F on L²[−L/2, L/2]. Then Φ_x ∈ D(A_x) and

    ‖A_x Φ_x‖ ≤ C_F x^c e^{−πx/q_F},   with q_ζ = 1 and q_D = 5,

so ‖Φ_x − E_{[−τ,τ]}(A_x)Φ_x‖ ≤ C_F x^c e^{−πx/q_F}/τ for every τ > 0. With τ = e^{−πx/(2q_F)}, the spectral subspace for eigenvalues in [−τ, τ] contains a vector whose Fourier transform converges to Ξ_F locally uniformly on ℂ.

**Proof route.**

1. Extend the window explicit formula QW_x(f, g) = Σ_ρ m(ρ) conj(f̂(conj γ_ρ)) ĝ(γ_ρ) from smooth compactly supported tests (`weilSesq_hasSum`) to L² window tests, by mollification.
2. Φ̂_x = Ξ_F − τ̂, where τ is the tail on |u| > L/2. Ξ_F vanishes at every γ_ρ and at every conj γ_ρ (the partner ordinate), so only τ̂ enters. On |Im z| ≤ 1/2, |τ̂(z)| ≤ C x^{11/4} e^{−πx}/(1 + |z|) (the lens's annihilator estimate; for D the exponent is −πx/5).
3. Apply Cauchy-Schwarz against a weighted sampling bound, Σ_ρ |ĝ(γ_ρ)|²/log(2 + |γ_ρ|) ≤ C(x)‖g‖² with C(x) polynomial in x. That bound follows from Plancherel-Polya and the local count N(t + 1) − N(t) = O(log t), which is kernel-proved (RvM). The result is an L² bound on the functional g ↦ QW_x(Φ_x, g), and the representation theorem for closed forms then puts Φ_x in D(A_x).
4. The spectral theorem.

**Why it is not a relabeling.** It holds for D, which violates RH. It says where the approximant of Ξ_F sits in the spectrum, not where any zero lies.

**Arithmetic D lacks.** None, and that is the point. The theorem would show that the approximation property behind CCM/CvS "super-accuracy" follows from the functional equation alone. The Euler product could then enter the Hilbert-Polya-by-truncation program only in two ways: through κ_ζ(x), and through the choice of one eigenvector inside the near-null subspace (for ζ, the ground state). As a design rule this is already the dossier's "an FE-uniform lemma cannot be the last step". As a theorem it would settle the question for this program, and it would rebut the reading that 10^{−55} accuracy "cannot be coincidence".

**Status and caution.** A writer's sketch, unrefereed. Qualitatively it is close to Connes, arXiv:2602.04022 §6.4 (the near-radical vector E(h) and its convergence to Ξ, according to the spectral lens's literature referee). The quantitative operator-norm form and the spectral-projection consequence must be checked against CCM and CvS before anything is claimed.

### D3. Detection without masking: the analytic half, in the kernel

**Next theorem** (THEOREM-paper-proof in the idea; constants not optimized; the referees' fixes are required). Let ρ0 = 1/2 + δ0 + iγ0 be a simple zero of ξ with 0 < δ0 < 1/2, and let d0 be the distance from γ_{ρ0} to the other ordinates. There is an absolute C such that the even-sector window form QW_x is indefinite for all

    x ≥ X(ρ0) := γ0/4 + (1/π) log(1/|ζ'(ρ0)|) + C·(log(1/δ0) + log(1/min(1, d0)) + log(2 + γ0)).

The required fixes: symmetrize the detector over the quadruple ±γ0 ± iδ0, keep the zero simple, and write out the constants. The algebraic half is already kernel-checked (`detector_pair_term_le`, `isNegFamily_of_diag_dominant`). The analytic half needs the tail estimate for the truncated Polya kernel, a Paley-Wiener interpolant, and the window explicit formula from D2, step 1. The counting version, κ(x) ≥ #{off-line pairs with X(ρ) ≤ x}, also needs Gram-matrix control, which has not been written.

**Why it is not a relabeling.** It is one-directional and quantitative, and it holds for D. D's horizon is about 5γ/4, which is loose by about 3.5 times against the observed onset near x = 31.

**Arithmetic.** None; it is an instrument. It ranks here because it is the only output of this team that bears directly on a named open lemma in the dossier. Effective O2 (E6Bridge14) needs a maximal-zero hypothesis and an on-line spacing floor. Window detection needs neither, and pays only logarithmically in δ0, d0 and |ζ'(ρ0)|, at the price of a horizon linear in the height. Together with `weil_negIndex_le_offline`, it sandwiches κ(x) between the number of resolved off-line pairs and the number of existing ones. It also gives Telperion a pipeline for Weil-side falsification, from Arb-certified negative Rayleigh quotients to a kernel refutation atom, which the harness can exercise on D today (section 6.3). It cannot certify RH: certifying κ_ζ(x) = 0 at useful x is beyond envelope methods, since ground-state eigenvalues at x = 40 are of order 1e−109 or smaller.

### D4. Close the last cell of the degree-one axiom lattice (cross-reference)

**Context.** The sibling class-P run showed two things for degree one. First, integer frequencies plus the ζ-shape FE (any conductor, Selberg normalization) plus Λ ≥ 0 force F = ζ. Second, positive Beurling systems with ζ's exact conductor-1 FE are the integers. Both are THEOREM-paper-proof, with the coefficient core kernel-checked and novelty unverified. This team's builds supply the other side. With the completion left arbitrary, Euler-product fakes with Λ ≥ 0 exist (the golden hybrid, the formal curves). And every lattice system is excluded both by the pole axiom (D1) and by the Γ(s/2) completion, through the arithmetic-geometry lens's periodicity obstruction. That argument extends, by this writer's check, to any conductor Q^s and any shift Γ(s/2 + μ) with Re μ ≥ 0, because the poles of the gamma ratio lie on a single horizontal line and so cannot be invariant under a vertical period.

**Next theorem.** The one open cell is the twisted Beurling cell (conductor q > 1), conjectured empty. Its natural first case is the sibling's NT5, "Beurling Lemma C": if ζ·G is a log-positive Beurling system with the twisted ζ-shape FE, and G is a finite generalized Dirichlet polynomial with real frequencies ≥ 1, then G = 1 and q = 1. The periodicity obstruction settles the sub-case where all norms lie in a single ray q^ℤ.

**Why it is not a relabeling.** It classifies a class that contains ζ, and the classification is independent of RH. The payoff is ledger closure. Once the class is {ζ}, "RH for the class" is RH verbatim, so no class-level (relativization) argument in degree one can help, and every remaining argument must be about ζ itself.

**Arithmetic D lacks.** Λ ≥ 0 together with multiplicativity (the sibling run's P2).

### Further questions (unranked)

- **The Locator itself.** Does the (κ+1)-th eigenvector's transform converge to Ξ_F? D2 is the cluster-level first step. The single-eigenvector statement is CONJECTURE-with-evidence (D at x = 60 and 80).
- **The channel no-go, extended to the trace formula.** The dynamics lens sketched, without proof, that sign-constrained Selberg trace-formula tests see only |γ| < 2r_1 ≈ 19.07, where r_1 is the spectral parameter of the first Maass cusp form of PSL(2, ℤ). It needs a precise statement before it can be a target.
- **Positivity after the pole direction is removed.** Does Λ ≥ 0 imply any inequality on the second level of the pole-free Weil operator that fails for a frustrated FE datum? The evidence so far says no. D's ground state is nodeless. E_θ has Λ ≥ 0, and since all its zeros are off the line its Weil form should be indefinite at large windows (Weil's criterion for this degree-2 function; paper-level, not checked here); its extra poles at 1 ± θ carry the positivity.
- **Off the crux:** V_b deficit universality, and localization of total-positivity minors, which is an arithmetic-free problem.

---

## 5. New barriers and no-go results

### 5.1 The positivity principle, as a list of theorems

The heuristic of section 0.3 rests on these statements:

- Landau (classical): if Λ_F ≥ 0, F ≠ 0 to the right of the abscissa of convergence of log F, which is a real singularity.
- Pringsheim for local factors (classical; D1a).
- The pole shadow and local RH under positivity (THEOREM-kernel-checked in genus one: `pole_shadow`, `local_rh_of_positivity`; general degree is D1).
- The stoquastic structure of the pole-free Weil operator and its Perron-Frobenius condensate (THEOREM-paper-proof; alignment with the pole vector COMPUTED).
- The negative-control lesson that Perron-Frobenius structure also appears for D (COMPUTED).

### 5.2 Kernel-checked no-go results

1. **Pointwise-layer barrier** (`pointwise_layer_does_not_imply_rh`). The layer's clauses are strip, symmetries, Box 1 and Box 2, no real zeros, effective dVP and the Li disk. They are satisfied both by ζ's zeros and by the zeros of an entire, symmetric, real function with an off-line zero at 0.799 + 1.952i. No argument that uses only these properties of a zero set can prove RH.
2. **Gaussian-layer barrier** (`gaussian_layer_barrier`). The conclusions of E6Bridge30 (every c, λ ≤ 3/2000) and E6Bridge16 (λ ≤ 1/40) hold verbatim for ξ·XiA. The full Wall detects the fake at λ = 1/2. So the program's two proved Gaussian instruments are blind to it, and the Wall itself is not.
3. **Channel no-go** (`channel_axioms_do_not_imply_rh`). Unitary scattering data on PSL(2, ℤ)\H cannot prove RH. Birman-Krein positivity adds nothing beyond contractivity, and it is exactly the σ = 1 slice of the rational face.
4. **The CvS real-zeros step is structure-generic** (`pontryagin_cvs_line`, `no_upper_zeros_of_psd`). It holds for any Hermitian form under which multiplication by z is symmetric. So it cannot carry arithmetic, and on D it bounds the non-real eigenvector zeros by D's positive index.
5. **Genus one: positivity gives exactly the trivial bound** (`admissible_iff`, `exists_admissible_not_rh_iff`). The formal Euler axioms give |m| ≤ q, RH is m² ≤ 4q, and the first gap is at q = 5.
6. **Lattice fakes cannot beat finite certification** (`local_zero_low_copy`, `hybrid_zero_in_certified_box`). This limits barriers, not proofs: a barrier witness against certificate-using arguments must be non-lattice.
7. **Finite Euler truncations of the scattering matrix are never unimodular** (`finite_euler_blowup_on_axis`). This is the scattering analogue of `EulerFactorSectionOffline`.

### 5.3 Paper-level no-go results

- **Total-positivity blindness** (THEOREM-paper-proof). Consider a product-closed total-positivity class containing a nonzero sector: PF_m, bounded-order Toeplitz minors, or certificates of the Katkova / Griffin-Ono-Rolen-Zagier bounded-order kind. No such class can exclude an off-line zero at angle ≤ π/(m+1). Membership already follows from finite verification plus the strip. D is the witness.
- **Moment and random-model certificates for clause (III)** (HEURISTIC to paper sketch). In Region II (T_cert < c < 2π e^{8λ}), the Bohr-Jessen model predicts T^{1−1/(8κ)} barrier crossings while matching every moment of order below 2/κ. In Region I, moment certificates are dominated by the envelope (constants not pinned).
- **Barrier III** (THEOREM-paper-proof, with integers reproduced by the referees and by this writer). Nothing uniform over (effective Euler product + exact FE with an arbitrary, q-periodic completion + entire order-1 completion) proves RH or any zero-free strip. Genus one with a = q already gives Re ρ ≈ 1 − 1/(q log q).
- **The periodicity obstruction** (THEOREM-paper-proof). A Beurling system with all norms in q^ℤ cannot carry Γ(s/2 + μ) with Re μ ≥ 0; the extension to general conductor and shift is this writer's check.
- **Temperedness** (folklore; Lean scratch). E_θ satisfies FE, Euler product, Λ ≥ 0 and prime-power support, and has off-line zeros. So those inputs cannot give a zero-free strip narrower than θ. An argument that genuinely uses degree one escapes this.
- **Base-point genericity** (THEOREM-paper-proof; Proposition 1 of Strömbergsson-Södergren covers almost every lattice). No open or almost-everywhere property of the base point implies RH at z = i. Arb-certified witnesses exist inside the Hecke orbit of i (3i and 4i).
- **The non-self-dual lane** (standard). Zero sets stay invariant under ρ ↦ 1 − ρ̄, so this lane supplies no reflection-breaking.
- **"CCM step 2 = Locator and κ ≡ 0"** (a remark, near-tautological by the referees' judgment). Together with the D calibration, it places the Euler product's burden in the CCM program exactly: on κ, and on the selection of one eigenvector.

### 5.4 The fake zoo

Each row is a function with the functional-equation shape and off-line zeros. The column "real singularity" is the pole-shadow check from section 0.3.

| Object | Completion | Euler product | Λ ≥ 0 | Real singularity at or right of the off-line zeros | Off-line zeros | Trust | Source |
|---|---|---|---|---|---|---|---|
| D (Davenport-Heilbronn) | conductor 5, Γ_ℝ(s+1) | no (b(6) ≠ b(2)b(3)) | no (Λ_D(3) < 0) | none; D is entire | yes, including Re s > 1 | Arb (segment windings) | dossier; Build C; sibling run |
| Epstein at i√5, 3i, 4i | E*(z, s) | no (a genus sum of two products) | no (by Landau: class number 2 gives zeros in Re s > 1) | pole at 1 only | from heights 15.67, 20.65, 28.12 | Arb | Build C |
| V_b = ξ(s+ib) + ξ(s−ib) | exact self-dual FE | no | n/a (not a Dirichlet series) | none; entire | positive density (up to 61% at u = 1) | COMPUTED | data discovery |
| Channel fake ξ·Q_{3/4+20i} | FE, real, entire | none claimed | none claimed | none claimed | 3/4 + 20i | kernel | Build C |
| H4 (golden hybrid), completion XiH = ξ·XiA | non-Γ_ℝ factor, vanishing in the strip | yes | yes (weights ≥ 1) | pole lattice at Re s = 0.861 | 1/2 ± 0.299 + i(2k+1)·1.952 | kernel | Build B |
| Hlit = ζ·Z_{5,−5}(5^{−s}) | same | yes | yes | double pole at s = 1, plus a pole lattice on Re s = 1 | same | kernel | Build B |
| Formal curve F(5, 5), and the family F(q, m) | exact FE, q-periodic completion | yes (integer exponents ≥ 0) | yes | pole lattice on Re s = 1 | Re ρ = 0.79899; tends to 1 in the family | exact integers | arithmetic geometry |
| E_θ = ξ(s+θ)ξ(s−θ) | self-dual, degree 2 | yes (Re s > 1 + θ) | yes | poles at 1 ± θ | every zero, at Re 1/2 ± θ | scratch Lean (with `hzero`) | data discovery |
| Ruelle zeta R = Z(s+1)/Z(s) of a surface with an exceptional eigenvalue | FE | yes (geodesic norms) | yes | real pole at s_1 ∈ (1/2, 1) (writer's normalization remark) | the exceptional datum is a pole, not a zero | classical | data-discovery referee; writer |
| Sibling controls: ζ(1 + 4·2^{−s} + 2·4^{−s}), F0, W1(29, 11) | Γ_ℝ with conductor | yes | **no** (Λ(4) < 0, or negative at even powers of 29) | none | Re s = 1.7716, Re s = 1, Re s = 0.5612 | kernel | `RH_AXIOM_ISOLATION_2026-09-22.md` |
| Sibling F1 = ζ(s/2 + 3/4)ζ(s/2 − 1/4) | one gamma factor, entire and symmetric | weighted | yes (Beurling form) | poles at 1/2 and 5/2 | all zeros off the line | kernel | sibling |

Every control with Λ ≥ 0 has a real singularity at or to the right of its off-line zeros. Every Dirichlet-series control without one violates Λ ≥ 0. Landau and Pringsheim guarantee this. The value of the table is that it shows the constraint binding in every construction the two runs found.

### 5.5 Corrections to the dossier's ledger

1. "Every finite certificate is compatible with an off-line zero beyond its horizon" remains true of zero configurations. It is false as a statement about Euler-product counter-models of lattice type, since every such model has an off-line zero below height 4.54. Barrier witnesses must be non-lattice.
2. "Any proof must use the FE and the Euler product jointly" is necessary but not sufficient in the forms the program uses. The golden hybrid and the formal curves satisfy the FE (with an arbitrary completion), an Euler product and Λ ≥ 0, and they violate RH. The separating inputs are the pole axiom, the exact Γ_ℝ completion, Ramanujan at every prime, and finite certification. In degree one, the exact Γ_ℝ-shape completion with its pole normalization, together with Λ ≥ 0, already pins the class to {ζ} (sibling run).
3. The dossier's untested non-self-dual lane is closed: it offers no new reflection-breaking.
4. CCM/CvS super-accuracy is generic to the functional equation (the D calibration). It is not evidence for RH.
5. The li_positivity island runs Lean v4.34.0-rc1, not v4.32.
6. `arb_dh.py:winding_number` is not a rigorous count as a method. Its certified conclusion has been re-established by segment enclosure.

---

## 6. Proposed registry nodes (drafts; the lead authors them)

### 6.0 Preconditions

These are the same preconditions as in the sibling report.

1. Commit the five Lean files and the three research directories. All are untracked on `cl/crux`.
2. Wire the files into their islands' lakefiles and AxiomGuard targets.
3. Run a blind read-back audit.
4. Statement modules must either carry the local definitions or import the Crux modules. The definitions involved are `IsWeilNegFamily`, `NegIndexLE`, `IsNegFamily`, `IsHermitian`, `ChannelAxioms`, `PointwiseLayer`, `XiA`, `XiH`, `XiHR`, `XiHRZeroSide`, `fakeSide`, `fakeZero`, `Admissible`, `N`, `tr`, `twoA2`, `Xi` and `bigRoot`.
5. li_positivity (v4.34.0-rc1) and rvm_bridge (v4.33.0-rc2) compose only at registry level. `closure_clean` stays false wherever Zeta23 cross-island dependencies exist.

The proved-node statement texts below are copied verbatim from the artifacts. None has been re-elaborated as a standalone statement module.

### 6.1 Mirrormere (clause I in Weil and operator coordinates)

**`MM_weil_negindex_le_offline`** (kind `lemma`; rvm_bridge). Title: *"Unconditional inertia bound for the zeta Weil form: a family of Weil tests spanning a negative-definite subspace has at most |S| members, where S holds one zero from each off-line pair {ρ, 1 − conj ρ}. The unconditional companion of MM_offline_pairs_le_defect. Says nothing if there are infinitely many off-line zeros; under RH it says κ = 0. NOT RH."* Artifact: `examples/rvm_bridge/lean/Crux/Crux_spectral_operator.lean` (`CruxSpectralOperator.weil_negIndex_le_offline`; also `kappaWindow_le_offline` and `kappaWindow_mono`).

```lean
-- namespace CruxSpectralOperator; open Zeta23 Complex MeasureTheory WeilExplicit; open scoped ComplexConjugate
def IsWeilNegFamily {n : ℕ} (g : Fin n → ℝ → ℂ) : Prop :=
  (∀ i, IsWeilTest (g i)) ∧
    ∀ c : Fin n → ℂ, c ≠ 0 → (weilForm (autocorr (∑ i, c i • g i))).re < 0

theorem weil_negIndex_le_offline (S : Finset ℂ)
    (hS : ∀ ρ, WeilExplicit.zeroMult ρ ≠ 0 → ρ.re ≠ 1 / 2 → ρ ∈ S ∨ 1 - conj ρ ∈ S)
    {n : ℕ} (g : Fin n → ℝ → ℂ) (hg : IsWeilNegFamily g) : n ≤ S.card
```

**`MM_weil_sesq_z_symmetric`** (`lemma`; rvm_bridge). Title: *"Zero-side representation of the sesquilinear zeta Weil form, and its z-symmetry B(f', g) + B(f, g') = 0 (unconditional)."* Artifact: the same file (`weilSesq_hasSum`, `weilSesq_deriv_symm`).

```lean
theorem weilSesq_deriv_symm {f g : ℝ → ℂ} (hf : IsWeilTest f) (hg : IsWeilTest g) :
    weilSesq (deriv f) g + weilSesq f (deriv g) = 0
```

**`MM_pontryagin_cvs`** (`lemma`; li_positivity). Title: *"Pontryagin form of the Connes-van Suijlekom real-zeros step, abstract: for a Hermitian form B with E in its radical and multiplication by z symmetric on the Jordan chains of E's zeros, the zeros in the open upper half-plane (with multiplicity) number at most the negative index of B; K = 0 is the CvS theorem without discretisation. Abstract linear algebra; the continuous-window glue is paper and enters as hypotheses. Holds verbatim for Davenport-Heilbronn."* Artifact: `examples/li_positivity/lean/Crux/Crux_spectral_operator.lean` (`Crux.SpectralOperator.pontryagin_cvs_line`, `no_upper_zeros_of_psd`, `card_le_of_isotropic`).

```lean
-- namespace Crux.SpectralOperator; variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def IsHermitian (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop := ∀ u v, conj (B u v) = B v u
def IsNegFamily (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {ι : Type*} [Fintype ι] (w : ι → V) : Prop :=
  ∀ c : ι → ℂ, c ≠ 0 → (B (∑ i, c i • w i) (∑ i, c i • w i)).re < 0
def NegIndexLE (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (K : ℕ) : Prop :=
  ∀ (n : ℕ) (w : Fin n → V), IsNegFamily B w → n ≤ K

theorem pontryagin_cvs_line (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : IsHermitian B) (E : V)
    (hE : ∀ v, B E v = 0) {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℂ) (R P : ι → V)
    (rk : ι → ℕ) (hP : ∀ i, P i = E ∨ ∃ k, P i = R k ∧ rk k < rk i)
    (hα : ∀ i, 0 < (α i).im)
    (hZ : ∀ i j, B (P i + α i • R i) (R j) = B (R i) (P j + α j • R j))
    (hind : LinearIndependent ℂ R)
    (hrad : ∀ c : ι → ℂ, (∀ v, B (∑ i, c i • R i) v = 0) → ∑ i, c i • R i = 0)
    {K : ℕ} (hK : NegIndexLE B K) : Fintype.card ι ≤ K
```

**`MM_galerkin_pontryagin_cvs`** (`lemma`; li_positivity). Title: *"The same count for Hermitian matrices with displacement structure (Ω_i − Ω_j)Q_ij = ℓ_i conj g_j − g_i ℓ_j; the Galerkin matrices of the window Weil form satisfy this identity to 1e-40 (COMPUTED, not kernel)."* Artifact: the same file (`galerkin_pontryagin_cvs`).

**`MM_rh_iff_weil_negindex_zero`** (`lemma`; rvm_bridge). The title must carry *"RELABELING of Weil's criterion"*.

```lean
theorem rh_iff_weil_negIndex_zero :
    RiemannHypothesis ↔ ∀ (n : ℕ) (g : Fin n → ℝ → ℂ), IsWeilNegFamily g → n = 0
```

**`MM_negctl_channel_axioms`** (`lemma`; li_positivity). Title: *"NEGATIVE CONTROL (dynamical lens): the channel axioms of unitary scattering on PSL(2,Z)\H hold for xi and for xi * Q_{3/4+20i}, which vanishes off the line; no argument using only these properties proves RH."* Artifact: `examples/li_positivity/lean/Crux/Crux_dynamics_ergodic.lean`.

```lean
-- namespace CruxDynamicsErgodic; open Complex ComplexConjugate LiCriterion
structure ChannelAxioms (Λ : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ Λ
  fe : ∀ w, Λ (1 - w) = Λ w
  real : ∀ w, Λ (conj w) = conj (Λ w)
  edge : ∀ w : ℂ, 1 ≤ w.re → Λ w ≠ 0
  inner : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖Λ (2 * s - 1)‖ ≤ ‖Λ (2 * s)‖
  unitary : ∀ s : ℂ, s.re = 1 / 2 → ‖Λ (2 * s - 1)‖ = ‖Λ (2 * s)‖
  bk : ∀ t : ℝ, 0 ≤ (conj (Λ (1 + 2 * t * I)) * deriv Λ (1 + 2 * t * I)).re

theorem channelAxioms_xi : ChannelAxioms riemannXi
theorem channel_axioms_do_not_imply_rh :
    ¬ ∀ Λ : ℂ → ℂ, ChannelAxioms Λ → ∀ w : ℂ, Λ w = 0 → 0 < w.re → w.re < 1 → w.re = 1 / 2
```

**`MM_xi_scattering_contractive`** (`lemma`; li_positivity). Title: *"The real-xi scattering matrix xi(2s-1)/xi(2s) is contractive on Re s >= 1/2 and unimodular on the axis (unconditional; mathematically it needs only zeros in the closed strip)."*

```lean
theorem xi_inner {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖riemannXi (2 * s - 1)‖ ≤ ‖riemannXi (2 * s)‖
theorem xi_unitary {s : ℂ} (hs : s.re = 1 / 2) : ‖riemannXi (2 * s - 1)‖ = ‖riemannXi (2 * s)‖
```

**`MM_bk_is_sigma_one_slice`** (`lemma`; li_positivity). Title: *"Birman-Krein positivity equals the sigma = 1 slice of the rational face: logDeriv phi_Lambda(1/2+it) = -4 Re Lambda'/Lambda(1+2it), and contractivity implies the weak form."* Artifact: `bk_phase_identity`, `bk_of_inner`.

**`MM_rh_iff_shift_contractive`** (`lemma`; li_positivity). The title must carry *"RELABELING (exchange rate)"*. Artifact: `zero_free_strip_iff_shift_contractive`, `rh_iff_all_shifts_contractive`.

```lean
theorem zero_free_strip_iff_shift_contractive (h₀ : ℝ) :
    (∀ ρ : NontrivialZero, |ρ.val.re - 1 / 2| ≤ h₀) ↔
      ∀ h : ℝ, h₀ < h → ∀ u : ℂ, 1 / 2 ≤ u.re → ‖riemannXi (u - h)‖ ≤ ‖riemannXi (u + h)‖
```

**`MM_negctl_golden_gaussian_layer`** (`lemma`; rvm_bridge). Title: *"NEGATIVE CONTROL (golden fake): the E6Bridge30 conclusion (every c, lam <= 3/2000) and the E6Bridge16 envelope (lam <= 1/40) hold verbatim for the multiplicity-weighted zero side of the entire symmetric function xi * XiA, which has an off-line zero; at lam = 1/2 the fake part is negative, so the full Wall detects it."* Artifact: `examples/rvm_bridge/lean/Crux/Crux_meta_barriers.lean` (`CruxMetaBarriersRvM.gaussian_layer_barrier`).

```lean
theorem gaussian_layer_barrier :
    Differentiable ℂ XiHR ∧ (∀ s, XiHR (1 - s) = XiHR s) ∧
    (∀ c lam : ℝ, 0 < lam → lam ≤ 3 / 2000 →
      0 ≤ (XiHRZeroSide (RvMBridge6.gaussTest c lam)).re) ∧
    (∀ c lam : ℝ, 0 < lam → lam ≤ 1 / 40 → RvMBridge16.envelopeCsharp lam ≤ |c| →
      0 ≤ (XiHRZeroSide (RvMBridge6.gaussTest c lam)).re) ∧
    (∃ ρ : ℂ, XiHR ρ = 0 ∧ ρ.re ≠ 1 / 2) ∧
    (fakeSide (RvMBridge6.gaussTest (Real.pi / Real.log 5) (1 / 2))).re < 0
```

Note for the lead: `XiHRZeroSide` is a `tsum`, and Mathlib's `tsum` of a non-summable family is 0. The proof establishes summability inside `XiHRZeroSide_eq`, but the statement does not display it. This writer recommends adding the summability conjunct to the registry statement, so that the positivity is visibly non-vacuous. That amended text has not been typechecked.

### 6.2 RH campaign (the barrier ledger)

**`RH_barrier_pointwise_layer`** (`lemma`; li_positivity). Title: *"Pointwise-layer barrier: strip, symmetry, Box 1, Box 2, no real zeros, effective dVP and the Li disk are satisfied by zeta's zeros and by those of an entire symmetric function with an off-line zero at 0.799 + 1.952i; they do not imply RH. A relativization: silent about zeta."* Artifact: `examples/li_positivity/lean/Crux/Crux_meta_barriers.lean` (`pointwise_layer_does_not_imply_rh`, `zeta_pointwiseLayer`, `hybrid_pointwiseLayer`).

```lean
-- namespace CruxMetaBarriers; open Complex
structure PointwiseLayer (Z : ℂ → Prop) : Prop where
  strip : ∀ ρ, Z ρ → 0 < ρ.re ∧ ρ.re < 1
  reflect : ∀ ρ, Z ρ → Z (1 - ρ)
  conj : ∀ ρ, Z ρ → Z (starRingEnd ℂ ρ)
  box1 : ∀ ρ, Z ρ → Real.sqrt 3 / 2 ≤ |ρ.im|
  box2 : ∀ ρ, Z ρ → (ρ.re - 1 / 2) ^ 2 ≤ ρ.im ^ 2 / 3 - 1 / 4
  noReal : ∀ ρ, Z ρ → ρ.im ≠ 0
  dvp : ∀ ρ, Z ρ → 55 / 16 ≤ |ρ.im| → ρ.re ≤ 1 - ZeroFreeBridge.dlvpRateC / Real.log |ρ.im|
  liDisk : ∀ ρ, Z ρ → 1 ≤ (ρ * (1 - ρ)).re

theorem zeta_pointwiseLayer : PointwiseLayer ZetaStripZero
theorem hybrid_pointwiseLayer : PointwiseLayer (fun ρ => XiH ρ = 0)
theorem pointwise_layer_does_not_imply_rh :
    ¬ ∀ Z : ℂ → Prop, PointwiseLayer Z → ∀ ρ, Z ρ → ρ.re = 1 / 2
```

**`RH_genus_one_square_root_gap`** (`lemma`; li_positivity). Title: *"Genus one: the formal Euler clauses hold iff |m| <= q; RH iff m^2 <= 4q; an admissible RH-violating datum exists iff q >= 5 (the golden fakes)."*

```lean
def Admissible (q m : ℤ) : Prop :=
  0 < N q m 1 ∧ 0 ≤ twoA2 q m ∧ ∀ n : ℕ, 0 ≤ N q m (n + 1)

theorem admissible_iff (q m : ℤ) (hq : 2 ≤ q) : Admissible q m ↔ -q ≤ m ∧ m ≤ q
theorem exists_admissible_not_rh_iff (q : ℤ) (hq : 2 ≤ q) :
    (∃ m : ℤ, Admissible q m ∧ 4 * q < m ^ 2) ↔ 5 ≤ q
theorem rh_int_iff_zeros (q m : ℤ) (hq : 2 ≤ q) :
    m ^ 2 ≤ 4 * q ↔ ∀ s : ℂ, Xi (Real.log q) ((m : ℝ) / Real.sqrt q) s = 0 → s.re = 1 / 2
```

**`RH_pole_shadow_genus_one`** (`lemma`; li_positivity). Title: *"Pole shadow (genus one): positivity of the local weights forces a local pole at least as far right as any off-line local zero; with no local pole in Re s > 1/2, local RH holds."*

```lean
theorem pole_shadow (q m : ℤ) (hq : 2 ≤ q) (hD : 4 * q < m ^ 2) {k : ℕ} (δ : Fin k → ℂ) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : ∀ j, ‖δ j‖ ≤ R) (hRα : R < bigRoot q m) (C : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ C + (∑ j, δ j ^ n).re - tr q m n < 0

theorem local_rh_of_positivity (q m : ℤ) (hq : 2 ≤ q) {k : ℕ} (δ : Fin k → ℂ)
    (hpole : ∀ j, ‖δ j‖ ≤ Real.sqrt q) (C : ℝ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ C + (∑ j, δ j ^ n).re - tr q m n) : m ^ 2 ≤ 4 * q
```

**`RH_lattice_fake_low_zero`** (`lemma`; li_positivity). Title: *"Every zero of a polynomial local factor recurs with period 2 pi i/log p and has a copy below height pi/log 2 < 4.54; the golden hybrid has an off-line zero inside the box certified zero-free for zeta. Finite certification excludes every lattice fake."*

```lean
theorem local_zero_low_copy (P : Polynomial ℂ) (p : ℝ) (hp : 2 ≤ p) (s : ℂ)
    (hs : P.eval ((p : ℂ) ^ (-s)) = 0) :
    ∃ s' : ℂ, P.eval ((p : ℂ) ^ (-s')) = 0 ∧ s'.re = s.re ∧ |s'.im| ≤ Real.pi / Real.log 2
theorem hybrid_zero_in_certified_box :
    ∃ ρ : ℂ, XiH ρ = 0 ∧ ρ.re ≠ 1 / 2 ∧ 1 / 1000 ≤ ρ.re ∧ ρ.re ≤ 999 / 1000 ∧
      0 ≤ ρ.im ∧ ρ.im ≤ 55 / 16
```

**`RH_golden_hybrid_pole_record`** (`lemma`; li_positivity). Title: *"Record of the correction: zeta * Z_{5,-5}(5^-s) has a double pole at s = 1; the repair H4 has positive weights and a simple pole at 1 with residue 11, but a pole at log 4/log 5 in the strip and Ramanujan fails at 5."* Artifact: `Hlit_double_pole`, `H4_simple_pole`, `H4_pole_in_strip`, `w4_pos`, `w4_even_ge`.

### 6.3 Targets (stated only, not typechecked)

- **`RH_pole_shadow_all_degrees`** (`milestone`; D1). The statement is D1a, and then D1b. The first kernel step is D1a, reached through the power-sum route.
- **`MM_window_near_radical`** (`milestone`; D2). The statement is D2. It depends on extending the window explicit formula to L² tests.
- **`MM_window_detection`** (`milestone`; D3; this is the idea's `MM_phi_detection`). The statement is D3, with the even-sector symmetrization.
- **`MM_negctl_dh_window_indefinite`** (`lemma`; Arb-conditional negative control). *"The Davenport-Heilbronn window Weil form is indefinite at x = 40."* The plan: an explicit integer vector; the transcendental matrix inputs enter as BandHyp-style Arb enclosures; the kernel checks c^T Q c < 0 in integer interval arithmetic (ℤ plus a cast, since Rat does not kernel-reduce). The margin at N = 70 is about −1.5e−2, so roughly 12-digit enclosures suffice. The negative-control harness must see a tampered vector fail.
- **`RH_negctl_formal_curve_F55`** (`lemma`; from the arithmetic-geometry lens). Self-reciprocity by `decide`; a_d ≥ 0 for d ≤ 30 from the Lucas recurrence t_d = 5t_{d−1} − 5t_{d−2}, plus a tail lemma; the violation certificate (N_3 − q³ − 1)² = 10000 > 2000; the integral q-symplectic identity C^T ω C = qω.
- **`RH_negctl_eisenstein_shift`** (`lemma`; from the data-discovery lens). Port `EisensteinShiftControl.lean`, discharge `hzero` from `exists_nontrivial_zero_above`, and prove the coefficient identity for −L'/L before any docstring claims it.

### 6.4 Not proposed

These should not be registered, or, if registered, the title must carry CONJECTURE or HEURISTIC:

- the Locator (a conjecture);
- the spectral lens's "no-go for CCM" (a remark);
- the probability lens's region split (heuristic);
- total-positivity statement 8;
- the "unitary half-gap law" (refuted as stated);
- any Beurling-FE "proof strategy" framing.

---

## 7. What this team got wrong, or could not check

### 7.1 Process defects

1. **The arithmetic-geometry lens failed twice in the main run.** The second failure was a final answer over the 128k output cap. It was rerun separately with generation and referees only, so the eighth lens has no build and no skeptic.
2. **The first attempts of the Lee-Yang and data-discovery generators failed.** The run was resumed, and every generator restarted on 2026-09-23.
3. **Handoffs were truncated silently.** Referees received at most 14,000 characters of each idea, builders 16,000, skeptics 8,000, and this synthesis 8,000 / 90,000 / 30,000. The visible consequences:
   - the Lee-Yang circularity referee could not audit claim (D);
   - the spectral builder re-derived everything, because its copy of the reports was cut;
   - the probability lens's literature referee judged a Monte Carlo that had not finished.

   Recommendation, as in the sibling report: pass file paths instead of relaying payloads, and never truncate without saying so.
4. **All agents ran in one session.** Their independence is self-attested.
5. **The build cap did not bind.** The arithmetic-geometry survivor went unbuilt only because its rerun had no build phase.

### 7.2 What the team got wrong

Section 3.6 lists 27 items. The most consequential:

- Theorem B of the meta-barriers idea (the double pole at s = 1).
- The dossier's finite-certificate heuristic, read as a statement about counter-models.
- The even-sector Pontryagin-CvS statement.
- The dynamics lens's normalization of the scattering matrix and its Hecke-orbit claim.
- The Lee-Yang claim that Q is stoquastic.
- The probability lens's "decisive experiment".
- The data-discovery two-channel synthesis.
- The arithmetic-geometry claim that polarization is "the unique missing ingredient".

Every idea's own honesty sections were largely accurate, and most errors were overclaims of scope, status or novelty. Six claims were false as stated: Theorem B (the double pole), the Hecke-orbit claim, Birman-Krein positivity for the true scattering matrix, the stoquasticity of Q, the unitary half-gap law, and the even-sector Pontryagin-CvS statement for Galerkin truncations.

### 7.3 What could not be checked

- **Novelty.** Only targeted searches were run, and no expert was consulted. Open questions:
  - Pontryagin-CvS against Krein-Langer and Kaltenbaeck-Woracek;
  - D2 against Connes arXiv:2602.04022 §6.4 and against CCM;
  - the general pole shadow against the Selberg-class literature on local factors;
  - the local de Bruijn lemma against de Bruijn 1950 and Polymath15;
  - the D calibration (the literature referee found nothing like it, but the search was not exhaustive);
  - Beurling-Hamburger against Bochner, Bochner-Chandrasekharan, Chandrasekharan-Mandelbrojt and Knopp.
- **Paper-level glue not formalized.** The window glue of Build A. Realizability and the operator form of Hecke-wave in Build C. The Li identification, the Weil-window identity and the envelope beyond λ = 1/40 in Build B. Base-point genericity.
- **Interval certification missing.** D's onset at x = 31; the 21i/20 zero.
- **Numerics not re-run by this writer.** The builds' Python numerics were reproduced by the skeptics. This writer re-ran only the Lean files and the integer spot checks in section 3.5.
- **Artifacts outside the skeptic filter.** The scratch Lean files and the generator-phase numerics (section 3.7). They live in `/private/tmp` and are ephemeral.
- **This writer's own arguments are unrefereed.** These are D1b, D2, the extension of the periodicity obstruction to general conductor and shift, and the Selberg-Ruelle normalization remark.
- **Smaller unchecked items.** Zhu's window margin for the golden fake (0.8 against 0.8047) was not checked against the corpus's Fourier convention. The "Theta 1.77" figure for H_{13,−8} was not checked. Katkova's PF_44/PF_43 indexing was not checked against her paper.
- **Registry texts.** The target statements in 6.3 are untypechecked. The proved-node texts in 6.1 and 6.2 are verbatim from the artifacts, but none was re-elaborated as a standalone statement module.
- **Nothing is committed, and nothing has been through CI.**

### 7.4 Status

`conjecture1_proved = False`. The Riemann Hypothesis remains open. This team located, more sharply than before, where the Euler product's positivity is spent. That is on the pole direction, and it moved no clause of the wall.

---

## Appendix: reproduction

```sh
# Lean, single-file elaboration on the pinned islands (never `lake build`; the .lake is shared)
LOCK=/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/leanlock.sh
cd telperion/examples/li_positivity/lean
$LOCK lake env lean Crux/Crux_spectral_operator.lean   # 32 axiom lines
$LOCK lake env lean Crux/Crux_meta_barriers.lean       # 161 axiom lines
$LOCK lake env lean Crux/Crux_dynamics_ergodic.lean    # 94 axiom lines
cd ../../rvm_bridge/lean
$LOCK lake env lean Crux/Crux_spectral_operator.lean   # 22 axiom lines
$LOCK lake env lean Crux/Crux_meta_barriers.lean       # 88 axiom lines

# numerics (run from scratch copies to leave committed outputs untouched)
cd telperion/research/crux_spectral-operator && /usr/bin/python3 validate_forms.py   # see README section 8 for the rest
cd ../crux_meta-barriers && /usr/bin/python3 golden_fake_numerics.py                 # 14 checks
cd ../crux_dynamics-ergodic && /usr/bin/python3 certify_zeros.py                      # Arb windings
```

Workflow journals: `~/.claude/projects/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/subagents/workflows/wf_6c4fbedf-c32/journal.jsonl` and `.../wf_ccfd2420-544/journal.jsonl`.

---

## Addendum (lead, 2026-09-23): the arith-geometry lens, re-run

The arith-geometry generator in this workflow **failed with an API error**, not a referee kill: its final
answer exceeded the 128,000-token output cap. The synthesis above therefore lists that lens as failed.
It was re-run separately (workflow `wf_ccfd2420-544`) with the same dossier and brief, an output-size
guard, and the same three hostile referees. Result: **survived, 0 of 3 kills** (scores 4, 4, 3).

- **Idea: formal curves as negative controls.** A formal curve is a self-reciprocal integer polynomial
  P whose zeta P/((1-T)(1-qT)) is an Euler product with nonnegative integer exponents. It carries every
  zeta-level Weil ingredient: exact FE, Euler product, Frobenius lattice with Weil pairing and Rosati
  involution, effective formal square, formal Lefschetz numbers, and the exact radical.
- **Golden fake over F_5:** P = 1 + 5T + 20T^2 + 25T^3 + 25T^4 has off-line zeros with Re rho = 0.79899.
  The Weil bound holds at k = 1, 2 and fails at k = 3 (100 > 44.7), an exact integer certificate.
  Every referee reproduced it independently. A family F(q, m) has Re rho_max -> 1.
- **Conclusion:** the only Weil ingredient that zeta-level data cannot supply is the **polarization**
  (Rosati positivity / Hodge index on C x C). "Use the Euler product and the FE jointly" is necessary but
  not sufficient.
- **Convergence:** this matches the meta-barriers lens (golden-fake relativization barrier, 0 kills,
  kernel-checked) and the axiom-isolation team (class P = {zeta}; Beurling-Hamburger Theorem A). Together:
  finite positivity certificates can be fooled, and formal Weil structure can be faked. The rigid lever is
  the archimedean factor coupled to N, i.e. an archimedean positivity tied to the Euler product.
- Notes and referee record: `telperion/research/crux_arith_geometry/`. conjecture1_proved = False.
