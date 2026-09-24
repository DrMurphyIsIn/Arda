# RH crux, round 2: five lenses on the window and the barrier

*Team report for the workflow run `wf_0465504d-707` (round 2 of the RH crux program), written 2026-09-23 on branch `cl/crux2` of the `arda-crux2` worktree (HEAD `7da086c3e`). Round 1 is `RH_CRUX_RESEARCH_2026-09-22.md`, and its companion class-P report is `RH_AXIOM_ISOLATION_2026-09-22.md`. This report cites both wherever round 2 builds on them.*

*`conjecture1_proved = False`. The Riemann Hypothesis is open. Nothing below proves it, reduces it, or moves any clause of the wall. Every mathematical claim carries a tag from section 0.3. Anything no referee or skeptic has seen is labelled as such.*

---

## 0. Preamble

### 0.1 The brief and the two deaths

The brief was the same as in round 1: genuinely new, correct mathematics near the crux. Two failure modes were fatal:

1. **Circularity.** The key property is equivalent to RH by a short argument.
2. **Negative-control failure.** The argument goes through verbatim for Davenport-Heilbronn (D), an Epstein zeta function with off-line zeros, the golden fake, or ζ times a surgered Euler factor.

An idea survived if at most one of its three hostile referees killed it. The referees covered circularity, negative controls, and literature/novelty. Survivors were built, and a build counts as verified only if a skeptic re-ran it and could not refute it.

### 0.2 What happened, in one paragraph

Round 2 ran five lenses, each aimed at a gap round 1 left open: **verified-window**, **semilocal-archimedean**, **rigidity-rate**, **unified-barrier** and **kappa-certify**. All five survived. Two drew one kill each: rigidity-rate on novelty, and kappa-certify on its negative control, which the author had declared himself. All five were built in the Lean kernel, and all five skeptics failed to refute them. This writer re-elaborated all five Lean files (section 3.1). The results fall into two groups:

- **Two instance lenses: verified-window and kappa-certify.** Working independently, they found the same mechanism. The prime comb of the Weil functional reaches a test on the window only through the operator norm of the comb compressed to that window, not through the comb's pointwise supremum. That roughly halves the exponent of Zhu's doubly exponential barrier, and at L = 2.3 it cuts it by more than a factor of three. The two lenses produced:
  - an Arb-certified exact positivity record of κ_ζ(x) = 0 for x ≤ 11.006, up from Zhu's 4.95;
  - a kernel-checked form-level comb constant;
  - conditional almost-positivity, λ_min ≥ −10^−997, up to support 4.5.
- **Three no-go lenses: semilocal, rigidity and unified.** Between them they show:
  - every semi-local or finite-precision input is fooled, by an explicit Euler-product family W_{p,c}, by pole-shadow fakes, or by a Pólya-kernel probe;
  - every non-circular global input that defeats the fakes collapses the model class to ζ;
  - the zero-free-region rate does not come from the rigidity mechanism.

No lens produced a route to RH, and none claimed one. By the brief's own standard, round 2 is correct, mostly negative mathematics plus one real certified-computation advance off the crux. There is no progress on the wall.

### 0.3 Tags

- **THEOREM-kernel-checked**: elaborated in Lean 4, every `#print axioms` line within `[propext, Classical.choice, Quot.sound]` (or a subset), and no `sorry`. The artifact path is given.
- **THEOREM-paper-proof**: a written proof that survived a hostile referee, or a classical theorem cited as such.
- **THEOREM-certified-computation**: Arb ball arithmetic outside the kernel, relative to paper lemmas that are named.
- **CONJECTURE-with-evidence**, **HEURISTIC**: as named.
- **COMPUTED**: floating-point or high-precision numerics that are not interval-certified.
- **Writer's sketch (unrefereed)**: an argument first written in this report. No one else has checked it.

### 0.4 Provenance

1. **The synthesis payload was truncated.** The judged-ideas data given to this writer stopped mid-sentence, inside the second unified-barrier referee. It contained no kappa-certify record and no build or skeptic records. Every record was recovered from the workflow journal, `~/.claude/projects/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/subagents/workflows/wf_0465504d-707/journal.jsonl`. It has 62 lines: 5 ideas, 15 referee verdicts, 5 builds and 5 skeptic verdicts, followed by the start of this synthesis. Numbers quoted below come from those records.
2. **Referee reports did not reach the builders in full.** The kappa-certify and semilocal builders both say the referee JSON was truncated out of their task text, so each re-audited the idea from scratch. The two builds therefore double as independent checks. It also means some referee corrections were resolved or overridden without the builder seeing them (section 2.2).
3. **Lean re-run by this writer, 2026-09-23.** All five files were re-elaborated with `leanlock.sh lake env lean` on their pinned islands. Results are in section 3.1. This writer did not re-run the Python or Arb numerics; the skeptics did.
4. **Independence.** Generators, referees, builders, skeptics and this writer are all subagents of one session, so their independence is self-attested. Several referees had used up their web-search budget, which makes the novelty checks partial (section 6).

---

## 1. What round 1 established

Round 1 is `RH_CRUX_RESEARCH_2026-09-22.md`, on branch `cl/crux`. Eight lenses ran, four survived, and three were built in the kernel. It found no route to RH. Its lasting content:

- **The positivity principle** (HEURISTIC as a principle; each instance tagged separately). Nonnegative von Mangoldt coefficients see real singularities and nothing else. Its local form is the kernel-checked **pole shadow**: an off-line local zero with nonnegative weights is shadowed by a real local pole at least as far right. Every Euler-product fake in the zoo carries such a singularity.
- **Build A, the Weil-Pontryagin window core.** The unconditional inertia bound κ ≤ #off-line pairs (`weil_negIndex_le_offline`), and the relabeling `rh_iff_weil_negIndex_zero`.
- **Build B, the golden-fake barrier.** An Euler-product fake with Λ ≥ 0 that passes the pointwise and Gaussian layers and vanishes off the line.
- **Build C, the channel no-go.** Seven unitary-scattering "channel axioms" hold for ξ and for a fake with an off-line zero.
- **The class-P companion run.** Integer frequencies plus the ζ-shape FE plus Λ ≥ 0 force F = ζ (`classP_eq_zeta`). The W1(29,11) fooling lemma keeps the FE but breaks P2.
- **Four ranked directions.** D1: the pole shadow in every degree. D2: the near-radical lemma. D3: detection without masking. D4: closing the degree-one axiom lattice.

The HAVE/NEED line from the dossier also carries into round 2. HAVE is "there is L0 such that window Weil positivity holds for all g supported in [−L0, L0]". Zhu (arXiv:2608.24827) certified L0 = 0.8, which is x = 4.95. NEED is "for all L".

Round 2's lenses were chosen to press on four places:
- the HAVE side of clause I (verified-window, kappa-certify);
- the semi-local route suggested by Connes-Consani (semilocal-archimedean);
- whether Theorem A's rigidity carries a rate (rigidity-rate);
- whether round 1's barriers are really one barrier (unified-barrier).

---

## 2. The five lenses

### 2.0 Scorecard

Referee order is circularity / negative control / literature. A cell reads as the score (0 to 10), plus KILL if that referee killed.

| Lens | Best idea (short) | Circ. | Neg. ctl | Lit. | Kills | Mean | Self | Outcome | Build | Skeptic |
|---|---|---|---|---|---|---|---|---|---|---|
| verified-window | form-level comb constant + zero/arithmetic gluing | 5 | 6 | 4 | 0 | 5.00 | 6 | survives | kernel (rvm_bridge) | not refuted |
| semilocal-archimedean | S-local horizon is q + O(log q) | 5 | 5 | 4 | 0 | 4.67 | 4 | survives | kernel mod `ProbeInput` (rvm_bridge) | not refuted |
| unified-barrier | one family W_{p,c} is every round-1 barrier | 5 | 5 | 4 | 0 | 4.67 | 5 | survives | kernel (li_positivity) | not refuted |
| rigidity-rate | rigidity carries no rate | 5 | 5 | 3, KILL | 1 | 4.33 | 5 | survives | kernel (li_positivity) | not refuted |
| kappa-certify | κ_ζ(x) = 0 certified to x = 11.006 | 3, KILL | 5 | 5 | 1 | 4.33 | 6 | survives | kernel cores + Arb (li_positivity) | not refuted |

No idea scored above 6 from any referee. The highest mean, 5.00, went to verified-window, and its headline structural claim was refuted by the same referee pass (section 2.1).

### 2.1 verified-window: a form-level comb constant, and gluing verified zeros to the window

**Result.** Zhu's normalization throughout: supp f ⊂ [−L, L], F = f̂, and window x = e^{2L}.

1. **Form-level comb constant.** On the window, the prime comb enters Q only as ⟨f, P f⟩, where P = Σ (Λ(n)/√n)(τ_{log n} + τ*_{log n}) is compressed to L²[−L, L]. Its top value A_win(L) is about 0.30 to 0.41 of the pointwise mass A_L = Σ 2Λ(n)/√n. In the PNT model A_win ~ e^L, against A_L ~ 4e^L. Because Λ ≥ 0, every twist of the comb is entrywise dominated by the untwisted comb.
2. **Theorem 1** (THEOREM-paper-proof). A zero-free envelope reduction. It moves Zhu's cutoff from 2πe^{A_L} to about 2πe^{A_win}. At L = 1.4166 that is about 10^3 instead of 1.85e5.
3. **Theorem 2** (THEOREM-paper-proof; hypotheses: zeros on the line to height T, and an upper bound for A⁺).
   - Split G = |F|² as φG + |ωF|², with φ = K(2 − K) ≥ 0 and ω = 1 − K the transform of a measure on [−δ/2, δ/2]. Because the split is on |F|² and not on F, there are no cross terms.
   - The piece φG goes to the zero side, where each verified zero contributes φ(γ)|F(γ)|² ≥ 0.
   - The piece |ωF|² goes to the arithmetic side, bounded by A⁺ = A_win(L + δ/2).
   - The conclusion is Q ≥ M_T − ε, with M_T positive semidefinite.
4. **Instance.** At T = 640000, which is Arb-conditional in the program as `AllZeros_h640000`:
   - idea stage: λ_min(Q_L) ≥ −10^−1157 for every L ≤ 2.25, using a float A⁺;
   - builder, with the kernel-certified A⁺ = 11.161373: −10^−997.
   L = 2.25 is support 4.5, a CCM window of about 90.

**Referee verdicts.** 0 kills; scores 5 (circularity), 6 (negative control), 4 (literature).

Decisive objections:
- **The sharpness no-go (b) and the rate (c) are false as stated** (circularity referee, confirmed by his own twisted scan). Kronecker alignment reaches A_win only at heights where log(r/2π) already dominates. At L = 1.4166 the twisted top value is 2.98 on r ∈ [100, 300], against A_win = 3.777. The last height where it beats log(r/2π) is about 79, not about 275. There is also a clean contradiction argument: a test at height r < 2πe^{A_win} with quotient near A_win would make Q negative at heights where the zeros are verified to lie on the line. So (b) covers only methods that use one twist-uniform constant, and in that form it is a tautology. The "fourth root of Zhu" rate falls with it, and so does "contradicts Zhu's Remark 1.6". The builder restated the gain as coming from the window (an uncertainty principle), not from non-alignment of phases.
- **Almost-positivity is not positivity** (all three referees). Zhu certified exact positivity at L = 0.8. The bound −10^−1157 at L = 2.25 is far below the true floor λ*(2.25) ~ 10^−470, so it does not decide the sign of Q_L. "Exact positivity reduces to one finite inequality" is also wrong as stated, because M_T contains an envelope integral over all frequencies. It is a semi-infinite form inequality.
- **Mis-tagging.** The idea-stage A⁺ enclosures were float64, not "symbolic-exact". The builder fixed this with a kernel certificate, but only at L′ = 2.3.
- **Novelty** (literature referee, web budget exhausted). The key lemma is textbook: Schur/Perron domination, plus the fact that a compressed shift has smaller norm than its symbol's supremum. What is new is its application to Zhu's cutoff.

**Salvage** (adopted by the builder):
- keep Theorem 1, Theorem 2 and the A_win table;
- retract (b), (c) and the Zhu-contradiction line;
- state (b) as a limit of methods that use a frequency-independent constant;
- replace A_win by a **height-local twisted constant** (section 4 makes this precise);
- interval-certify A⁺;
- make exact positivity the next deliverable.

### 2.2 semilocal-archimedean: the S-local horizon is the next prime plus a logarithm

**Result.** Let S_q be the primes below q, and let Q_{S_q} be the Weil functional with only the primes in S_q (and their powers) kept. Q_{S_q} equals the full Weil form on (1/q, q). So "S-local positivity on its natural window" is window Weil positivity, which is a relabeling, and the lens says so. The real question was whether Q_{S_q} stays positive beyond q, which would leave a semi-local reservoir. The answer is essentially no.

- **The probe.** g_x = Φ′·1_W, where Φ is the Pólya kernel (Φ̂ = Ξ). Its transform vanishes at every zero, on or off the line, so Q(g_x) is super-exponentially small. Deleting the prime q costs 2(log q/√q)·h(log q) < 0, by a kernel-checked sign lemma.
- **Onset law.** Balancing the two sizes gives Δ e^{2πΔ} = √q/(4π), that is Δ(q) = W0(√q/2)/(2π) ~ (1/4π) log q.
- **Horizon.** x*_{S_q} ≤ q + Δ(q).

The lens also found:
- S-local positivity is non-monotone in S.
- The pure archimedean pole-free functional (Connes-Consani's object) is indefinite at x = 3.3 and numerically positive up to about 3.27.
- A **fooling identity.** For a one-prime surgery at p0 ∉ S, Q_S^F = Q_S^ζ + 2 log p0·Id.
- A **surgery detection law**, with the exact plateau log p0 (2 − a). For the golden fake this is log 5 (2 − √5) = −0.379937.
- A **two-sided precision barrier.** Window positivity at x pins every Λ(n), n < x, to precision about e^{−c(x − n)}.

**Referee verdicts.** 0 kills; scores 5, 5, 4.

Decisive objections:
- **The title overclaims.** The theorem gives x*_{S_q} ∈ [q, q + Δ(q)]. The lower end is RH-window, proved only for q ≤ 3. The Galerkin data show the true excess *shrinking* with q while the probe's Δ grows. So the Lambert-W law describes the probe, not the horizon, and the honest headline is an upper bound.
- **Effectivity.** Part (b) is asymptotic, with constants only sketched. The claimed "valid for q up to 1e11 via Platt" range is not justified. The builder corrected it to q ≤ 5e7.
- **The kernel skeleton is trivial algebra.** Every analytic input is a hypothesis.
- **Novelty is modest** (literature referee).
  - The qualitative no-go is nearly forced. Deleting the prime q multiplies ζ by (1 − q^{−s}), whose zeros sit on Re s = 0. So the horizon theorem is the a → ∞ case of the lens's own surgery detection law, and the two results are really one.
  - The mechanism is the known near-null phenomenon of Connes-Consani-Moscovici and Connes-van Suijlekom.
- **A disputed constant.** The circularity referee said the overlap constant was off by a factor of 4, 16π⁶ against 64π⁶. The builder, who never saw the referee report, re-derived the law independently. His explanation: the referee's script uses half the kernel, so the idea's 64π⁶ is correct in the idea's normalization. The builder's overlap ratios (0.69 → 0.988) and zero-side ratios (1.07 → 0.995) converge to the law in the idea's normalization. This writer treats the dispute as resolved in favour of the idea's constant, with the normalization stated explicitly.

**Salvage:**
- file the result as a no-go note, retitled as an unconditional upper bound;
- merge the horizon theorem and the surgery law;
- interval-certify one onset;
- keep the fooling identity as a standing negative-control filter;
- downgrade the "robust input cannot prove window positivity" meta-claim to HEURISTIC;
- keep the conjectured super-exponential sharpening Δ*(q) → 0 as the one open item.

**Relation to round 1.** The probe Φ′·1_W is an explicit near-radical vector. Its Q-size bound is the form-level half of round 1's direction D2, which is written as an operator-norm bound. The operator-norm version is still open.

### 2.3 rigidity-rate: rigidity carries no rate

**Result.** The lens made Theorem A quantitative (FE + positive Beurling measure + gap ⇒ ζ, from the class-P run). Both of its steps become exact finite identities, and both are kernel-checked:
- the FE defect tested on the triangle (1 − |ξ|)_+ equals the sinc²-weighted non-integrality of N, which is at least (8/π²)∫‖x‖²x^{−2} dN;
- the defect tested on the modulated triangle equals the multiplicity error a_m − r.
So quantitative rigidity delivers only finite coefficient data.

Three consequences follow.
1. **The pole-shadow fake.** Set F = ζ(s)/(ζ_{≥X}(s + δ − it)·ζ_{≥X}(s + δ + it)), where ζ_{≥X} is ζ with the Euler factors below X removed. It has:
   - Λ_F ≥ 0, a_n ≥ 0, and a_n = 1 for n < X;
   - Riemann's theta relation to 121 digits on y ∈ [1e−10, 1e10] at X = 10^6;
   - a zero at 1 − δ + it, for any t.
   Hence finite data gives no zero-free region at all. Agreement with ζ's coefficients up to T^A with A ≥ 3.86 still allows a zero inside the Mossinghoff-Trudgian-Yang region.
2. **With growth added.** Rescaling and grafting Broucke's 2025 Beurling systems gives P2 systems with FE-convexity growth whose zeros lie at distance about 4 loglog t/log t. So these hypotheses do not imply Vinogradov-Korobov.
3. **Transfer lemma.** Agreement to scale t^{1/(1−θ)+} is identification with ζ.

The resulting dichotomy: fixed precision is blind, and growing precision is identification.

**Referee verdicts.** One kill (literature, score 3); the others scored 5 and 5.

Decisive objections:
- **Novelty kill** (literature referee):
  - The triangle/sinc² pair is the Fejér kernel, and Hamburger-type rigidity through a Fourier window is classical.
  - "Finite data gives no zero-free region" is folklore.
  - The dVP ceiling for Beurling systems is Diamond-Montgomery-Vorhauer (2006) plus Broucke.
  - The transfer lemma is the Hardy-Littlewood approximate formula (Titchmarsh 4.11) plus Rouché.
- **"FE broken only beyond X" is false as worded.** F has infinitely many poles inside the strip, at ρ − δ ± it. So it breaks analytic continuation with finitely many poles, which is exactly the hypothesis Hamburger uses. A theta relation on a y-window is far weaker than the Mellin FE.
- **"The dVP cap" is not established.** The fakes sit at 4 loglog t/log t, which is outside dVP's c/log t, and the true ceiling lies somewhere between the two. The honest statement is "not VK, not better than C loglog t/log t".
- **The rescaled witnesses are weighted measure systems**, not integer Beurling systems.

**Salvage.**
- Keep the window identities as a quantitative Hamburger lemma.
- Keep the pole-shadow family as a negative-control generator.
- Retitle claim 2.
- Keep the intermediate regime (precision t^A with A < 1/(1 − θ) and uniform K) as the stated open problem, together with the Mellin-local FE-defect question.

**Builder advance** (section 3). The fake was rebuilt from Mathlib's `riemannZeta`, so coefficients and analytic object are tied together in the kernel. The builder also added:
- a kernel-checked **expulsion** core, with the paper step on top of it;
- a **competing conjecture, restricted-support rigidity**: every new zero at depth η costs log K ≳ X^{1−θ−η}/log X. The evidence favours this conjecture over the lens's dVP-cap conjecture.

### 2.4 unified-barrier: semi-locality is the relativization barrier

**Result.** One family, W_{p,c}(s) = ζ(s)(1 + c p^{−s} + p·p^{−2s}), with 2√p < c < p + 1. It is a surgery at a single prime. Its completion ξ·surg satisfies the exact Γ_R functional equation with conductor p². For every finite S, every N0 and every L there is a W_{p,c} that:
- has p ∉ S, p² > N0 and log p > L;
- satisfies the semi-local axioms X1 to X6 (local factors on S, FE shape, P2 on [0, N0), the channel axioms, bounded-support Weil positivity, and robust positivity);
- vanishes off the line inside the strip.

The same family unifies round 1's barriers:
- the golden fake is W_{5,5};
- W1 is W_{29,11};
- the channel axioms amount to the *trivial* local bound |c| < p + 1;
- `classP_sharp`: the class-P collapse theorem is sharp exactly at P2.

The lens also shows:
- **Exhaustion.** Each non-circular global input forces the Hasse bound c² ≤ 4p. After that, `rh_W_iff` makes class-level RH identical to RH.
- **Sharpness of M.** The corpus's LowHeightBox theorem is not semi-local: W_{41,13} violates it.

**Referee verdicts.** 0 kills; scores 5, 5, 4.

Decisive objections:
- **X5 is overclaimed.** Z_W(g) = Z_ζ(g) + 2 log p·g(0) is just the conductor term of the explicit formula. It *transfers* positivity from ζ to W, one way only. For large L, positivity of ζ is RH-strength. The skeptic flagged the builder's summary for still calling this an "iff". The Lean header states it correctly.
- **The KP99 citation is misquoted.** KP99 classifies S#_1 as sums Σ P_j(s)L(s + iθ, χ_j). Getting from there to "L(χ) times surgeries" needs an argument the idea did not supply.
- **Exhaustion holds only for quadratic surgeries.** The idea's own degree-4 example passes P2 at p, p² and p³.
- **"Ramanujan at p" is mislabelled.** a_W is bounded, so Selberg's Ramanujan axiom holds. What kills W is the θ < 1/2 Euler axiom.
- **Novelty is folklore.** Non-Ramanujan local factors are exactly why the Selberg class has its axioms, and "support-prime duality" is the explicit formula.

**Salvage.** Keep it as internal infrastructure:
- a standing negative-control generator;
- a filter that tags each corpus node as semi-local-valid or not.
Also restate X5 as a transfer, generalize the killers, and fix the KP99 step.

**Builder advance.**
- The support-prime duality itself is now in the kernel (`surg_explicit_formula`, Poisson summation over the lattice of zeros).
- `surgery_not_selberg`: the Selberg Euler axiom fails for every surgery, including on-line ones.
- `prime_square_surgery` upgrades the degree-4 example to a kernel theorem: P2 at every prime square, and still an off-line zero.

### 2.5 kappa-certify: κ_ζ(x) = 0 certified to x = 11.006

**Result.** κ_ζ(x) = 0 is certified at x = e^{307/128} = 11.006, which covers every prime power ≤ 11 (THEOREM-certified-computation). The certificate gives Q ≥ 6.60e−49·‖f‖², with λ*_even ∈ [6.60e−49, 8.83e−49]. Zhu's previous certified record was 4.95, and a literature referee confirmed that record by fetching arXiv:2608.24827v2 directly. The certificate rests on:
- Legendre-Galerkin blocks in Arb, with rigorous composite Gauss-Legendre quadrature, verified blocked Cholesky, and super-exponential tails;
- exact-rational 8×8 LDLᵀ Schur-complement cores in the kernel, with tamper controls.

The new method is a **window-aware reduction**:
- *Lemma A*: path-graph orbits give ‖P_A‖ ≤ Σ c_n cos(π/(⌊2A/log n⌋ + 2)), about A_L/2.
- *Lemma B*: an erf-plateau leakage bound.
- Together they move the threshold from 2πe^{A_L} = 31535 to 957 at x = 11. This is the same idea as verified-window's A_win, found independently.

The negative control was declared up front. The same certificate goes through for D with margins 10^23 to 10^40 larger, and κ_D ≥ 2 appears only at x ≈ 40.

**Referee verdicts.** One kill (circularity referee, score 3; the kill is for negative-control failure); the others scored 5 and 5.

Decisive objections:
- **The certificate is blind to the Euler product at every scale it can reach.** D passes it with larger margins. κ = 0 at x ≤ 11 excludes no zero that is not already excluded to 3e12.
- **The kernel label is mostly decorative.** The load-bearing steps are outside the kernel: the Schur reduction from 2300 modes, the quadrature, the Bessel recurrences, and the frequency-side Weil form on all of L²[−a, a]. The kernel checks the 8×8 cores.
- **The Q formula is written wrong for complex f.** It needs (1/2π)∫_ℝ, not (1/π)∫_0^∞. This is presentational.
- **κ_D(40) ≥ 2 needs a 2-dimensional negative subspace.** The builder resolved this: there is exactly one negative eigenvalue per parity sector at N = 110.
- **Feasibility of the separation scale** (literature referee). Extrapolating the Landau-Widom law to x ≈ 31 gives λ ~ 10^−150 and a cutoff near 10^6. That is infeasible for dense Cholesky.

**Salvage:**
- make the ζ-vs-D separation at x = 40 a required negative-control fixture for every window emitter;
- keep Lemmas A and B as a reusable reduction pair;
- keep the three documented numerical failure modes as emitter hardening;
- write a short note extending Zhu;
- the one direction with arithmetic content: certify the Fejér-mass bound, then aim at a *zero-free* certificate κ_ζ(40) = 0 alongside κ_D(40) ≥ 2 (section 4).

---

## 3. Verified builds (skeptic-unrefuted) and refuted claims

### 3.1 The five builds, re-elaborated by this writer

Every build is untracked in `arda-crux2` on `cl/crux2`. Nothing is committed, and nothing is wired into a lakefile or AxiomGuard. The table shows this writer's re-run on 2026-09-23 with `leanlock.sh lake env lean <file>`. Every run exited 0 with 0 errors and no `sorryAx`.

| Build | File (under `telperion/examples/`) | Lines | sha256 prefix | `#print axioms` | Time |
|---|---|---|---|---|---|
| verified-window | `rvm_bridge/lean/Crux/Crux2_verified_window.lean` | 2115 | `50e7c931` | 22: 20 standard three, 2 `[propext]` (`cw_check`, `checkRows_sound`) | 66 s |
| semilocal-archimedean | `rvm_bridge/lean/Crux/Crux2_semilocal_archimedean.lean` | 1069 | `a793aabb` | 46: all standard three (one line-wrapped) | 21 s |
| kappa-certify | `li_positivity/lean/Crux/Crux2_kappa_certify.lean` | 998 | `d94a824b` (matches claim) | 22: all standard three | 40 s |
| rigidity-rate | `li_positivity/lean/Crux/Crux2_rigidity_rate.lean` | 1604 | `98edde22` (matches claim) | 80: all standard three | 39 s |
| unified-barrier | `li_positivity/lean/Crux/Crux2_unified_barrier.lean` | 2641 | `72c88517` (matches claim) | 133: 129 standard three, 2 `[propext]`, 2 none | 43 s; 39 lint warnings |

Unified-barrier imports the round-1 modules `Crux_meta_barriers`, `Crux_dynamics_ergodic` and `Crux_axiso_theorem`. These are not `lean_lib` targets, so a fresh checkout must run `research/crux2_unified-barrier/build_deps.sh` first. The rvm_bridge and li_positivity islands are on different toolchains and compose only at registry level.

### 3.2 What each verified build establishes

**verified-window (skeptic: not refuted; he re-ran Lean, rebuilt the file byte-identically, and reproduced every ε row).**
- THEOREM-kernel-checked:
  - `schur_comb` and `primeSide_autocorr_le`: a continuous Schur/Collatz-Wielandt test for the window-compressed positive comb, stated on the registry's E8 explicit-formula vocabulary.
  - `primeSide_autocorr_twist_le`: the same constant bounds every frequency twist.
  - `primeSide_autocorr_le_cert`: ‖primeSide(g ⋆ g̃)‖ ≤ 11.161373010·‖g‖² for every continuous compactly supported g vanishing off [−2.3, 2.3]. This is an exact-integer certificate: 920 cells, 35 prime powers below 100, and log p enclosures proved from Mathlib, checked by `decide +kernel`.
  - `combMass_gt_three_lam`: the certified constant is under one third of the pointwise mass, which is about 33.79.
  - `weil_almost_pos_cert`: Theorem 2's gluing on `RvMBridge4.limit_explicit_formula`, conditional on four named inputs (contraction, zeros to height T, a tail bound E1, an archimedean bound E2).
- THEOREM-paper-proof, with one correction: R must be the root of log(R/2π) − 1/R = A⁺. The idea's R = 2πe^{A⁺}(1 + 10^−6) is not covered by Zhu's Lemma 3.1.
- COMPUTED, conditional on zeros to 640000: λ_min(Q_L) ≥ −10^−997 for all L ≤ 2.25.
- Not kernel-checked:
  - the three analytic inputs to the gluing;
  - the other windows' constants (exact-integer Python);
  - the Galerkin lower end 11.0586;
  - Theorem 1 with general ω;
  - sharpness.

**semilocal-archimedean (skeptic: not refuted; he re-ran Lean and all three numerics scripts).**
- THEOREM-kernel-checked, on the registry Weil functional:
  - the deficit identity;
  - the relabeling `rh_iff_semilocal_natural_windows`, labelled as Weil's criterion restated;
  - the sign lemma and the deficit bound;
  - `horizon_of_probeInput`: `ProbeInput q x` makes W_{S_q} indefinite on every window ≥ log x;
  - the precision-barrier structural half;
  - `latticeForm_nonneg_iff` and `surgery_local_rh_iff`: the surgery term is PSD for every N iff |a| ≤ 2, i.e. iff local RH holds;
  - `pair_probe_surgery_value`: the plateau.
- **`ProbeInput` is a named, unproved obligation.** It needs Φ̂ = Ξ, Φ′ < 0 and a tail sum over zeros, none of which is in Mathlib or Zeta23.
- COMPUTED, reproduced independently: the onset law converges to W0(√q/2)/(2π) (gap from 11% at q = 7 down to 0.2% at q = 199); 14 Galerkin negative eigenvalues agree with an independent zero-side evaluation.
- The skeptic's re-runs overwrote the three numerics JSON files. The regenerated values match every quoted figure.

**kappa-certify (skeptic: not refuted; he rebuilt the tamper twins and regenerated the new x = 11 odd core byte-identically).**
- THEOREM-kernel-checked:
  - `LemmaA.comb_bound` and `prime_comb_bound`: Lemma A in *continuous* form, for measurable real g, via a Perron weight on the translation cells. There is also a signed version, `shift_bound_signed`, with |c_i|.
  - `schur_link`: PSD from a PD block plus a Schur complement inside an Arb box.
  - Four exact LDLᵀ cores, at x = 6.996 and x = 11.006, even and odd. The x = 11.006 odd core is new.
- THEOREM-certified-computation, modulo paper lemmas P1 to P3 (the explicit formula on the full form domain, the Binet envelope, Lemma B): κ_ζ(x) = 0 for every x ≤ 11.006.
- The skeptic added two independent checks:
  - Q₄₀ − R″₄₀ is PSD across two unrelated code paths (u-domain against Legendre), with minimum eigenvalue +1.9e−55;
  - Rayleigh-Ritz upper bounds at N = 160 stay above the certified lower bounds.
- Audit findings F1 to F7 were fixed or documented. F1 was a radius-inflation gap in the x = 11 reload, now regenerated. F7: e^{133/64} = 7.9895, not 7.991.

**rigidity-rate (skeptic: not refuted; 80/80 axioms clean, numerics identical to 1e−9).**
- THEOREM-kernel-checked:
  - the window identities;
  - the pole-shadow fake built from Mathlib's `riemannZeta` (`LSeries_fakeCoeff_eq_poleShadow`, `poleShadow_simple_zero`, `poleShadow_real_double_zero`);
  - `finite_data_no_zero_free_region`, whose only hypotheses are X > 1, δ > 0 and t ≠ 0;
  - `mty_fake`, with A ≥ 3.86;
  - the expulsion core `poleShadow_real_exp_large`;
  - `expulsion_of_transfer_bound`, conditional on the transfer inequality.
- THEOREM-paper-proof: the transfer lemma, rescaling and grafting.
- THEOREM-paper-proof conditional on an external preprint: the rate cap. The builder read Broucke arXiv:2507.13780 Thm 1.6 in the PDF itself; it allows α = 1 and gives a discrete system.
- The skeptic notes three weaknesses:
  - `fake_window_tests_blind` is essentially trivial;
  - "order exactly 1 + ord ζ" is not literally in the kernel;
  - F is only meromorphic, with poles further left.

**unified-barrier (skeptic: not refuted; he re-ran Lean and all three numerics scripts, 88 + 34 + 1 PASS).**
- THEOREM-kernel-checked:
  - `semilocal_barrier_full`: no hypotheses; X1 to X4 and X6 outright, the surgery-side lattice sum for X5, and an off-line zero in the strip;
  - `surg_explicit_formula`;
  - `channelAxioms_W_iff`;
  - `robust_positivity_iff`;
  - `surgery_not_selberg`;
  - `exhaustion`, `rh_W_iff`, `prime_square_surgery`;
  - `classP_sharp`, `golden_unified_full`, `lowHeightBox_nonrelativizing`.
- Caveat (skeptic): X5 as a transfer is paper-level and one-directional. ζ's Weil functional is not defined on this island.
- Paper-level: M is non-vacuous, and degree-1 completeness via KP99, which is cited and misquoted (section 2.4).

### 3.3 No build was refuted. Claims that were refuted, retracted or corrected

| Claim (lens) | Fate | Replaced by |
|---|---|---|
| "Any method using verified zeros below T and window arithmetic above T needs T ≥ 2πe^{A_win}"; rate L(T) = log log T − log c "caps every method" (verified-window) | **Refuted** by the circularity referee's twisted scan and contradiction argument | A limit of methods with one frequency-independent constant only (builder) |
| "Contradicts Zhu Remark 1.6" (verified-window) | **Retracted** | The gain comes from the window (uncertainty principle), not from phase non-alignment |
| "Exact positivity reduces to one finite inequality" (verified-window) | **Corrected** | A semi-infinite form inequality: Galerkin plus a tail argument |
| R = 2πe^{A⁺}(1 + 10^−6) (verified-window) | **Corrected** (builder) | R = root of log(R/2π) − 1/R = A⁺; ε unchanged |
| A_win enclosures "symbolic-exact" (verified-window) | **Mis-tag** | Kernel-certified upper bound at L′ = 2.3 only; others exact-integer Python |
| "The S-local horizon IS q + W0(√q/2)/(2π)" (semilocal) | **Overclaim** | Upper bound on x*; the true excess appears to shrink |
| Range "q up to 1e11 via Platt" (semilocal) | **Corrected** (builder) | q ≤ 5e7 |
| Fourier "positive class" (semilocal) | **Corrected** (builder) | Empty inside the Weil test class; a statement about the symbol only |
| "Universal Y" in the detection law (semilocal) | **Corrected** (builder) | A bracket [Y_1, Y_2] |
| probe_fast.py zero side for x < 4 (semilocal) | **Bug found** (builder) | Under-resolved (0.554 against a true 0.1668); reported onsets came from the direct evaluation and stand |
| "Rigidity + growth: the cap is dVP" (rigidity) | **Overclaim** | Not VK and not better than C loglog t/log t; conditional on Broucke |
| "Each axiom kept exactly while the other fails only beyond any scale" (rigidity) | **False as worded** | The fakes break analytic continuation (poles in the strip) |
| "X5 holds for every L" / "W satisfies X5 iff ζ does" (unified) | **Overclaim** (referee and skeptic) | One-directional transfer from ζ to W |
| "By KP99, surgeries are all the degree-1 Euler fakes" (unified) | **Misquoted citation** | CONJECTURE until the S#_1 multiplicativity step is written |
| "P2 at p² alone kills every off-line surgery" (unified) | **Quadratic surgeries only** | `prime_square_surgery` shows P2 at every prime square is not enough |
| "Ramanujan at p kills on-line surgeries" (unified) | **Mislabel** | The Selberg θ < 1/2 Euler axiom (`surgery_not_selberg`) |
| "Zhu's method provably cannot reach x = 11" (kappa) | **Softened** (F5) | "Zhu's method needs T# > 31535 there" |
| Q = (1/π)∫_0^∞ Ψ|F|² for complex f (kappa) | **Presentational error** | (1/2π)∫_ℝ |

---

## 4. The state of the crux after round 2

### 4.1 What moved and what did not

**What did not move.** Nothing changes on the wall:
- Clause I (Weil/Li/inertia positivity for *all* L) is exactly where round 1 left it.
- Clause II (Λ_dBN ≤ 0) was not touched.
- Clause III (the residual diagonal) was not touched.

**What moved on the HAVE side.**
- Certified exact window positivity went from L0 = 0.8 (x = 4.95) to L0 = 1.199 (x = 11.006). This is Arb-conditional on three paper lemmas.
- Almost-positivity reached L = 2.25, conditional on the zero ladder to 640000.
- Neither advance is structural. Both are blind to the Euler product at the scales they reach: D passes them, and so does every surgery at an unobserved prime. The unified barrier proves that last point in the kernel.

**What moved on the barrier side.** Three kernel-checked no-go results now surround the semi-local and finite-precision approaches.
- **`semilocal_barrier_full`.** Any argument valid on all models of X1 to X6 is fooled by W_{p,c}. Every round-1 barrier is an instance of it.
- **`finite_data_no_zero_free_region`.** Finite coefficient data plus P2 plus an Euler product gives no zero-free region at all.
- **The S-local horizon, modulo `ProbeInput`.** Semi-local positivity has no reservoir beyond window positivity.

Read together, they turn a round-1 heuristic into a kernel statement. **Any RH argument must couple positivity to every prime of ℕ together with the archimedean normalization.** The non-circular forms of that coupling pin the model to ζ (`rh_W_iff`). The circular form, Weil positivity at unbounded support, is RH.

### 4.2 The one convergent finding

Two independent lenses, with different proofs and different islands, found the same thing. On the window, the prime comb acts only through the norm of its compression to L²[−L, L], not through its pointwise supremum:
- verified-window: a Perron weight on cells (`schur_comb`), with a certified constant;
- kappa-certify: a path-graph cosine bound (`comb_bound`), in closed form.

This is the round's only positive methodological result, and it is what produced both records.

**Writer's observation (unrefereed, elementary), which clarifies the objection to verified-window's sharpness claim.** Modulation M_r g = e^{irx}g is unitary on L²[−L, L] and preserves the support. It conjugates the untwisted compressed comb P to the twisted comb P_{−r}. So on *all* of L²[−L, L] the twisted top eigenvalue equals A_win for every r. The quantity that differs between heights is the top value of the twisted comb *restricted to low-frequency tests*, which is what a finite Galerkin basis measures. The circularity referee's twisted scan (2.98 against 3.777 on r ∈ [100, 300], N = 60 to 80 modes) measures exactly this restricted value. That is why reaching A_win at a high-frequency test needs Kronecker alignment. The two numbers do not contradict each other, and the next theorem has to be stated with a bandwidth restriction.

### 4.3 The most promising direction: a height-local comb constant, aimed at the first zero-free window certificate that fails for D

**The precise next theorem** (CONJECTURE until built; the route is a writer's sketch that combines the verified-window circularity referee's salvage with kappa-certify's Lemma B).

Fix L > 0, δ > 0 and L′ = L + δ/2. For a height r and a bandwidth B, define the *band-restricted twisted comb constant*

  A_B(r) := sup { ⟨h, P_r h⟩ / ‖h‖² : h ∈ V_B(L′) },

where:
- P_r = Σ_{log n < 2L} (Λ(n)/√n)(e^{ir log n}τ_{log n} + c.c.), compressed to L²[−L′, L′];
- V_B(L′) is the span of the first N_B ≈ 2L′B/π + O(log) prolate spheroidal functions of the window, i.e. the tests whose spectrum is essentially inside [−B, B].

*Band-split reduction.* Let {χ_j} be a partition of unity on ℝ with χ_j = |ω_j|². Each ω_j is the Fourier transform of a finite measure on [−δ/2, δ/2], concentrated near a band centred at t_j. Then for every f ∈ L²[−L, L]:

  Q(f) ≥ Pole(f) + (1/2π) Σ_j ∫ χ_j |F|² (Ψ_0 − A_B(t_j)) dt − η(L, δ, B)·‖f‖²,

where η is an explicit prolate and Gaussian leakage term of the Lemma B type. The effective threshold becomes

  R_eff = inf { R : Ψ_0(t) ≥ Σ_j χ_j(t) A_B(t_j) + margin for all t ≥ R }.

This is a *finite* computation. Above 2πe^{A_win}, the pointwise envelope already wins. Below it, A_B(r) can be enclosed on a grid in r, because the entries of P_r are Lipschitz in r with constant Σ Λ(n) log n/√n.

*Target instance.* A zero-free certificate of κ_ζ(40) = 0, meaning Q_ζ ≥ 0 on L²[−log 40/2, log 40/2]. It would sit beside the existing certified κ_D(40) ≥ 2 (Arb-certified at the idea stage; reproduced as COMPUTED by the builder), and it would be the first window certificate in this program whose conclusion *fails for Davenport-Heilbronn at the same window*. A cheaper validation run first: exact zero-free positivity at x = 17 (L = 1.4166), where the circularity referee measured an effective threshold of about 80 against the uniform 275.

**Why it is not a relabeling.**
- The target is a statement at one fixed window, and it is strictly weaker than RH, which needs every window.
- Fixed-window positivity demonstrably does not force zeros onto the line. D's window form is PSD for x < 31 although D has off-line zeros, and every surgery at p0 > 40 has a PSD window form at x = 40 (the fooling identity) while having an off-line zero.
- The band constant A_B(r) is a finite-dimensional statement about the phases {r log p mod 2π} for p < 40. It measures quantitatively how badly those phases can align at moderate heights. This is the first place in the program where independence of prime phases would enter *at a finite height and quantitatively*. Round 1 found that it entered only through density statements such as Bohr-Landau.

**Why it survives the negative controls.**
- *The reduction lemma* is a valid inequality for any Dirichlet series with an explicit formula of this shape. For signed coefficients, A_B(r) is computed from the signed comb, and entrywise domination by the untwisted comb fails (D's twisted supremum exceeds its untwisted norm by 46% to 65% at L = 1.717 to 1.84). So the lemma proves only true instances.
- *Davenport-Heilbronn.* D's window form at x = 40 is indefinite, and certified so. The instance **must fail** for D, and the separation fixture checks that it does. This is a positive control, not a death.
- *Epstein and the golden fake.* The golden fake W_{5,5} has p0 = 5 < 40, so its window form at x = 40 is Q_ζ + Z with Z indefinite for x > 5.6. The certificate must fail for it, and the surgery detection law predicts that it will.
- *ζ × a surgered factor at p0 > 40.* The certificate goes through verbatim, and its conclusion is **true** for that function: by the fooling identity its window form is Q_ζ + 2 log p0·Id. By `semilocal_barrier_full`, no fixed-window certificate can do otherwise. This is the honest limit of the direction. It certifies instances, never RH, and it names the reason in the kernel.

**Why it is still worth doing.** It would turn "window certificates cannot see the Euler product" (true at x ≤ 11, by the D margins of 10^23 to 10^40) into the calibrated statement "window certificates see ζ's arithmetic from x ≈ 31 to 40 on, and not before". It also sharpens the detection horizon (round 1's D3; kappa-certify's heuristic horizon of about γ/4) into a certified data point: D's off-line ordinate 85.7 becomes visible at x ≈ 40.

**Feasibility, stated honestly.** kappa-certify's fitted law is −ln λ* ≈ 2π² N(2πx)/ln N, with a ratio of 0.97 at x = 11. This writer's extrapolation of it (unrefereed) gives λ*(40) of order 10^−190. The literature referee's extrapolation to x ≈ 31 gives 10^−150. So a certificate needs arithmetic with at least 250 digits and, even with the band-split threshold, a basis in the thousands. This is not estimated beyond these extrapolations. Whether the band constants lower R_eff enough to make x = 40 feasible is exactly what the x = 17 validation run is for.

### 4.4 Secondary directions, ranked

1. **Restricted-support rigidity** (rigidity-rate builder; CONJECTURE). Let N be a P2 measure system that agrees with ℤ on [1, X) and has counting error at most K x^θ. If ζ_N has a zero at depth η, then log K ≳ X^{1−θ−η}/log X.
   - This is a P2 uncertainty principle for Dirichlet integrals supported on [X, ∞).
   - It competes with the lens's own dVP-cap conjecture, and the evidence favours it.
   - It is new mathematics about how positivity propagates. It is not RH-equivalent, since it concerns near-ζ Beurling systems.
   - Negative controls: D and Epstein lack P2, and surgered fakes violate P2 at p² or change the counting.
   - It bears on rates, not on the wall.
2. **Certified detection horizon** (kappa-certify circularity referee, and round 1's D3). A theorem that a window of size x cannot detect an off-line zero with γ > c·x, built on the elementary identity ∫F(t − id) conj F(t + id)ρ = ∫∫ f(u) conj f(v) e^{d(u−v)} ρ̂(u − v) (THEOREM-paper-proof, kappa-certify statement (iii)). It is a no-go that would make "instances certify instances" a theorem for κ-certificates.
3. **Generalize the unified-barrier killers** to arbitrary local polynomials. Prove that P2 at *all* powers of p forces every root onto |α| = √p (a Kronecker limsup), and write the S#_1 multiplicativity step that KP99 does not supply. This is ledger hygiene, and the kernel cost is small.
4. **The operator-norm near-radical lemma** (round 1's D2), now with an explicit probe: the semilocal Φ′·1_W and its Q-size bound. What remains is the step from a form bound to an operator bound, plus the spectral projection.

---

## 5. Proposed draft registry nodes

*The lead authors registry nodes; these are drafts. The preconditions are those of round 1, section 6.0:*
1. commit the five Lean files and five research directories, which are all untracked on `cl/crux2`;
2. wire them into lakefiles and AxiomGuard, adding `build_deps.sh` or `lean_lib` targets for unified-barrier's round-1 imports;
3. do a blind read-back;
4. compose the islands (rvm_bridge v4.33.0-rc2, li_positivity v4.34.0-rc1) only at registry level.

*The title of every node must carry "NOT RH". Lean names are copied from the artifacts. None of the nodes has been re-elaborated as a standalone statement module.*

### 5.1 Mirrormere (clause I: window and Weil coordinates)

- **`MM_window_comb_form_constant`** (lemma; rvm_bridge). *"Form-level prime-comb bound on a fixed window: a positive Schur weight bounds ‖primeSide(g⋆g̃)‖ uniformly over frequency twists; Λ ≥ 0 enters only through entrywise domination. Not RH."* Artifact: `Crux2VerifiedWindow.schur_comb`, `primeSide_autocorr_le`, `primeSide_autocorr_twist_le`.
- **`MM_window_comb_cert_L23`** (instance; rvm_bridge). *"Kernel-certified comb constant 11.161373 on [−2.3, 2.3], under one third of the pointwise mass. Not RH."* Artifact: `primeSide_autocorr_le_cert`, `combMass_gt_three_lam`, `weilForm_autocorr_ge_cert`.

  ```lean
  theorem primeSide_autocorr_le_cert {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
      (hgW : ∀ x, x ∉ Set.Icc (-(23 / 10 : ℝ)) (23 / 10 : ℝ) → g x = 0) :
      ‖primeSide (autocorr g)‖ ≤ ((11161373010 : ℝ) / 1000000000) * ∫ x, ‖g x‖ ^ 2
  ```
- **`MM_verified_window_glue`** (lemma, conditional; rvm_bridge). *"Verified zeros to height T plus the form-level constant give ALMOST-positivity Re W(g⋆g̃) ≥ −(E1+E2); analytic inputs E1, E2 and the contraction are hypotheses. Almost-positivity is not positivity. Not RH."* Artifact: `weil_almost_pos_of_glue`, `weil_almost_pos_cert`.
- **`MM_window_comb_pathgraph`** (lemma; li_positivity). *"Window-compressed comb bound Σ c_n cos(π/(⌊2A/log n⌋+2)) for measurable real tests on [−A, A] (Lemma A, continuous form). Holds with |c_n| for signed coefficients. Not RH."* Artifact: `Crux2KappaCertify.LemmaA.comb_bound`, `prime_comb_bound`, `shift_bound_signed`.
- **`MM_kappa_window_cores_x11`** (instance; li_positivity). *"Schur link and exact LDLᵀ cores for κ_ζ(x)=0 at x = 6.996 and 11.006; the Arb facts (C − λ0 I > 0, Schur box) are hypotheses; the reduction Q ≥ R″ and the explicit formula on the form domain are paper-level. Holds verbatim for D. Not RH."* Artifact: `schur_link`, `Core_x6996_{even,odd}.core_schur`, `Core_x11006_{even,odd}.core_schur`.
- **`MM_semilocal_relabeling`** (lemma; rvm_bridge). The title must carry *"RELABELING of Weil's criterion"*. Artifact: `Crux2SemilocalArchimedean.rh_iff_semilocal_natural_windows`.

### 5.2 Barrier and negative-control nodes

- **`RH_barrier_semilocal_W`** (lemma; li_positivity). *"For every finite S, N0, L0 there is an Euler product W_{p,c} = ζ(1 + c p^{−s} + p^{1−2s}) with p ∉ S, p² > N0, log p > L0, satisfying the semi-local axioms (X5 only as the surgery-side lattice sum; the ζ-to-W transfer is paper-level and one-directional) and vanishing off the line in the strip. Not RH."* Artifact: `Crux2UnifiedBarrier.semilocal_barrier_full`.

  ```lean
  theorem semilocal_barrier_full (N0 : ℕ) (S : Finset ℕ) (L0 : ℝ) :
      ∃ p c : ℕ, p.Prime ∧ p ∉ S ∧ N0 < p ^ 2 ∧ L0 < Real.log p ∧ 4 * p < c ^ 2 ∧ c < p + 1 ∧ ...
        ∧ (∃ s : ℂ, LiCriterion.riemannXi s * surg p c s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1)
  ```
- **`RH_classP_sharp_at_P2`** (`classP_sharp`), **`RH_golden_is_W55`** (`golden_unified_full`), **`RH_negctl_W41_box1_nonrelativizing`** (`lowHeightBox_nonrelativizing`). These are internal unification nodes and must be titled as such.
- **`MM_channel_is_trivial_bound`** (lemma; li_positivity). *"Build C's channel axioms and the dVP defect-summability both hold for ξ·surg iff |c| < p+1 (the local trivial bound), never seeing the Hasse bound. Not RH."* Artifact: `channelAxioms_W_iff`, `robust_positivity_iff`.
- **`RH_surgery_support_prime_duality`** (`surg_explicit_formula`), **`RH_prime_square_surgery`** (`prime_square_surgery`), **`RH_surgery_not_selberg`** (`surgery_not_selberg`).
- **`RH_barrier_pole_shadow_no_zero_free_region`** (lemma; li_positivity). *"For every X > 1, δ > 0, t ≠ 0 some multiplicative P2 Euler product agrees with ζ's coefficients below X and vanishes at 1 − δ + it; the object has poles in the strip (not an entire L-function). Not RH."* Artifact: `Crux2RigidityRate.finite_data_no_zero_free_region`, `mty_fake`, `poleShadow_simple_zero`.
- **`RH_window_defect_identities`** (lemma; li_positivity). *"Quantitative Hamburger identities: triangle defect equals sinc²-weighted non-integrality; modulated triangle reads off multiplicities (finite atomic measures). Classical in substance."* Artifact: `window_defect_identity`, `triPairHat_mod_int`.
- **`RH_barrier_semilocal_horizon`** (lemma, conditional; rvm_bridge). *"`ProbeInput q x` ⇒ the S_q-local Weil form is indefinite on every window ≥ log x. `ProbeInput` is a named, unproved obligation (Φ̂ = Ξ, Φ′ < 0, zero-tail). Not RH."* Artifact: `horizon_of_probeInput`, `sLocal_neg_of_probe`. A companion stated-only target node, **`RH_probeInput_onset`**, would carry the obligation.
- **`RH_surgery_local_weil_iff_hasse`** (lemma; rvm_bridge). Artifact: `latticeForm_nonneg_iff`, `surgery_local_rh_iff`, `pair_probe_surgery_value`.

### 5.3 Stated-only targets (CONJECTURE; no proof exists)

- **`RH_restricted_support_rigidity`**: the P2 uncertainty principle of section 4.4, item 1, with `expulsion_of_transfer_bound` as its kernel core.
- **`MM_band_comb_reduction`**: the band-split reduction of section 4.3.
- **`MM_negctl_dh_window_indefinite_x40`**: κ_D(40) ≥ 2 as a kernel instance. The Arb data exists as `sep_x40_N60.json`, but it has not been emitted to Lean.

---

## 6. What was not checked

- **The Python and Arb numerics were not re-run by this writer.** Skeptics re-ran them, with these exceptions:
  - kappa-certify's one-hour `certify_wa` builds and `quad_opt2` were not re-executed. The x = 11 certificate depends on the refined quadrature bound, 1.48e−55; the crude bound is 2.9e−43.
  - The idea-stage onsets in semilocal were not re-run by its builder: the pole-free probe, the precision barrier, and the golden and W1 onsets.
  - verified-window's Galerkin lower value 11.0586 is not in the shipped outputs. The shipped value is 11.05626 at N = 200.
  - The minimality claim for the verified-window N = 460 certificate is not in any artifact.
- **Paper lemmas that nothing in this round has kernel-checked:**
  - the explicit formula on the full form domain of L²[−a, a] (kappa P1);
  - the Binet envelope (P2);
  - Lemma B and the whole reduction Q ≥ R″ (P3);
  - `ProbeInput`;
  - the three analytic inputs to `weil_almost_pos_cert`;
  - the ζ-to-W transfer in X5;
  - the rescaling, grafting and transfer lemmas.
- **The zero ladder is on a different island.** `AllZeros_h640000` is Arb-conditional on 640 band hypotheses, lives on another island, and was not imported by verified-window. The −10^−997 figure is therefore COMPUTED relative to it.
- **Novelty is only partly verified.** Several referees had exhausted their web-search budget. Two external facts were verified directly:
  - Zhu's 4.95 record, by the kappa literature referee fetching arXiv:2608.24827v2;
  - Broucke's Thm 1.6, by the rigidity builder reading the PDF.
  
  These were not checked against the literature:
  - Connes-Consani-Moscovici and Connes-van Suijlekom, for the semilocal horizon and the archimedean value 3.27;
  - Bombieri's remarks on Weil's functional, for the compressed comb;
  - the Selberg-class literature on surgeries;
  - the S#_1 multiplicativity step behind KP99.
- **Cross-lens numbers were not reconciled.** verified-window's A_win(L; L′) and kappa-certify's ‖P_A‖, A′(A) and Fejér mass use different window and comb-range conventions. For example, kappa reports 4.890 at x = 16.4, while verified-window reports [3.786, 3.947] at L = 1.4166, i.e. x ≈ 17. This writer did not determine whether the gap is a convention difference or a real disagreement. It must be settled before either constant feeds the other's pipeline.
- **The writer's modulation observation in section 4.2** is elementary but unrefereed. The band-split reduction in section 4.3 is a sketch, and its leakage term η has not been written down.
- **The feasibility of the x = 40 target** is estimated only by extrapolating a fitted law.
- **Fixture status.** The D-vs-ζ separation at x = 40 is Arb-certified at the idea stage (`sep_x40_N60.json`) and only COMPUTED in the builder's re-check. It is not in the kernel and not in CI.
- **Artifacts.** Three semilocal numerics JSONs were overwritten by the skeptic's re-run; the regenerated values match every quoted figure. Nothing from round 2 is committed. The 450 MB kappa matrices stay in the lens scratch directory, `/private/tmp/claude-0/crux2/kappa-certify`.
- **Independence.** Everything was done by subagents of one session, so independence is self-attested.

`conjecture1_proved = False`.
