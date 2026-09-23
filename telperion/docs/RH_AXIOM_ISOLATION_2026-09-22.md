# RH axiom isolation: class P (degree-1 functional equation plus positive von Mangoldt coefficients)

*Workflow `rh-axiom-isolation`, run `wf_5863fa13-b6d`. Four attack seats (construct, theorem, literature, barrier), three hostile referees per seat (correctness, relabeling, novelty), kernel builds for the three top-ranked seats, a skeptic on each build, then this synthesis. The run launched 2026-09-22 and was relaunched after a usage-limit stop. This memo was written 2026-09-23 on branch `cl/crux` of the `arda-cl-crux` worktree (HEAD `3b5bcccd5`).*

*`conjecture1_proved = False`. Nothing in this memo bears on where the zeros of the Riemann zeta function lie. RH is not advanced by anything below. The main finding is that the question this run was asked turns out to be RH itself.*

---

## 0. Preamble

### 0.1 The answer in one paragraph

The run asked whether the joint cell "degree-1 functional equation (P1) plus nonnegative von Mangoldt coefficients (P2)", with or without an Euler product (P3), forces RH. The cell turned out to be a single point.

- **Integer frequencies.** P1 plus P2 forces F = ζ. Multiplicativity is never used; it follows from the other two axioms.
  - The literal zeta-shape case is Hamburger's theorem of 1921.
  - The twisted case (any conductor, any gamma shift with Re μ ≥ 0, pole only at s = 1) was proved on paper by four distinct routes: three go through the Kaczorowski-Perelli periodicity theorem, and one avoids it.
  - The combinatorial core of the twisted case, `classP_eq_zeta`, is now kernel-checked. Its two external inputs enter as named hypotheses.
- **Beurling-type generalized integers with ζ's exact conductor-1 FE.** Positivity of the counting measure alone again forces ζ. There are three independent paper proofs.
- **Consequence.** "Every F in class P satisfies RH" is exactly RH. It is not GRH, because P2 excludes L(s, χ) and ζ(s + iθ).

What adding P1 to positivity buys is uniqueness, not a proof mechanism. The zero-free region provable from P1 + P2 alone is de la Vallée Poussin's. The FE sharpens its constants, not its rate.

Kernel-checked near-misses certify what each axiom is doing:

- **Drop P2.** Keep the FE, an Euler product and a_n ≥ 0. There are then exact zeros at Re s = 1.7716 > 1, on Re s = 1, and at Re s = 0.5612. The last of these comes from the barrier seat's core, which is kernel-checked but was never attacked by a skeptic.
- **Drop the pole normalization and integer frequencies.** Keep P2 (in Beurling form), one gamma factor, a weighted Euler product and an exact FE. Then every zero is off the line, unconditionally.

One cell is unresolved: the Beurling relaxation with a twisted FE (conductor q > 1). It is conjectured to be empty.

### 0.2 Tags

Every claim below carries one tag:

- **THEOREM-kernel-checked.** Proved in the Lean kernel, with `#print axioms` at most `[propext, Classical.choice, Quot.sound]`. The artifact and its sha256 are pinned.
- **THEOREM-paper-proof.** A written proof that survived a hostile correctness referee.
- **CONJECTURE-with-evidence.**
- **HEURISTIC.**

Two further trust classes are named explicitly and never merged with the kernel. **Arb-certified** means rigorous interval arithmetic outside the kernel. **float64 evidence** means neither kernel nor interval. "Only claims that survive count": a claim that no referee saw is listed as unrefereed and is not counted as proved, even when it looks right.

### 0.3 Provenance, and what this writer re-checked

1. **The synthesis payload was truncated.** The relayed data was cut at 120,000 characters, in the middle of the barrier seat's claim 7. All build and skeptic records were missing. The full record was recovered from the workflow journal, `~/.claude/projects/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/subagents/workflows/wf_5863fa13-b6d/journal.jsonl`. It has 51 entries: 4 attack results, 12 referee verdicts, 3 builds and 3 skeptic verdicts. Every verdict quoted below comes from that journal.
2. **Referees saw truncated results.** Each referee received only the first 14,000 characters of the seat's result. Some claims were therefore never refereed. They are listed in §4.3 and §6.
3. **Build selection mixed score scales.** The builds went to the three seats with the highest mean referee score, but the referees scored on two different scales, 0-10 and 0-100. The means were literature 29.3, theorem 28.0, construct 6.0 and barrier 5.3. So the barrier seat was never built, and no skeptic attacked its kernel core, although its novelty referee judged its Collapse B the most valuable single statement of the run.
4. **Writer re-checks, 2026-09-23.**
   - **Lean re-run.** Byte-identical snapshots of all four Lean files were re-elaborated under the lean-slot lock. All exited 0, and the axiom transcripts match the recorded ones line for line.
   - **Restatements.** Thirteen restatements in Mathlib-only vocabulary were appended to the snapshots and proved from the artifacts. This guards against rigged definitions and namespace shadowing.
   - **Numerics.** Every numerics script except the integer-frequency stress test (which the literature skeptic ran) was re-run from a scratch copy, so the committed outputs were not touched.
   - **One false numerical claim.** The barrier seat's cited numerical confirmation of the Fejér normalization is false as stated (§3.4, item 2). The identity itself is true.
   - **Statement texts.** All draft registry statement texts in §5 were typechecked, and five of them were proved from the artifacts.

---

## 1. The class-P question, precisely

### 1.1 As posed

The run's question, verbatim from the workflow script:

> THE QUESTION (class P): let F(s) = sum a_n n^{-s} (a_1 = 1) be a Dirichlet series with (P1) a degree-1 functional equation of the zeta shape: xi_F(s) := s(s-1) pi^{-s/2} Gamma(s/2) F(s) (or Q^s-twisted with one Gamma(s/2 + mu) factor) is entire of order 1 and xi_F(s) = epsilon * conj(xi_F(1 - conj s)) with |epsilon| = 1; (P2) POSITIVITY: -F'/F(s) = sum Lambda_F(n) n^{-s} with Lambda_F(n) >= 0 for all n (the axiom the classical 3-4-1 zero-free proof uses; Davenport-Heilbronn and Epstein lack it); (P3) F has an Euler product OR is at least allowed to be a Beurling-type generalized zeta exp(sum over a positive measure). Does every F in class P satisfy RH? [...] Decide what adding (P1) to positivity buys, with and without full multiplicativity.

The theorem seat was additionally asked for three things: (a) a zero-free region from P1 + P2 alone, and whether P1 improves the rate; (b) an RvM-type count valid on the class; (c) rigidity.

### 1.2 Precise form

**Data.** A sequence a: ℕ → ℂ with a_1 = 1 whose series F(s) = Σ a_n n^{-s} converges absolutely in some right half-plane.

**(P1) Functional equation.** There are Q > 0, μ ∈ ℂ with Re μ ≥ 0, and ε with |ε| = 1 such that

    ξ_F(s) := s(s-1) Q^s Γ(s/2 + μ) F(s)

extends to an entire function of order 1 and satisfies ξ_F(s) = ε·conj(ξ_F(1 - conj s)). The conductor is q := πQ². There are three normalizations:

- **Literal zeta shape:** Q = π^{-1/2} and μ = 0, so q = 1.
- **Selberg normalization:** additionally, F has no pole except at s = 1. This is automatic when μ = 0. It is a genuine restriction when μ ∉ -ℕ₀, because Γ(s/2 + μ) is then regular at s = 0, and "ξ_F entire" by itself allows F a simple pole at s = 0.
- **Literal twisted:** the s(s-1) factor is exactly as written, so F may have simple poles at both s = 0 and s = 1.

**(P2) Log-positivity.** -F'/F(s) = Σ_{n≥2} Λ_F(n) n^{-s} with Λ_F(n) ≥ 0 for every n. Equivalently, F = exp(Σ b_n n^{-s}) as formal Dirichlet series, with b_n = Λ_F(n)/log n ≥ 0.

**(P3) Multiplicativity, optional.** Either a_n is multiplicative (an Euler product), or the Beurling relaxation holds: F(s) = ∫_{[1,∞)} x^{-s} dN(x) with N = exp*(Π) for a positive measure Π on (1, ∞). In the Beurling reading P2 is automatic, and positivity of N is weaker than P2.

**The readings, and where each one stands after this run:**

| Reading | Frequencies | P1 normalization | Status (details in §4) |
|---|---|---|---|
| R1 | integers | literal zeta shape | {ζ}. Hamburger 1921; P2 only supplies absolute convergence |
| R2 | integers | twisted, Selberg normalization, Re μ ≥ 0 | {ζ}. THEOREM-paper-proof, four routes; coefficient core kernel-checked |
| R2' | integers | literal twisted (pole at 0 allowed) | μ must be real (paper). μ = 0 is R2; μ = 1/2 is excluded (paper). Real μ > 0, μ ≠ 1/2 is **open** |
| R3 | Beurling, ≥ 1 | literal zeta shape (q = 1) | {ζ}. THEOREM-paper-proof, three routes; positivity of N alone suffices |
| R4 | Beurling, ≥ 1 | twisted, q ≠ 1 | q < 1 impossible, and ε = -1 needs q ≥ 2π/3 (paper). q > 1 is **open**; conjectured empty |

### 1.3 Why this question separates FE, positivity and multiplicativity

The three axioms do different jobs in the classical theory.

- **P2 is the only input of the 3-4-1 zero-free argument.** This covers de la Vallée Poussin, Stechkin, Kadiri and Mossinghoff-Trudgian.
- **P2 plus P3 without P1 describes Beurling systems.** For these, Diamond-Montgomery-Vorhauer (Math. Ann. 334, 2006) show that the de la Vallée Poussin region is the ceiling, and RH can fail.
- **P1 alone allows zeros off the line.** Davenport-Heilbronn is the standard example, with zeros even in σ > 1.
- **The Selberg class (P1 + P3 + Ramanujan) is conjectured to satisfy RH.**

Class P is exactly the cell P1 ∧ P2, with P3 optional. It is the cell the partly retracted 2026-09-18 memo `RH_BARRIER_FE_UNIFORMITY_DESIGN_2026-09-18.md` (§3) pointed at: "the Euler product alone caps at de la Vallee-Poussin, the functional equation alone decides nothing; any proof must use both, jointly and inseparably."

That made the question worth asking, in two directions:

- **A negative control stronger than Davenport-Heilbronn.** Suppose the cell contained a member other than ζ with an off-line zero. That member would satisfy every input of every positivity proof and the exact FE, so it would be a sharper negative control than Davenport-Heilbronn.
- **A proof strategy.** Suppose instead that every member provably satisfied RH, by an argument using only P1 + P2. That argument would be a proof strategy.

The run shows that neither happens at degree 1: the cell is {ζ}. The table below records every axiom cell the run touched.

| Axioms kept | Representative | Off-line zeros? | Trust |
|---|---|---|---|
| P1 only (degree 1, integer frequencies) | Davenport-Heilbronn; the q = 5 mixture a·ζ(s)(1+√5·5^{-s}) + b·L(s, χ₅) | yes | Arb-certified (`QC_DH_SCOUT.md` §4, re-certified in §3.4; mixture zeros at height about 61) |
| P1 + P3 + a_n ≥ 0 | ζ(s)(1+4·2^{-s}+2·4^{-s}); F0 = ζ(s)(1+2^{-s})(1+2^{1-s}); W1 = ζ(s)(1+11·29^{-s}+29·29^{-2s}) | yes: Re s = 1.7716, Re s = 1, Re s = 0.5612 | THEOREM-kernel-checked |
| P1 + P3 + P2 for n < N0 only | W1 family with p² > N0 | yes | kernel-checked at (29,11), where N0 = 841; paper for the family |
| P1 + P2, integer frequencies (R1, R2) | ζ only | RH itself | THEOREM-paper-proof; coefficient core kernel-checked |
| P1 + P2 + P3 | ζ only | RH itself | follows from R2. Under Selberg's axioms it is also classical: the Kaczorowski-Perelli S_1 classification plus one line |
| P2 + P3, no P1 (Beurling) | Diamond-Montgomery-Vorhauer systems | yes, near σ = 1 | literature; primary source not re-read |
| P2 + one gamma factor + exact FE + weighted Euler product, pole at 1/2 and frequencies √n | F1 = ζ(s/2+3/4)ζ(s/2-1/4); the E8 twin | every zero is off the line | THEOREM-kernel-checked (F1 unconditionally) |
| P1 at q = 1 + N ≥ 0, Beurling frequencies ≥ 1 (R3) | ζ only | RH itself | THEOREM-paper-proof |
| the same, with frequencies below 1 allowed | Ftwin = ζ(s)(p^{s-1/2} + c p^{-1/2} + p^{1/2-s}) | yes | FE kernel-checked; positivity of its measure is paper |
| P1 twisted (q > 1) + P2, Beurling (R4) | none known | unknown | OPEN; conjectured empty |

---

## 2. The four seats

Referee scores are shown as returned. The two scores of 78 are on a 0-100 scale; every other score is on 0-10. A seat survives with fewer than 2 kills out of 3.

| Seat | Correctness | Relabeling | Novelty | Kills | Workflow mean | Built |
|---|---|---|---|---|---|---|
| construct | 8, no kill | 4, no kill | 6, no kill | 0/3 | 6.0 | yes |
| theorem | 78, no kill | 3, **KILL** | 3, no kill | 1/3 | 28.0 | yes |
| literature | 78, no kill | 6, **KILL** | 4, no kill | 1/3 | 29.3 | yes |
| barrier | 7, no kill | 4, no kill | 5, no kill | 0/3 | 5.3 | **no** (ranked fourth) |

### 2.1 Construct seat

**Result.** *"Class P, constructor seat: every counterexample route is blocked. Class P collapses to {zeta}, and sharp near-misses show that P2 and the pole normalization in P1 are the axioms doing the work."* The seat tried to build a member of class P with an off-line zero and could not. It proved that the routes it tried are closed, and it produced two sharp near-misses.

| # | Claim | Submitted | After review |
|---|---|---|---|
| 1 | Positivity lemma: P2 gives a_n ≥ 0, a zero-free σ > 1, a pole at 1, and F not entire | paper | arithmetic half **kernel-checked**; Landau half paper |
| 2 | Theorem A (Beurling-Hamburger): N ≥ 0 on [1,∞), N({1}) = 1 and ζ's FE give N = Σ δ_n. Proof via the 1D Cohn-Elkies function sin²(πx)/(π²x²(1-x²)) | paper | paper, survives. Step 3 kernel-checked, conditional on the Step-2 pairing identity. Novelty unverified |
| 3 | Conductor bound: q ≥ 1, and q = 1 only for ζ | paper | paper, survives |
| 4 | Theorem B: twisted P1 + P2, integer frequencies, Selberg normalization give ζ (via Kaczorowski-Perelli 1999 and Saias-Weingartner 2009 plus Lemma C) | paper | paper, survives with a fix; a routine citation chain |
| 5 | Lemma C: a self-reciprocal Dirichlet-polynomial twist ζ·P satisfies P2 only if P = 1 | paper | paper, survives; **kernel-checked for q = p and q = p²**, every prime p |
| 6 | Prop D: there is no positive super-system ζ·G with G ≠ 1 | paper | paper, survives with a fix |
| 7 | Near-miss 1: F0 = ζ(s)(1+2^{-s})(1+2^{1-s}) | paper + float | **kernel-checked**, except finite order |
| 8 | Near-miss 2: F1 = ζ(s/2+3/4)ζ(s/2-1/4), and the E8 twin | paper + float | **kernel-checked**, including unconditional off-line zeros; wording corrected |
| 9 | Lattice and number-field rescaling puts the pole at (d+1)/2 | paper | algebra kernel-checked; formula scoped to the Dedekind-type normalization |
| 10 | Moving zeros, signed Beurling measures; DMV systems cannot satisfy ζ's FE | paper | **unrefereed** (truncated). The DMV consequence survives through barrier claim 2 |
| 11 | Twisted Beurling conjecture | conjecture | **unrefereed** (truncated) |

**Referees.**

- **Correctness (8, no kill).**
  - All THEOREM claims were checked line by line, and the numerics were recomputed at 35 digits. For F0, F1 and E8 the functional-equation residual is 1e-35 with the right ε, and 2.0 with the wrong one.
  - Decisive objections:
    - (i) The title overclaims. Two corners are open, and FE plus N ≥ 0 examples exist for every real q > 1: ζ(s)(1 + √λ·λ^{-s}) fails only P2.
    - (ii) "The only axiom it breaks" is false for F1. F1 also uses frequencies √n (Beurling primes √p), μ = 3/4, and q = 1/2 < 1.
    - (iii) Prop D's step "G of order ≤ 1" is unjustified. It is also unneeded: finite order makes g a polynomial.
    - (iv) Theorem B's principal-character step is garbled. The correct reason is that for non-principal χ, P·L(s, χ) is entire, which contradicts the pole at 1.
    - (v) The lattice formula matches the Dedekind normalization, not the Epstein normalization the seat actually used.
- **Relabeling (4, no kill).** The seat's own conclusion makes "RH for class P" identical to RH, so it gives zero leverage. Theorem B is mostly a citation chain. Theorem A's novelty needs checking against Bochner 1951, Chandrasekharan-Mandelbrojt 1957, Córdoba 1989 and Lev-Olevskii 2015.
- **Novelty (6, no kill).** Theorem A was not found in the literature, but it sits in a crowded neighbourhood:
  - Beurling, Ark. Mat. 1 (1951): unit coefficients, no FE, and the class D_1 = {ζ, (2^s - 1)ζ}.
  - Kahane-Mandelbrojt 1958: discrete support and spectrum, with density hypotheses.
  - Dixit, JNT 206 (2020): positive coefficients and growth in place of an FE; at most 2d functions.
  - Knopp 1994.

  The referee also found that F1 is a weighted Euler product, not a Beurling zeta, and that the near-misses are textbook constructions.

**Salvage.**

- **Keep as a short note, tagged THEOREM-paper-proof:** Theorem A (strengthened: the support conclusion does not need N({1}) = 1), the conductor bound, Lemma C and Prop D (with the fixes).
- **Keep as illustrations only, never as evidence about ζ:** the near-misses. They serve as a map of which axiom does the work.
- **Retire class P as an RH attack vector, and record it as a no-go.**

### 2.2 Theorem seat

**Result.** *"Class P is the one-element set {zeta}: the FE plus log-positivity forces F = zeta, with or without multiplicativity. The Beurling version is also {zeta} at conductor q = 1."* The seat also gives an explicit de la Vallée Poussin region and an RvM formula for every F satisfying P1 + P2.

| # | Claim | Submitted | After review |
|---|---|---|---|
| C1 | Normal form: a_n ≥ 0, σ_a = σ_c = 1, pole at 1, F ≠ 0 on σ ≥ 1, μ = 0, ε = ±1 | paper | paper, survives. The simple-pole step must come first; C1(i) is **kernel-checked** |
| C2 | Literal normalization gives ζ (Hamburger 1921) | classical | classical |
| C3 | Twisted, any Q and μ, no multiplicativity: F = ζ | paper, with KP99 as input | paper, survives. **Kernel-checked at the coefficient level** (`classP_eq_zeta`). Novelty: a corollary of KP99 + SW09 plus one new lemma |
| C4 | "Class-P RH" is RH, not GRH | paper | survives; this is the relabeling |
| C5 | Beurling: q ≥ 1, equality only for ζ (Fejér kernel); ε = -1 needs q ≥ 2π/3 (Hermite h4 - (12+δ)h0) | paper | paper, survives. The growth hypotheses must be written out; the ε = -1 bound is not sharp |
| C6 | Explicit region σ > 1 - (7-4√3)/((5/2)log(\|t\|+1) + 4 log q + 2.44) | paper | paper, survives; final algebra **kernel-checked**. No content for integer members |
| C7 | P1 improves the rate only through rigidity | mixed | (a) is an identity; (b) follows from C3 + Ford 2002; the meta-claim is **HEURISTIC** |
| C8 | RvM with conductor: N_F(T) = (T/2π) log(qT/(2πe)) + 7/8 + S_F(T) + O(1/T) | paper | paper, survives. The sentence "P1+P2 give no density result beyond this" is **HEURISTIC** |
| C9 | Negative controls (q = 4 control; conductor-5 KP element; E8) | theorem + numerics | partially refereed (truncated). The builds kernel-check (i) and the coefficient in (ii) |
| C10 | The Beurling class P has nothing with q > 1 | conjecture | **unrefereed** (truncated) |

**Referees.**

- **Correctness (78/100, no kill).** No counterexample and no fatal gap. Independent recomputation gave:
  - the C6 constant 2.430257, with δ* = 2√3 - 3 and c* = 7 - 4√3;
  - the Hermite threshold √(3/(2π)) = 0.690988;
  - the asymptotic constant 34.8205, so the stated 34.83 is a conservative round-up.

  Gaps:
  - (i) C1(iii) uses a simple pole before simplicity is proved. The fix: Γ(s/2) has a simple pole at 0, so m = 1.
  - (ii) The density sentence in C8 is mis-tagged.
  - (iii) Quote the exact KP99 statement.
- **Relabeling (KILL, 3).** At the literal normalization the headline is Hamburger's theorem. With multiplicativity it is the S_1 classification plus one line. The only pieces beyond the known are C3 (arbitrary Q, no multiplicativity, resting on KP99) and C5. C3 Step 4 skips an application of Landau. C6 and C8 say nothing new for integer members, since F = ζ.
- **Novelty (3, no kill).** C2 is Hamburger; Perelli's survey (arXiv:1605.02354) records the degree-1, conductor-1 case. C3:
  - With multiplicativity, it is immediate from KP99.
  - Without multiplicativity, it is KP99 plus Saias-Weingartner (Acta Arith. 140, 2009) plus Step 4. Steps 1-2 re-derive Saias-Weingartner by hand, uncited.
  - Only Step 4 is new, "a roughly 10-line lemma" that is correct.

  C5's step "FE if and only if ν̂ = εν" needs Kahane-Mandelbrojt/Bochner growth hypotheses. C6 and C8 are Iwaniec-Kowalski chapter 5 with constants that are not competitive.

**Salvage.** Keep three things as a short internal note, correctly attributed:

- (A) the Step-4 lemma, with the reduction chain KP99, then SW09, then Step 4;
- (B) the Beurling corollary C5(i), framed as a partial answer to Hilberdink-Lapidus 2006;
- (C) C4 as the ledger finding: the class-P lane is closed.

### 2.3 Literature seat

**Result.** *"RH for class P (degree-1 FE + positive Λ_F). With integer frequencies class P is just {zeta}; the Beurling version is open."*

| # | Claim | Submitted | After review |
|---|---|---|---|
| 1 | Hamburger: literal P1 with integer frequencies gives c·ζ | classical | classical |
| 2 | NEW: F in S#_1 with a(1) = 1 and Λ_F ≥ 0 gives F = ζ (mixture-of-Euler-products lemma: cumulants, Pringsheim, Pólya-Ritt, Landau) | paper sketch | paper sketch, survives with fixes. θ = 0 is **kernel-checked** |
| 3 | With the Selberg axioms: S_1 = {ζ, L(s+iθ, χ)}, and P2 picks ζ | classical | classical |
| 4 | Negative controls: q = 4 Euler-product control; DH-type q = 5 mixture | theorem + numerics | **kernel-checked**, with corrections (§3.4) |
| 5 | Beurling reduction: FE if and only if a self-dual positive crystalline measure; ε = +1 forced at q = 1 (Hermite); c_0 formula | paper sketch | survives; the theta identity is Arb-enclosed |
| 6 | Uniformly discrete g-integers give ζ (Lev-Olevskii 2015) | paper sketch | survives with the pigeonhole fix; partly covered by Beurling 1951 |
| 7 | Kahane-Mandelbrojt finite basis: an order in a real number field | conditional on H_0 | conditional; the K = Q branch is kernel-checked |
| 8 | E8 normalization witness | theorem + numerics | **kernel-checked**; wording corrected |
| 9 | Positivity without FE caps at de la Vallée Poussin | paper + HEURISTIC | standard; the "needs arithmetic" part is HEURISTIC |
| 10 | A Beurling class-P RH counterexample is a Hilberdink [α,0]-system with α > 1/2 | paper reduction | the exponents are cited literature facts, not re-derived |
| 11 | Novelty: RH for Beurling zetas with a zeta-type FE is not treated in the literature | conjecture | **refuted as written**: Beurling 1951 and Dixit 2020 were missed |

**Referees.**

- **Correctness (78/100, no kill).** Every number reproduces at 40 digits. Defects:
  - D1: the cumulant formulas need a (a+b)^3 normalization, and κ₃ > 0 when b < 0.
  - D2: E8 is excluded "only because of its pole" only in the free-(Q, μ) frame.
  - D3: step (3) needs a vector y, not a scalar y₀.
  - D4: step (4) must come after the KP structure theorem.
  - D5: an unnecessary density sentence.
  - D6: use Saias-Weingartner in place of the Bohr sketch.
  - D7: the exponents in claim 10 are cited, not checked.
- **Relabeling (KILL, 6).** The class-P RH route is a relabeling. Claim 2 survives only as a modest standalone lemma. The Beurling relaxation is no escape: RH for Beurling class P implies RH, because the class contains ζ.
- **Novelty (4, no kill).** The headline is classical. The literature-absence claim is false as written: Beurling 1951 settles the unit-mass case of the Beurling relaxation, and Dixit 2020 is a published finiteness result in the positive-coefficient Beurling setting. No prior statement of claim 2 was found. Its step (3) is only sketched.

**Salvage.** Record the no-go: integer-frequency class P = {ζ}, so RH for class P is the same statement as RH. Keep claim 2 as a modest lemma once step (3) is written out, and keep the three negative controls. Rescope claims 5, 6, 7 and 10 against Beurling 1951 and Dixit 2020.

### 2.4 Barrier seat

**Result.** *"Class P is exactly {zeta}; the strongest honest barrier is a sharp one-prime-surgery sandwich, with a kernel-checked finite core."*

| # | Claim | Submitted | After review |
|---|---|---|---|
| 1 | Collapse A: integer frequencies, any conductor, μ ∈ {0, 1/2}, Λ_F ≥ 0 for all but finitely many n, gives ζ. KP-free: Poisson periodicity, cumulants along progressions, Bohr, power sums | paper | paper, survives with the Hadamard fix in Step 2. **Corollary (c) is false as stated** (§3.4) |
| 2 | Collapse B: positive N on [1,∞) with the gap N([0,1)) = 0 and ζ's conductor-1 FE gives N = Σ δ_n (triangle LP for ε = +1; Hermite h0 - h4/100 for ε = -1) | paper | paper, survives. The **"confirmed numerically" sentence in its proof is false** (§3.4); the identity is true |
| 3 | Gap sharpness: Ftwin satisfies ζ's exact FE and has off-line zeros | kernel | FE kernel-checked; positivity of the measure (c ≥ 0) is paper. Ftwin is W1 rescaled by p^{1/2-s} |
| 4 | W1: ζ(s)(1 + c p^{-s} + p p^{-2s}), c² > 4p; exact FE, Euler product, exact off-line zero at (29,11) | kernel + paper | survives; kernel-checked parts confirmed |
| 5 | W2 (two primes): the off-line zeros can be pushed above any height T0 | paper + float64 | the existence proof is paper, **conditional on RH for ζ up to T0** (known to about 3e12); the numerical instance is float64 |
| 6 | Finite-T fooling lemma | paper | survives (modest, easy) |
| 7 | The one-prime surgery barrier and its exits D1-D4 | paper (assembly) | D1-D4 are cited theorems. "No intermediate class" and "no argument consuming only H-data can prove RH" are **HEURISTIC**. The quantifiers must be explicit. Partially refereed |
| 8 | Conductor-aspect ceiling: fixed-T positivity is optimal up to log log q, even with FE and Euler product | paper | **unrefereed** (truncated) |
| 9 | Scope limits (a)-(c) | paper | **unrefereed** (truncated) |
| 10 | Answer to the posed question | summary | **unrefereed**; it restates claims 1, 2, 4, 5 and 7 |

**Referees.**

- **Correctness (7, no kill).** The kernel core holds (the referee re-elaborated it), and there is no counterexample to Collapse A, Collapse B or W1. The referee also reproduced W2's three zeros, refined to \|E\| < 2e-30, and its counts 330 and 3. Decisive objections:
  - (i) Corollary (c) of Collapse A is false: L(s, χ) with χ a cubic character mod 7 is a counterexample, and ">> log x" is asserted without proof.
  - (ii) The barrier's quantifiers are unstated. The coefficient bound A must grow with N0; with A = 1, W1 cannot have an off-line zero.
  - (iii) H7b holds only below the verified RH height of ζ.
  - (iv) "No intermediate class" is HEURISTIC.
  - (v) Claim 3 is mis-tagged.
  - (vi) Step 2 needs a Hadamard fix, and the `q4_core` docstring overstates.
- **Relabeling (4, no kill).** The barrier assembles known classifications (Hamburger, Kaczorowski-Perelli, Soundararajan) with S#-versus-S folklore. Collapse A is a short corollary of KP99; what is new is a KP-free proof. Claim 3 duplicates W1. The Lean core is elementary algebra. What survives: Collapse B, the KP-free proof of Collapse A, W2's existence argument, and the fooling lemma.
- **Novelty (5, no kill).** Collapse B is the most valuable claim. It was not found anywhere: Hamburger's second theorem, Burnol (arXiv:1106.4749, which needs discrete frequencies in finitely many translates of ℤ and uses no positivity), Córdoba, Lev-Olevskii, Kurasov-Sarnak and Cohn-Elkies were all checked. Collapse A has modest novelty. W1, W2 and the fooling lemma have low novelty. The referee recommends consulting an expert (Burnol, Kaczorowski-Perelli, Broucke/Vindas) before any novelty claim.

**Salvage.** Recast the seat as a note led by Collapse B, with Ftwin as its sharpness example. Add Collapse A as a KP-free proof of a statement that also follows from KP99, and correct corollary (c). Keep W1, W2 and the fooling lemma as short illustrative remarks labelled "standard". State the barrier with explicit quantifiers and tag its meta-sentences HEURISTIC.

### 2.5 Where the seats converge, and where they conflict

**Convergence.**

- **Four distinct routes to the integer-frequency collapse** (three share the Kaczorowski-Perelli periodicity input):
  - theorem seat: KP99 periodicity, cumulant rigidity, finite differences, and |P(q)| ≤ 1;
  - literature seat: KP99, a mixture-of-Euler-products lemma, Landau, and Pólya-Ritt;
  - construct seat: KP99, Saias-Weingartner, and Lemma C;
  - barrier seat: Poisson periodicity (KP-free for μ ∈ {0, 1/2}), cumulants, Bohr uniqueness, and power sums.
- **Three independent proofs of the Beurling conductor-1 case:** the Cohn-Elkies f, the Fejér kernel, and the triangle LP with a Hermite certificate.
- **Duplicate kernel checks:**
  - The q = 4 control ζ(s)(1+4·2^{-s}+2·4^{-s}) is kernel-checked twice, in the theorem build and the literature build.
  - F0 (= W1 at (2,3)) is kernel-checked twice, in the construct build and the barrier core.
- **Relabeling.** All four relabeling referees diagnosed "RH for class P" as a relabeling of RH; two of them killed on that ground.

**Conflicts, and how they resolve.**

1. **"μ = 0 is forced" (theorem C1(iv)) versus "the μ ≠ 0 corner is open" (construct).** Both are right. C1(iv) assumes the Selberg normalization. Under the literal twisted P1, a real μ > 0 lets F have a pole at s = 0. Only μ = 1/2 is handled, by barrier Collapse A. μ real is forced in every normalization, by C1(iv)'s ratio-of-gammas argument, which does not use the pole structure.
2. **Excluding ε = -1.** The barrier and literature seats exclude it at q = 1; the construct seat excludes it for q < 1; theorem C5(ii) gives q ≥ 2π/3. These are consistent.
3. **Poisson normalizations.** The seats write the distributional identity differently:
   - construct: ν = δ0 + N_sym with ν̂ = εν + β(δ0 - ελ);
   - theorem: ν = εαδ0 + ν+ with ν̂ = εν;
   - barrier: ν = εrδ0 + N_sym with ν̂ = εν.

   The writer checked that the three are mutually consistent. They differ only in the mass placed at δ0. The Lebesgue term vanishes exactly when that mass equals ε·Res_{s=1}Λ, which gives β = 2A - ε in the construct form, where Res_{s=1}Λ = 2A.
4. **Novelty.** The theorem seat presents C3 as possibly new. Its referees place it as KP99 + SW09 plus a single new lemma. That lemma, |P(q)| ≤ 1 from log-positivity and periodicity alone, is the one piece nobody found in print.

---

## 3. Builds: verified (skeptic-unrefuted) versus refuted

### 3.1 The three skeptic-unrefuted builds

All three builds are **untracked** in `arda-cl-crux` (branch `cl/crux`). None is in CI or AxiomGuard.

| Build | Artifact | sha256 (prefix) | Island | `#print axioms` | Builder status | Skeptic |
|---|---|---|---|---|---|---|
| construct | `telperion/examples/rvm_bridge/lean/Crux/Crux_axiso_construct.lean` (1776 lines) | `d10aa76f663d8e12` | rvm_bridge: Lean v4.33.0-rc2, Mathlib `51e6992e`, Zeta23 `fbdc36bb` | 73 lines, all `[propext, Classical.choice, Quot.sound]` | kernel-checked | **not refuted** |
| theorem | `telperion/examples/li_positivity/lean/Crux/Crux_axiso_theorem.lean` (2079 lines) | `8744ea992d6dd2d4` | li_positivity: Lean v4.34.0-rc1, Mathlib `de5ce8a9` | 98 lines: 97 three-axiom; `IsQSmooth.dvd` uses `[propext]` only | partial | **not refuted** |
| literature | `telperion/examples/li_positivity/lean/Crux/Crux_axiso_literature.lean` (1246 lines) | `30bc271808d2aac2` | li_positivity | 40 lines: 37 three-axiom; `one_le_coefF` and `coefF_le_seven` use `[propext, Quot.sound]`; `coefF_eq` uses `[propext]` | kernel-checked | **not refuted** |

Every file contains no `sorry`, `admit`, `native_decide`, new `axiom` or `opaque`. The construct skeptic also scanned for `set_option`, `macro`, `elab`, `instance`, `unsafe`, `partial`, `#eval` and `run_cmd`, and found none.

**What each build establishes (THEOREM-kernel-checked):**

- **Construct.**
  - A kernel definition of P2 (`IsLogDerivCoeff`). Λ_F is unique whenever it exists (`logMul_eq_convolution`). P2 gives a_n ≥ 0 (`positivity_lemma`), and P2 gives a(p)² ≤ 2a(p²) (`P2_forces_sq_ineq`). Positive control: ζ satisfies P2 (`zeta_P2`).
  - F0: an entire completion with Xi0(1-s) = Xi0(s) and conductor 4 (`Xi0_entire`, `Xi0_one_sub`, `Xi0_eq`); coefficients in {1, 4, 6}, multiplicative; zero set exactly {i t_k} ∪ {1 + i t_k} with t_k = (2k+1)π/log 2 (`P0_eq_zero_iff`); every representation has Λ_F0(4) = -4 log 2 (`F0_not_P2`).
  - Lemma C at q = p and q = p², for every prime p (`lemmaC_prime`, `lemmaC_prime_sq`).
  - F1 and the E8 twin: entire, symmetric completions; no zero on Re s = 1/2; every zero off the line; **infinitely many off-line zeros, unconditionally** (`Xi1_offline_zeros`, via `exists_nontrivial_zero_above` from Zeta23's hypothesis-free RvM formula); P2 in Beurling form (`F1_logDeriv_hasSum`); a genuine pole at 1/2 (`F1_pole_half`).
  - Theorem A Step 3, conditional on the Step-2 pairing identity (`thmA_step3_plus`, `thmA_step3_minus`, `ce_support_forcing`).
  - The (d+1)/2 rescaling algebra.
- **Theorem.**
  - `classP_eq_zeta`: IsDirExp a b (a = exp*(b), a(1) = 1), b ≥ 0, a periodic mod q, and |P(q)| = √q with P = a ⋆ μ together imply q = 1 and a ≡ 1. Multiplicativity is never assumed.
  - Steps 1-4 are kernel-checked separately: `step1_units` (uses Mathlib's Dirichlet theorem), `step2`, `step3`, and `step4_top_coeff`, which gives |P(q)| ≤ 1 **without the FE**.
  - `cumulant_rigidity` and `finite_difference_rigidity` replace the paper proof's use of Pringsheim, Hadamard and independence of exponentials.
  - Non-vacuity (`classP_hypotheses_satisfiable`) and sharpness (`a2_topcoeff`, `a2_logcoeff_four`).
  - The q = 4 control: exact FE, the zero at Re s₀ = log₂(2+√2), and b(4) = -11/2.
  - The conductor-5 KP element's coefficient b(2·7·17·37) = -2.
  - The C6 algebra and the 3-4-1 inequality.
- **Literature.**
  - The q = 4 control in full: coefficients 1, 5, 7 (`LSeries_coefF`), multiplicative (`coefFA_isMultiplicative`); the zeta-shape FE with conductor 4 and ε = +1 (`completedF_fe`); exact zeros at s_k = log₂(2+√2) + i(2k+1)π/log 2 with ζ(s_k) ≠ 0 (`negControl_zeros`); Λ(4) = -11 log 2 for every analytic representation (`vonMangoldtF_of_logDeriv`).
  - The DH-type mixture: coefficients ≥ 0 if and only if |b| ≤ a; closed forms for Λ at 4, 6, 12, 36, 42 and 546; for every a ≥ |b| > 0, one of Λ(6), Λ(12), Λ(36) is negative (`dhMixture_P2_fails`).
  - E8: FE, no zero on the critical line, zeros at 2ρ + 5/2 for every ζ-zero ρ, Euler product for Re s > 9/2.
  - θ = 0 from n^{-iθ} ≥ 0 on the residue class 1 mod q (`theta_eq_zero_of_nonneg_twist`).

**What the builds do not establish.**

- Theorem A as a whole: Steps 2 and 4, and the Fourier pair in Lean.
- Kaczorowski-Perelli, Saias-Weingartner, Hamburger, Landau, Lev-Olevskii, Kahane-Mandelbrojt.
- The implication "FE implies |P(q)| = √q". It is the hypothesis `hFE` of `classP_eq_zeta`.
- Finite order of any completion.
- The E8 identification 240 ζ(u)ζ(u-3).
- The root number of L(s, χ₅).
- DH-type zeros in σ > 1.
- Anything about RH.

**Skeptic caveats (none refutes a build):**

- Construct: "five is sharp at p = 2" is a hand-verified fact, not a Lean theorem; `Xi1_eq` holds only for Re s > 1/2, s ≠ 5/2; numerics check N6.zeta_pairing is vacuous.
- Theorem: `a2_logcoeff_four`, `a9_logcoeff_four` and `a5_logcoeff` are stated "for any b with IsDirExp a b", with no Lean proof that such b exists (existence is trivial, by recursion); `nc_F_vanishes` is not linked in Lean to a9's Dirichlet series.
- Literature: the third conjunct of `cumulant_pm_one` is a bare ring identity; the DH non-vacuity has no `_consistent` theorem; the stress test could be tagged HEURISTIC.

### 3.2 This writer's re-verification

**Lean.** The four snapshots were re-elaborated with `leanlock.sh lake env lean <file>` on the pinned islands. Results:

| File | Result |
|---|---|
| theorem | exit 0 |
| literature | exit 0 |
| construct | exit 0 in 60 s |
| barrier | exit 0 in 34 s, `push_neg` deprecation warnings only |

In every case the axiom lines are identical to the recorded transcripts: `research/axiso_construct/outputs/lean_print_axioms.txt`, `research/axiso_theorem/lean_axiom_audit.txt`, the literature skeptic's transcript, and the barrier correctness referee's transcript.

**Restatements.** Thirteen restatements using only Mathlib vocabulary were appended and proved from the artifacts, each with exactly `[propext, Classical.choice, Quot.sound]`:

| Artifact | Restatement | Statement |
|---|---|---|
| theorem | `writer_classP_coeff_collapse` | `classP_eq_zeta` with `IsDirExp` unfolded |
| theorem | `writer_top_coeff_le_one` | `step4_top_coeff` |
| theorem | `writer_q4_control_zero` | ∃ s, 1 < Re s ∧ ζ(s)(1+4·2^{-s}+2·4^{-s}) = 0 |
| literature | `writer_negcontrol_zero_right_of_one` | the same zero, with Im s ≠ 0 and ζ(s) ≠ 0 |
| literature | `writer_negcontrol_fe` | the conductor-4 FE with explicit Γ_ℝ |
| construct | `writer_F1_offline_zeros` | ∀ T ∃ s, ζ(s/2+3/4)ζ(s/2-1/4) = 0, 1/2 < Re s < 5/2, T < Im s |
| construct | `writer_zeta_zero_above` | ∀ T ∃ ρ, ζ(ρ) = 0, 0 < Re ρ < 1, T < Im ρ |
| construct | `writer_F0_zero_on_one_line` | ∃ s, Re s = 1 ∧ ζ(s)(1+3·2^{-s}+2·4^{-s}) = 0 |
| barrier | `writer_W1_29_11_offline` | the exact zero with 1/2 < Re s < 1 |
| barrier | `writer_W1_29_11_fe` | the conductor-841 FE with Mathlib's `completedRiemannZeta` |
| all | three node statements | proved from the artifacts; §5.2 |

**Numerics.** Every script except `integer_case_stress.py` was re-run from scratch copies with `/usr/bin/python3` (mpmath 1.3.0, python-flint 0.6.0, numpy 1.23.5, scipy 1.13.1). All exit 0 and reproduce the recorded values:

- **Construct numerics:** 26 of 26 PASS.
- **`verify_axiso_theorem.py`:** K1 and K2 give 0 counterexamples. Every log-positive periodic example has |P(q)| ≤ 1. For C9(i), b(4) = -11/2. For C9(ii), b(36) = -1/2 and b(8806) = -2.
- **Literature:**
  - Arb winding counts: 1 for the E8 off-line box, 1 for its mirror, and 0 for the box on the line.
  - Two certified off-line zeros of the DH-type mixture, at 0.779557 + 61.168517i and 0.804688 + 61.083549i.
  - The DH crown box re-certified with winding 1, and its control box 0.
  - The theta identity enclosed as 1 ± 2e-76.
- **Barrier:**
  - W2 (101, 10007, a = 1.0001): 330 zeros in [-0.5, 1.5] × [0.01, 150], against 330 sign changes on the line; winding 3 on [0.5006, 1.5] × [150, 170]. The first off-line zeros are 0.501943 + 162.690i, 0.502121 + 164.053i and 0.501093 + 165.416i.
  - The 3-4-1 sweeps pass for (29,11), (53,15), (101,21), (1009,64) and W2, and fail for (11,7), as the seat itself reported.
  - All of this is float64 only.

### 3.3 Outside the skeptic filter: the barrier seat's kernel core

`/Users/peterwmurphy/arda-closure/telperion/examples/class_p_barrier/lean/ClassPBarrierCore.lean` (302 lines, sha256 `a1d8a4369701964717beb9b635210fb8c44d4d39dc26d261cfe957cc83c5e953`). It lives in a different worktree (branch `rh/closure-base`) and is untracked there.

The file is **not** a Build-phase artifact, and no skeptic attacked it (§0.3, point 3). Two independent re-elaborations cover it: the barrier correctness referee (in `li-box-island`, Lean v4.34.0-rc1, Mathlib `de5ce8a9`) and this writer. Both give exit 0; 7 theorems report the three standard axioms, and `local_signs29` uses no axioms at all. The writer's restatements `writer_W1_29_11_offline` and `writer_W1_29_11_fe`, and the node statement `node_negctl_W1_29_11`, are proved from it.

Its content: E_{p,c} is self-reciprocal for every real c and every p > 0. The completed witness satisfies the exact FE. An exact zero sits at 29^{-s*} = (-11+√5)/58, with 1/2 < Re s* = 0.5612 < 1. F0 (the (2,3) case) has a zero on Re s = 1. Newton power sums give the local signs 12, -62, 375, -2286. The file also contains `q4_core` and the Ftwin FE.

It is listed for completeness. Because no skeptic attacked it, it is not counted among the verified builds.

### 3.4 Refuted, withdrawn or downgraded

| # | Item | Where | Refuted by | Replacement |
|---|---|---|---|---|
| 1 | "Every non-ζ element of S#_1 with a_1 = 1 has infinitely many n with Λ_F(n) < 0, counting function >> log x" | barrier, Collapse A corollary (c) | barrier referees 1 and 2: L(s, χ) with χ cubic mod 7 has Λ_F(n) = χ(n)Λ(n), which is never negative, only non-real | "Λ_F(n) ∉ [0, ∞) for infinitely many n"; the >> log x rate is unproved |
| 2 | "Normalisation check Σ_{n≠0} a sinc²(an) = 1 - a, confirmed numerically (numerics/surgery_checks.py)" | barrier, Collapse B proof text | barrier referee 1 and this writer. The cited script prints 0.66642 against 0.7 at a = 0.3 (also 0.22868 against 0.23, and 0.000628 against 0.001), because mpmath `nsum` mis-extrapolates this oscillating series | The identity is **true** (Poisson summation for the Fejér triangle). Direct summation to N = 200000 lands within the rigorous tail bound 2/(π²aN): the error is 1.7e-6 at a = 0.3, 6.6e-7 at a = 0.77 and 5.1e-7 at a = 0.999. The "confirmed" sentence must cite direct summation |
| 3 | "H does not imply RH ... no argument consuming only H-data about ζ can prove RH", "no intermediate class in degree one" | barrier claim 7 | all three barrier referees | The meta-sentences are **HEURISTIC**. The existence statement needs "for every N0, T, η, T0 there exist A, C", with T0 below the verified RH height for H7b. Fixing A = 1 blocks W1. D1-D4 remain cited theorems |
| 4 | Ftwin tagged THEOREM-kernel-checked | barrier claim 3 | barrier referees 1 and 2 | Only the FE is kernel-checked. Positivity of the measure (needs c ≥ 0) and Γ_ℝ·Ftwin are paper. Ftwin = p^{1/2-s}·W1, so it is not an independent witness |
| 5 | `q4_core` docstring "the conductor-4 slice of class P is empty" | barrier Lean file | barrier referee 1 | Holds only under strict all-n P2, and presupposes the paper classification of conductor-4 elements |
| 6 | Title "every counterexample route is blocked; class P collapses to {zeta}" | construct | construct referee 1 | Scope: {ζ} in readings R1, R2 and R3; R4 with q > 1, and R2' with real μ > 0, μ ≠ 1/2, are open |
| 7 | "F1 breaks only the s(s-1) pole normalization"; "Euler product over the Beurling primes √p" | construct near-miss 2 | construct referees 1 and 3 | F1 also has √n frequencies, μ = 3/4 and q = 1/2. It is a weighted Euler product, not a Beurling zeta |
| 8 | Prop D step "G of order ≤ 1" | construct | construct referee 1 | "Finite order, so g is a polynomial; g(σ) → 0 forces g = 0" |
| 9 | Theorem B, "χ principal via trivial zeros" | construct | construct referee 1 | "P·L(s, χ) is entire for non-principal χ, contradicting the pole at 1" |
| 10 | Rescaling formula w = s/d + 1/2 - 1/(2d) applied to Epstein/E8 | construct | construct referee 1 | That formula is the Dedekind-type normalization; the pole location (d+1)/2 still stands |
| 11 | "P1+P2 give no density result beyond RvM" inside a THEOREM tag | theorem C8 | theorem referee 1 | **HEURISTIC** |
| 12 | 3-4-1 exclusion used before the pole is shown to be simple | theorem C1(iii) | theorem referee 1 | Reorder: the simple pole comes from C1(iv) |
| 13 | C3 Step 4 goes from "no real zeros" to "no zeros on σ > 0" | theorem | theorem referee 2; build README | A second Landau step is needed. The kernel proof takes a different route and does not need it |
| 14 | κ₃ = -8ab(a-b) "is negative"; zeros "in σ > 1" of the DH-type mixture | literature claim 4 | literature referee 1; literature build | κ₃ = -8ab(a-b)/(a+b)³ is positive for b < 0. Kernel-checked witnesses: Λ(12) < 0 when 0 < b < a, Λ(36) < 0 when a = b, Λ(6) < 0 when b < 0. The σ > 1 zeros stay a paper sketch; Arb certifies off-line zeros in 1/2 < σ < 1 instead |
| 15 | "E8 is excluded from P1 only because its pole sits at 9/2" | literature claim 8 | literature referee 1; build | True only in the free-(Q, μ) frame. In the zeta-shape frame the gamma shift 7/4, the factor (2π)^{-s/2} and coefficients of size n^{5/4} also exclude it |
| 16 | Literature absence: "no paper on RH for Beurling zetas with a zeta-type FE" | literature claim 11 | literature referee 3 | **Refuted as written.** Beurling, Ark. Mat. 1 (1951) and Dixit, JNT 206 (2020) plus corrigendum are directly relevant |
| 17 | "Bounded weights, positive density" step | literature claim 6 | literature referee 1 | Unnecessary; the infinite-coset pigeonhole suffices |
| 18 | `telperion.arb_dh.winding_number` docstring: "a returned integer is a RIGOROUS zero count", and the matching wording in `QC_DH_SCOUT.md` §4 | repo tool, not a seat claim | literature build, confirmed by the literature skeptic and by this writer's reading of `arb_dh.py:409-447` | The method encloses D only at boundary nodes and sums quadrant steps, so it cannot exclude an extra turn between two nodes. The **method** claim is refuted. The crown-box **conclusion** stands: re-certified with whole-segment enclosures (`research/axiso_literature/arb_winding.py`), giving winding 1, with 0 on the control box |
| 19 | Build selection by the mean of scores on mixed scales | workflow | this writer | A process defect: it excluded the barrier seat from the Build and skeptic phase (§0.3) |

---

## 4. The answer as it stands

### 4.1 Proved

**(P-i) THEOREM-paper-proof (classical).** In reading R1 (literal zeta shape, integer frequencies), class P = {ζ}. This is Hamburger (Math. Z. 10, 1921; Titchmarsh Thm 2.13). P2 only supplies absolute convergence, through Landau.

**(P-ii) Reading R2: class P = {ζ}.**

- **Tag.** THEOREM-paper-proof, with its coefficient-level core THEOREM-kernel-checked.
- **Statement.** Take integer frequencies and twisted P1 with any Q > 0 and Re μ ≥ 0, in the Selberg normalization. Then class P = {ζ}; in particular Q = π^{-1/2}, μ = 0 and ε = 1. No Euler product is assumed.
- **External inputs.**
  - The Kaczorowski-Perelli structure theorem for S#_1 (Acta Math. 182, 1999): q ∈ ℕ and a(n)n^{iθ} periodic mod q. Its exact theorem number and statement still have to be confirmed against the paper.
  - Landau's theorem, used for the normal form.
  - Everything else is elementary or in Mathlib.
- **Kernel core.** `classP_eq_zeta` and `step4_top_coeff`, restated in Mathlib vocabulary in §5.2. θ = 0 is kernel-checked from its elementary hypothesis (`theta_eq_zero_of_nonneg_twist`).
- **Novelty.** With an Euler product the statement is immediate from KP99. Without one it is KP99 + Saias-Weingartner plus one new lemma: log-positivity together with periodicity forces |P(q)| ≤ 1, where P = F/ζ. No prior statement was found, but the search was not exhaustive.
- **Stronger variant (barrier Collapse A).** P2 for all but finitely many n suffices, for μ ∈ {0, 1/2}, with a KP-free proof. THEOREM-paper-proof, after the Step-2 Hadamard fix. Not kernel-checked.

**(P-iii) THEOREM-paper-proof (immediate).** "Every F in class P satisfies RH" is RH, verbatim. It is not GRH: L(s, χ) with χ ≠ χ₀, and ζ(s + iθ) with θ ≠ 0, violate P2. Multiplicativity is a consequence of the axioms, not an input. This is the relabeling on which two referees killed, and all four relabeling referees agreed on the diagnosis.

**(P-iv) Reading R3: the Beurling class P at conductor 1 is {ζ}.**

- **Statement.** Let N be a positive measure on [1, ∞) with N({1}) = 1 and polynomial growth. If s(s-1)π^{-s/2}Γ(s/2)∫x^{-s}dN is entire of finite order and satisfies the FE, then N = Σ_{n≥1} δ_n.
- **Tag.** THEOREM-paper-proof, with three independent proofs:
  - construct Theorem A (Cohn-Elkies f);
  - theorem C5(i) (Fejér kernel);
  - barrier Collapse B (triangle LP, with a Hermite certificate for ε = -1).
- **Kernel.** Step 3 is kernel-checked, conditional on the Step-2 pairing identity. The Fourier pair is checked symbolically (sympy) and by 50-digit quadrature.
- **Consequence.** No system of Diamond-Montgomery-Vorhauer type, and indeed no positive system at all, satisfies ζ's exact FE.
- **Companion results.**
  - Conductor bound: for ε = +1 with N ≥ 0, q ≥ 1, with equality only for ζ. THEOREM-paper-proof.
  - For ε = -1, q ≥ 2π/3. THEOREM-paper-proof, not sharp.
  - The gap hypothesis (all frequencies ≥ 1) is necessary: Ftwin's FE is kernel-checked, and positivity of its measure is paper.
- **Open points.**
  - Referee caveat: the step "FE implies a distributional Poisson identity" must be written out with its growth hypotheses. The writer expects a standard Phragmén-Lindelöf argument to deduce them from finite order, but this has not been written.
  - Novelty is unverified; the nearest prior art is Beurling 1951, Kahane-Mandelbrojt 1958, Burnol 2011 and Dixit 2020.

**(P-v) THEOREM-kernel-checked: which axiom does the work (re-verified by this writer).**

- **FE + Euler product + a_n ≥ 0 does not give a zero-free σ > 1.**
  - Witness: ζ(s)(1+4·2^{-s}+2·4^{-s}), coefficients in {1, 5, 7}, multiplicative, conductor 4, ε = +1.
  - Its zeros sit at log₂(2+√2) + i(2k+1)π/log 2, which is 1.77155 + 4.53236i for k = 0, and they are zeros of the absolutely convergent Dirichlet series itself.
  - Λ_F(4) = -11 log 2.
  - Checked twice, in independent builds.
- **The same data does not even give the prime number theorem line.**
  - Witness: F0 = ζ(s)(1+2^{-s})(1+2^{1-s}), coefficients in {1, 4, 6}, multiplicative, with an entire symmetric completion of conductor 4.
  - Its zeros lie exactly on Re s = 0 and Re s = 1.
  - Λ_F0(4) = -4 log 2 for every representation of Λ_F0.
- **P2 below a threshold does not suffice.** W1(29,11) has the exact FE of conductor 841 and an Euler product. It has an exact zero with Re s* = 0.5612. P2 holds for every n < 841 and fails exactly at the even powers of 29; that part is paper bookkeeping, with the local signs 12, -62, 375, -2286 kernel-checked. This witness comes from the barrier core, which is outside the skeptic filter.
- **Every real self-reciprocal twist ζ·P fails P2,** where P is a Dirichlet polynomial on the divisors of p or of p², for every prime p (Lemma C at conductors p and p²).
- **P2 plus one gamma factor plus an exact FE does not give RH without the pole normalization.** F1 = ζ(s/2+3/4)ζ(s/2-1/4):
  - it satisfies P2 in Beurling form;
  - it has one gamma factor and an entire symmetric completion;
  - it has no zero on Re s = 1/2;
  - it has infinitely many zeros with 1/2 < Re s < 5/2, unconditionally, via Zeta23's RvM formula.

  The E8 twin behaves the same way.
- **The DH-type q = 5 mixture fails P2 whenever its coefficients are nonnegative,** that is, for every a ≥ |b| > 0 (normalized so that a + b = 1).

**(P-vi) THEOREM-paper-proof, final algebra kernel-checked.** Every F satisfying P1 + P2 has the explicit region σ > 1 - (7-4√3)/((5/2)log(|t|+1) + 4 log q + 2.44) for |t| ≥ 1. It also satisfies an RvM formula with conductor. For integer members, which are all ζ, both are strictly weaker than known results. They carry content only for hypothetical Beurling members with q > 1. FE reflection adds no positivity of its own: that is an identity, C7(a). Rate improvements for class P come only through rigidity; that meta-claim is HEURISTIC.

**Short answer to "what does adding P1 to positivity buy, with and without multiplicativity":**

- **Uniqueness.** In integer frequencies, with or without multiplicativity, the class is {ζ}.
- **Beurling at conductor 1:** likewise {ζ}.
- **Beurling with q > 1:** unknown.
- **Zero-free regions:** nothing beyond the classical rate.

### 4.2 Conjectured, with evidence

- **The twisted Beurling conjecture: the Beurling class P is {ζ}.** Equivalently, no log-positive Beurling system has the zeta-shape FE with conductor q > 1. The statement text is in §5.2. Stated by the construct seat (claim 11), the theorem seat (C10) and the barrier seat (open problem 1). No referee attacked the conjecture itself.
  - **Evidence:**
    - q < 1 is impossible, and ε = -1 needs q ≥ 2π/3.
    - q = 1 forces ζ.
    - Integer frequencies force ζ.
    - Twists of ζ by integer-frequency Dirichlet polynomials are excluded.
    - Uniformly discrete g-integers force ζ (paper sketch via Lev-Olevskii).
    - The K = Q branch of the Kahane-Mandelbrojt order argument forces ζ.
    - An integer-frequency optimization stress test (q ≤ 24, n ≤ 3000) found a negative log-coefficient in every case. The best value drifts toward 0 (-0.676 at q = 24), so it is not uniform in q; it is float64 evidence only.
  - **Caution.** N ≥ 0 alone cannot decide q > 1: ζ(s)(1 + √q·q^{-s}) satisfies the FE with N ≥ 0 for every real q > 1 and fails only P2. So any proof has to use the multiplicative structure of P2.
- **The W2 numerical instance** (101, 10007, a = 1.0001): no off-line zero with t ≤ 150, and the first off-line zero at 0.50194 + 162.690i. Float64; reproduced by barrier referee 1 and by this writer; not interval-certified.
- **Novelty claims.** Theorem A / Collapse B, Collapse A, and the |P(q)| ≤ 1 lemma were not found in the literature. The referee searches were targeted, not exhaustive, and no expert was consulted.

### 4.3 Heuristic, and unrefereed

- **HEURISTIC:**
  - "no intermediate soft class in degree one" (barrier claim 7);
  - "beating de la Vallée Poussin needs arithmetic" (literature claim 9, theorem C7);
  - the C8 density sentence;
  - the mapping of the Weil-wall mechanisms into the barrier's hypothesis class (barrier claim 7, its own tag).
- **Unrefereed**, because the referees' input was truncated at 14,000 characters. None of these is counted as proved:
  - barrier claim 8, the conductor-aspect ceiling: W1 zeros at Re s = 1 - (log log q + C_T)/log q, which would make fixed-T positivity methods optimal up to log log q;
  - barrier claim 9, the scope limits;
  - barrier claim 10, the summary;
  - construct claim 10, moving zeros and signed Beurling measures;
  - construct claim 11 and theorem C10, the conjecture;
  - most of theorem C9 (its kernel-checked parts are counted through the builds).

### 4.4 Open

1. **The twisted Beurling cell (R4, q > 1).** Classify the positive self-dual measures ν = rδ0 + N_sym with gap (-q^{-1/2}, q^{-1/2}) whose positive part is a Beurling integer measure. The triangle-function argument only gives ∫ sinc²(x/q) dN_sym ≤ r(1 - q^{-1/2}), which is not rigid.
2. **The μ corner (R2').** Under the literal twisted P1, a real μ > 0 with μ ≠ 1/2 allows simple poles of F at both 0 and 1, outside S#. No collapse proof covers it. The linear-programming analogue is a Hankel-transform sign-uncertainty problem. The construct seat notes, unrefereed, that sharp magic functions exist only in effective dimensions 4μ + 1 ∈ {1, 8, 24}.
3. **The sharp ε = -1 threshold** in the Beurling class. Is ε = -1 impossible for every q?
4. **The Kahane-Mandelbrojt hypothesis.** Does H_0 follow from P1 + P2? And the case where the g-integers generate an order in a real number field K ≠ Q.
5. **FE-defect witnesses** (barrier open problem 2). Are there positive Beurling systems whose completion satisfies ξ(s) = ξ(1-s)(1 + O(ε)) on a region that contains an off-line zero? Collapse B says the defect cannot be zero. This is the only route to a t-aspect barrier for ζ itself.
6. **The θ = 1/2 boundary outside S#_1:** an FE, an Euler product, |Λ_F(n)| << √n log n, and an off-line zero.
7. **A formal proof of the collapse** that does not use KP99: see NT3 in §5.1.
8. **Degree ≥ 2 positive classes** (for example Dedekind zeta functions) as test beds with both axioms and members other than ζ. This is the theorem seat's open problem 5.
9. **RH.** `conjecture1_proved = False`.

---

## 5. Next theorems and draft registry nodes

### 5.1 The next theorems, in order

**NT1: the top coefficient from the FE (a small kernel target).**

- **Statement.** Let q ≥ 1 and P: ℕ → ℝ with P(1) = 1, supported on the divisors of q. Suppose q^{s/2}·Σ_{d|q} P(d)d^{-s} = ε·q^{(1-s)/2}·Σ_{d|q} P(d)d^{-(1-s)} for all s ∈ ℂ. Then P(q) = ε√q, and ε² = 1.
- **Proof idea.** Compare the coefficients of the distinct exponentials (√q/d)^s. The coefficient at d = q gives P(q) = ε√q, and the coefficient at d = 1 then forces ε² = 1.
- **Payoff.**
  - It discharges the hypothesis `hFE` of `classP_eq_zeta`.
  - It makes **Lemma C kernel-checked for every conductor**, not only p and p². The reason: for F = ζ·P with P on the divisors of q, a = 1 ⋆ P depends only on gcd(n, q), so it is automatically periodic mod q, and `classP_eq_zeta` applies. This reduction is the writer's observation; it is elementary but unrefereed.

**NT2: the collapse with KP99 as the only external input (a medium kernel target).**

- **Statement.** Take the hypotheses of `classP_eq_zeta`, with `hFE` replaced by the analytic FE: an entire ξ with ξ(s) = s(s-1)(q/π)^{s/2}Γ(s/2)L(a, s) for Re s > 1, and ξ(1-s) = εξ(s). Then q = 1 and a ≡ 1.
- **Proof route** (the writer's; unrefereed).
  1. `step3` gives L(a, s) = ζ(s)P(s).
  2. On Re s > 1, ξ = q^{s/2}P(s)·ξ_ζ(s), with ξ_ζ = s(s-1)Λ_ζ entire. The identity theorem extends this to ℂ.
  3. ξ_ζ has isolated zeros, so the FE transfers to q^{s/2}P(s), and NT1 applies.
- **Finite order is not needed** on this route.
- **Cross-island note.** The analytic-to-formal P2 bridge (`logMul_eq_convolution`) already exists on the rvm_bridge island (v4.33), while `classP_eq_zeta` is on li_positivity (v4.34). Combining them requires a port.

**NT3: degree-1 periodicity without KP99 (a medium-hard formalization).**

- **Statement.** Take integer frequencies, the untwisted gamma shape Γ(s/2), an absolutely convergent series on σ > 1, and ξ entire of order 1 with the FE. Then πQ² = q ∈ ℕ and a is q-periodic, so θ = 0 automatically.
- **Status.** This is the barrier seat's Collapse A, Step 1 (Poisson periodicity via Bochner's modular relation). It is also the μ = 0 case of KP99.
- **Payoff.** Together with NT2, the integer-frequency class P = {ζ} becomes a kernel theorem with **no** external black box.
- **Missing from Mathlib.** The modular relation for general polynomially bounded sequences. Poisson summation and the Jacobi theta FE are available.

**NT4: Collapse B / Theorem A in the kernel.**

- Prove the Fourier pair 𝓕(ceF) = ceFhat (an elementary integral, then Mathlib's Fourier inversion).
- Prove Step 2: the FE of a positive measure implies the distributional Poisson identity, with growth hypotheses stated.
- This removes the pairing hypothesis from `thmA_step3_plus` and `thmA_step3_minus`.

**NT5: research on the twisted Beurling cell.** The natural first theorem is **Beurling Lemma C**:

- **Statement.** Let G(s) = Σ_{λ∈L} g_λ λ^{-s} be a finite generalized Dirichlet polynomial, with real frequencies L ⊂ [1, ∞), g_1 = 1 and real coefficients. If ζ·G is a log-positive Beurling system satisfying the twisted zeta-shape FE, then G = 1 and q = 1.
- **What is known.** The integer-frequency case is NT1 plus `classP_eq_zeta`. When the frequencies of G generate a single ray λ^k with no λ^k an integer, the `step4_top_coeff` mechanism appears to apply verbatim: nonnegative log-coefficients force the roots of the polynomial outside the unit disk, while the FE forces a top coefficient of modulus √q > 1. This is the writer's remark, HEURISTIC and unrefereed.
- **The difficulty.** Frequency semigroups with several generators, where ζ's compensating prime-power mass lands on mixed monomials (construct open problem 3).
- **Later targets.** Derive the Kahane-Mandelbrojt H_0 from P1 + P2, then exclude real-quadratic orders.

**NT6: FE-defect witnesses (strategy).** See §4.4, item 5.

### 5.2 Draft registry nodes (statement text)

**Scope.** Every statement text below was elaborated against Mathlib `de5ce8a9` (the li_positivity island, or `li-box-island` for the barrier core) or against the rvm_bridge island. The five lemma statements are **proved** from the existing artifacts. The four targets and the conjecture are typechecked as `Prop` definitions only. The scratch files are `axiso_doc_verify/{T2,L3,C3,B3}.lean` (proved) and `Stmts.lean` (sha256 `0887fc5f...`).

**Before any `mission add` or `grant`:**

1. Commit the artifacts. They are untracked today, and the barrier core is in another worktree.
2. Put a skeptic on the barrier core.
3. Add every theorem to an AxiomGuard target.
4. Blind read-back audit, as usual.

The construct-based node is cross-island (rvm_bridge, Zeta23), exactly like the de la Vallée Poussin nodes, so `closure_clean` stays false until cross-island CI is wired.

**A. Lemmas that are ready to grant (all proved from the artifacts).**

`RH_classP_coeff_collapse`: kind `lemma`, no deps. Title: *"Class P at the coefficient level: F = exp G with G ≥ 0, periodic mod q, and |(F/ζ)(q)| = √q force q = 1 and F = ζ. The KP99 periodicity and the FE's top coefficient are HYPOTHESES."* Artifact: `examples/li_positivity/lean/Crux/Crux_axiso_theorem.lean` (`Crux.AxisoTheorem.classP_eq_zeta`).

```lean
theorem classP_coeff_collapse (q : ℕ) [NeZero q] (a b : ArithmeticFunction ℝ)
    (h1 : a 1 = 1)
    (hlog : a.pmul ArithmeticFunction.log = (b.pmul ArithmeticFunction.log) * a)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n : ℕ, 0 < n → a n = A (n : ZMod q))
    (hFE : |(a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) q| = Real.sqrt (q : ℝ)) :
    q = 1 ∧ ∀ n, 0 < n → a n = 1
```

`RH_classP_top_coeff_le_one`: kind `lemma`, no deps. Title: *"Log-positivity plus periodicity alone bound the top coefficient of F/ζ: |(F/ζ)(q)| ≤ 1 (no FE used)."* Artifact: the same file (`step4_top_coeff`).

```lean
theorem classP_top_coeff_le_one (q : ℕ) [NeZero q] (a b : ArithmeticFunction ℝ)
    (h1 : a 1 = 1)
    (hlog : a.pmul ArithmeticFunction.log = (b.pmul ArithmeticFunction.log) * a)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n : ℕ, 0 < n → a n = A (n : ZMod q)) :
    |(a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) q| ≤ 1
```

`RH_negctl_fe_euler_zero_right_of_one`: kind `lemma`, no deps. Title: *"Negative control: FE (conductor 4, root number +1) + multiplicative coefficients in {1,5,7} + a zero with Re s > 1; P2 is the axiom that fails."* Artifact: `examples/li_positivity/lean/Crux/Crux_axiso_literature.lean` (`LSeries_coefF`, `coefFA_isMultiplicative`, `completedF_fe`, `negControl_zeros`).

```lean
theorem negctl_q4_zero_right_of_one :
    (∀ s : ℂ, 1 < s.re →
        LSeries (fun n : ℕ => ((1 + (if 2 ∣ n then 4 else 0) + (if 4 ∣ n then 2 else 0) : ℕ) : ℂ)) s =
          riemannZeta s * (1 + 4 * (2 : ℂ) ^ (-s) + 2 * (4 : ℂ) ^ (-s))) ∧
    (∀ m n : ℕ, m ≠ 0 → n ≠ 0 → Nat.Coprime m n →
        (1 + (if 2 ∣ m * n then 4 else 0) + (if 4 ∣ m * n then 2 else 0) : ℕ) =
          (1 + (if 2 ∣ m then 4 else 0) + (if 4 ∣ m then 2 else 0)) *
          (1 + (if 2 ∣ n then 4 else 0) + (if 4 ∣ n then 2 else 0))) ∧
    (∀ s : ℂ, Complex.Gammaℝ s ≠ 0 → Complex.Gammaℝ (1 - s) ≠ 0 →
        (4 : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) *
            (riemannZeta (1 - s) * (1 + 4 * (2 : ℂ) ^ (-(1 - s)) + 2 * (4 : ℂ) ^ (-(1 - s)))) =
          (4 : ℂ) ^ (s / 2) * Complex.Gammaℝ s *
            (riemannZeta s * (1 + 4 * (2 : ℂ) ^ (-s) + 2 * (4 : ℂ) ^ (-s)))) ∧
    ∃ s : ℂ, 1 < s.re ∧ s.im ≠ 0 ∧
      riemannZeta s * (1 + 4 * (2 : ℂ) ^ (-s) + 2 * (4 : ℂ) ^ (-s)) = 0
```

`RH_negctl_W1_offline_in_strip`: kind `lemma`, no deps. Title: *"Negative control W1(29,11): exact FE of conductor 841 with ζ's gamma factor, Euler product, P2 for all n < 841, and an exact zero with 1/2 < Re s < 1 (no Arb trust boundary)."* Artifact: `ClassPBarrierCore.lean` (`completedF_one_sub`, `witness29_offline`). **Precondition:** copy the file into this branch and put a skeptic on it. The P2-below-841 part is `local_signs29` in the file plus paper bookkeeping; it is not in this statement.

```lean
theorem negctl_W1_29_11 :
    (∀ s : ℂ,
      ((29 : ℝ) : ℂ) ^ (1 - s) * (1 + ((11 : ℝ) : ℂ) * ((29 : ℝ) : ℂ) ^ (-(1 - s))
          + ((29 : ℝ) : ℂ) * ((29 : ℝ) : ℂ) ^ (-(2 * (1 - s)))) * completedRiemannZeta (1 - s) =
        ((29 : ℝ) : ℂ) ^ s * (1 + ((11 : ℝ) : ℂ) * ((29 : ℝ) : ℂ) ^ (-s)
          + ((29 : ℝ) : ℂ) * ((29 : ℝ) : ℂ) ^ (-(2 * s))) * completedRiemannZeta s) ∧
    ∃ s : ℂ, 1 / 2 < s.re ∧ s.re < 1 ∧
      riemannZeta s * (1 + ((11 : ℝ) : ℂ) * ((29 : ℝ) : ℂ) ^ (-s)
        + ((29 : ℝ) : ℂ) * ((29 : ℝ) : ℂ) ^ (-(2 * s))) = 0
```

`RH_negctl_F1_all_zeros_offline`: kind `lemma`, no deps (cross-island). Title: *"Negative control F1 = ζ(s/2+3/4)ζ(s/2-1/4): P2 in Beurling form, one gamma factor, entire symmetric completion, no zero on the critical line, and infinitely many zeros with 1/2 < Re s < 5/2 (unconditional). The pole normalization is what fails."* Artifact: `examples/rvm_bridge/lean/Crux/Crux_axiso_construct.lean` (`F1_logDeriv_hasSum`, `Xi1_no_zero_on_line`, `Xi1_one_sub`, `Xi1_offline_zeros`).

```lean
theorem negctl_F1_all_offline :
    (∀ s : ℂ, 5 / 2 < s.re →
      HasSum (fun n : ℕ => (((ArithmeticFunction.vonMangoldt n / 2 *
            ((n : ℝ) ^ (-(3 / 4 : ℝ)) + (n : ℝ) ^ (1 / 4 : ℝ)) : ℝ)) : ℂ) * (n : ℂ) ^ (-(s / 2)))
        (-deriv (fun s : ℂ => riemannZeta (s / 2 + 3 / 4) * riemannZeta (s / 2 - 1 / 4)) s /
          (riemannZeta (s / 2 + 3 / 4) * riemannZeta (s / 2 - 1 / 4)))) ∧
    (∀ s : ℂ, s.re = 1 / 2 →
      (fun u : ℂ => u * (u - 1) * completedRiemannZeta₀ u + 1) (s / 2 + ((3 / 4 : ℝ) : ℂ)) *
        (fun u : ℂ => u * (u - 1) * completedRiemannZeta₀ u + 1)
          (s / 2 + (1 / 2 - ((3 / 4 : ℝ) : ℂ))) ≠ 0) ∧
    (∀ s : ℂ,
      (fun u : ℂ => u * (u - 1) * completedRiemannZeta₀ u + 1) ((1 - s) / 2 + ((3 / 4 : ℝ) : ℂ)) *
        (fun u : ℂ => u * (u - 1) * completedRiemannZeta₀ u + 1)
          ((1 - s) / 2 + (1 / 2 - ((3 / 4 : ℝ) : ℂ))) =
      (fun u : ℂ => u * (u - 1) * completedRiemannZeta₀ u + 1) (s / 2 + ((3 / 4 : ℝ) : ℂ)) *
        (fun u : ℂ => u * (u - 1) * completedRiemannZeta₀ u + 1)
          (s / 2 + (1 / 2 - ((3 / 4 : ℝ) : ℂ)))) ∧
    ∀ T : ℝ, ∃ s : ℂ, riemannZeta (s / 2 + 3 / 4) * riemannZeta (s / 2 - 1 / 4) = 0 ∧
      1 / 2 < s.re ∧ s.re < 5 / 2 ∧ T < s.im
```

**B. Targets, stated only (status `draft`).**

`RH_classP_fe_top_coeff`: NT1, kind `lemma`, no deps. Title: *"The FE of q^{s/2}P(s) pins the top coefficient of a Dirichlet polynomial on the divisors of q: P(q) = ε√q."*

```lean
theorem classP_fe_top_coeff : ∀ (q : ℕ), 0 < q → ∀ (P : ℕ → ℝ), P 1 = 1 →
    (∀ d, ¬ d ∣ q → P d = 0) → ∀ (ε : ℝ),
    (∀ s : ℂ, (q : ℂ) ^ (s / 2) * ∑ d ∈ q.divisors, (P d : ℂ) * (d : ℂ) ^ (-s)
        = ε * (q : ℂ) ^ ((1 - s) / 2) * ∑ d ∈ q.divisors, (P d : ℂ) * (d : ℂ) ^ (-(1 - s))) →
    P q = ε * Real.sqrt q
```

`RH_classP_collapse_of_periodic`: NT2, kind `milestone`, deps `RH_classP_coeff_collapse` and `RH_classP_fe_top_coeff`. Title: *"Class P (Γ(s/2) shape) collapses to ζ given only the KP99 periodicity; no Euler product assumed. STATED ONLY."*

```lean
theorem classP_collapse_of_periodic : ∀ (q : ℕ) [NeZero q] (a b : ArithmeticFunction ℝ),
    a 1 = 1 →
    a.pmul ArithmeticFunction.log = (b.pmul ArithmeticFunction.log) * a →
    (∀ n, 0 ≤ b n) →
    ∀ (A : ZMod q → ℝ), (∀ n : ℕ, 0 < n → a n = A (n : ZMod q)) →
    ∀ (ε : ℝ) (ξ : ℂ → ℂ), Differentiable ℂ ξ →
      (∀ s : ℂ, 1 < s.re → ξ s = s * (s - 1) * ((q : ℂ) / (Real.pi : ℂ)) ^ (s / 2) *
          Complex.Gamma (s / 2) * LSeries (fun n => (a n : ℂ)) s) →
      (∀ s : ℂ, ξ (1 - s) = ε * ξ s) →
      q = 1 ∧ ∀ n, 0 < n → a n = 1
```

`RH_degree_one_periodicity`: NT3, kind `milestone`, no deps. Title: *"Degree-1 periodicity for the Γ(s/2) shape with integer frequencies (the μ = 0 case of Kaczorowski-Perelli 1999): πQ² ∈ ℕ and a is periodic. STATED ONLY."*

```lean
theorem degree_one_periodicity : ∀ (a : ℕ → ℂ) (Q : ℝ), 0 < Q → a 1 = 1 →
    (∀ s : ℂ, 1 < s.re → LSeriesSummable a s) →
    ∀ (ε : ℂ) (ξ : ℂ → ℂ), Differentiable ℂ ξ →
      (∃ C c : ℝ, ∀ s : ℂ, ‖ξ s‖ ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖))) →
      (∀ s : ℂ, 1 < s.re → ξ s = s * (s - 1) * (Q : ℂ) ^ s * Complex.Gamma (s / 2) * LSeries a s) →
      (∀ s : ℂ, ξ s = ε * (starRingEnd ℂ) (ξ (1 - (starRingEnd ℂ) s))) →
      ∃ q : ℕ, 0 < q ∧ Real.pi * Q ^ 2 = q ∧ ∀ n, 0 < n → a (n + q) = a n
```

`RH_classP_collapse_beurling_q1`: NT4, kind `milestone`, no deps. Title: *"Positive Beurling-type measures on [1,∞) with ζ's exact conductor-1 FE are the integers (Theorem A / Collapse B). STATED ONLY."* It uses two auxiliary definitions, which a statement module would carry:

```lean
def BeurlingNormalized (N : MeasureTheory.Measure ℝ) : Prop :=
  N (Set.Iio 1) = 0 ∧ N {1} = 1 ∧
    ∃ C k : ℝ, ∀ X : ℝ, 1 ≤ X → N (Set.Icc 1 X) ≤ ENNReal.ofReal (C * X ^ k)

def ZetaShapeFE (q : ℝ) (N : MeasureTheory.Measure ℝ) : Prop :=
  ∃ (ε : ℂ) (ξ : ℂ → ℂ) (σ₀ : ℝ), Differentiable ℂ ξ ∧
    (∃ C c : ℝ, ∀ s : ℂ, ‖ξ s‖ ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖))) ∧
    (∀ s : ℂ, σ₀ < s.re →
      MeasureTheory.Integrable (fun x : ℝ => (x : ℂ) ^ (-s)) N ∧
      ξ s = s * (s - 1) * ((q : ℂ) / (Real.pi : ℂ)) ^ (s / 2) * Complex.Gamma (s / 2) *
        ∫ x, (x : ℂ) ^ (-s) ∂N) ∧
    ∀ s : ℂ, ξ s = ε * (starRingEnd ℂ) (ξ (1 - (starRingEnd ℂ) s))

theorem classP_collapse_beurling_q1 : ∀ N : MeasureTheory.Measure ℝ,
    BeurlingNormalized N → ZetaShapeFE 1 N →
    N = MeasureTheory.Measure.sum (fun n : ℕ => MeasureTheory.Measure.dirac ((n : ℝ) + 1))
```

**C. The conjecture, recorded but not recommended as a node.** If it is ever registered, its title must carry "CONJECTURE" the way `RH_conjecture` carries "NOT proved".

```lean
def LogPositive (N : MeasureTheory.Measure ℝ) : Prop :=
  ∃ (Pm : MeasureTheory.Measure ℝ) (σ₀ : ℝ), Pm (Set.Iic 1) = 0 ∧
    ∀ s : ℂ, σ₀ < s.re →
      MeasureTheory.Integrable (fun x : ℝ => (x : ℂ) ^ (-s)) Pm ∧
      ∫ x, (x : ℂ) ^ (-s) ∂N = Complex.exp (∫ x, (x : ℂ) ^ (-s) ∂Pm)

-- CONJECTURE-with-evidence (twisted Beurling cell)
def twisted_beurling_empty : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ N : MeasureTheory.Measure ℝ,
    BeurlingNormalized N → LogPositive N → ¬ ZetaShapeFE q N
```

**Not proposed.** The barrier seat's `RH_barrier_surgery_scope`. Its load-bearing sentences were downgraded to HEURISTIC, and the 2026-09-18 memo shows what happens to a barrier node registered on a heuristic (§3.4, item 3).

### 5.3 Program-level recommendations

1. **Ledger edits.** Record the following in `RH_BARRIER_FE_UNIFORMITY_DESIGN_2026-09-18.md` (§3) and the wall map: at degree 1 the joint cell FE + P2 is {ζ}, and FE + Euler product + a_n ≥ 0 has kernel-exact off-line zeros. So degree 1 offers no class-level lever, and any class-P argument is an argument about ζ. The class-P lane is closed as an RH route. Do not edit this memo's sources; edit the ledger.
2. **Negative-control policy.** For arguments that consume the FE plus an Euler product, prefer the kernel-exact controls to the Arb-certified Davenport-Heilbronn function:
   - ζ(s)(1+4·2^{-s}+2·4^{-s}), with zeros at Re s > 1;
   - F0, with zeros on Re s = 1;
   - W1(29,11), with a zero in the open strip.

   For arguments that consume P2 without the pole normalization, use F1 or the E8 twin. **Caveat:** none of these has a kernel-checked order-1 bound, and LiCriterion-style consumers need one. So "Li positivity fails for s(s-1)·completedF 29 11" is not yet a kernel theorem, even after the LiCriterion chain is abstracted (step two of the 2026-09-18 memo).
3. **The surgery test (HEURISTIC design rule, barrier seat).** Before investing in a lemma meant to close the wall, check whether its proof goes through verbatim for W1 (Euler product) or for W2 (RH verified below T0). If it does, the lemma cannot be the last step.
4. **Tooling.** Replace the node-sampling winding count in `telperion/src/telperion/arb_dh.py` with the whole-segment enclosure method of `research/axiso_literature/arb_winding.py`. Correct the "RIGOROUS" wording in its docstring and in `QC_DH_SCOUT.md` §4.
5. **Workflow.**
   - Give referee scores a fixed scale in the schema.
   - Rank for builds by kills first, then by normalized score.
   - Never truncate relayed payloads silently. This run lost the build records (a 120,000-character cut) and part of every seat's claims (a 14,000-character cut for referees).
   - Run a Build and skeptic pass on the barrier core, which this run skipped.
6. **Commit hygiene.** The artifacts are untracked:
   - in `arda-cl-crux`: `examples/li_positivity/lean/Crux/`, `examples/rvm_bridge/lean/Crux/`, and `research/axiso_{construct,literature,theorem}/`;
   - in `arda-closure`: `examples/class_p_barrier/`.

   Commit them with CI and AxiomGuard coverage before any registry grant. The CI placeholder-scan convention applies: prose writes "no `sorry`".

---

## 6. What was not checked

**Published inputs that nobody re-read.**

- **Kaczorowski-Perelli 1999.** No seat or referee read the paper itself. The periodicity statement was taken from Zaghloul's verbatim quotation (arXiv:1903.06145) and Perelli's survey (arXiv:1605.02354). The exact theorem number and the precise form of the periodicity of a(n)n^{iθ} still need confirming against the paper.
- **Saias-Weingartner 2009 and Hamburger 1921.** Cited through surveys and Titchmarsh, not re-derived.
- **Growth hypotheses.** Nobody verified the Kahane-Mandelbrojt/Bochner growth hypotheses (their A3) against "finite order" for the step "FE implies distributional Poisson identity" in Theorem A, Collapse B and C5.
- **Diamond-Montgomery-Vorhauer 2006.** The primary source was not read, here or in the 2026-09-18 memo. The quotes come through Broucke-Debruyne-Vindas.

**Paper proofs checked only partly.** The writer did not re-derive them line by line. The writer did check:

- the consistency of the three Poisson normalizations;
- the Fejér identity, by direct summation with a tail bound;
- the derivation "FE implies |P(q)| = √q";
- the NT2 proof route;
- the Hermite certificate values (h(0) = 0.88; H4 > 100 for y² ≥ 2π).

Beyond that, the correctness referees are the only line-by-line check.

**Referee coverage gaps from truncation.** None of the following was seen by a referee:

- barrier claims 8, 9 and 10, and most of claim 7's non-vacuity paragraph;
- construct claims 10 and 11, and the end of claim 9;
- theorem C10 and most of C9;
- each seat's buildable-now section and open problems;
- the summaries of the theorem and barrier seats, and most of the literature summary.

**Novelty.** Novelty was never settled.

- The referees ran targeted searches: Beurling 1951, Kahane-Mandelbrojt 1958, Burnol 2011, Dixit 2020, Hilberdink-Lapidus 2006 and Perelli's survey were read.
- No exhaustive search was made and no expert was consulted.
- The Hecke G(λ) corollary suggested by construct referee 1 was not checked. It says that weight-1/2 forms for λ > 2 cannot have nonnegative coefficients once the low coefficients vanish.

**The barrier core.** It was never attacked by a skeptic. Its numerics are float64:

- the 3-4-1 sweeps (Lipschitz-safe grids, but floating point);
- W2's zero counts and zero locations;
- the fooling-lemma instances.

The W2 existence argument (Hurwitz, a local torus model, Rouché) was refereed only in outline. Its H7b clause is conditional on RH for ζ below T0.

**Kernel gaps inside the builds.**

- Finite or order-1 growth of Xi0, Xi1, XiE8 and completedF.
- The E8 identification Σ_{v∈E8∖0} |v|^{-2u} = 240ζ(u)ζ(u-3).
- The root number of L(s, χ₅), which is needed to place the DH-type mixture in S#_1.
- The existence of b in the sharpness theorems.
- The link from `nc_F_vanishes` to a9's Dirichlet series.
- The T log T count of F1's off-line zeros.
- The Euler product over √p for F1.
- F1's gamma factor. The seat states it as Γ(s/2 + 3/4) with ε = -1; the file uses Γ_ℂ(s/2 - 1/4) with ε = +1. The conversion is algebra that was not stated in Lean.

**Certificates outside the kernel.**

- Arb certificates: the first ζ zero, the E8 off-line zero, the mixture's off-line zeros, the DH crown box, and the theta identity. Rigorous, but not kernel.
- DH-type zeros in σ > 1: not certified by anything.
- The integer-frequency stress test: floating-point local optimization over finite ranges.

**Scripts this writer did not re-run.** `integer_case_stress.py` (the literature skeptic ran it), the construct seat's original float scripts in `/private/tmp/claude-0/axiso-construct/` (superseded by the build's Arb checks N3-N6), and the seat-phase scratch scripts in `scratchpad/classP/`.

**CI.** Nothing in this run has been through CI. Every artifact is uncommitted. The writer's verification files live in an ephemeral scratch directory:

- `.../scratchpad/axiso_doc_verify/`: snapshots `T.lean`, `L.lean`, `C.lean`, `B.lean` with sha256 as in §3.1 and §3.3; the restatement files `T2`, `L2`, `C2`, `B2`; the node files `L3`, `C3`, `B3`; `Stmts.lean`; the re-run outputs; `fejer_sum.py`; `journal_results.json`.
- Reproduce from the pinned islands with the commands in §3.2.

**The Riemann Hypothesis.** It remains open. `conjecture1_proved = False`.
