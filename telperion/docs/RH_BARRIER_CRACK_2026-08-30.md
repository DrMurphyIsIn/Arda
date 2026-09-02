# Cracking the finite/infinite barrier to RH: where the belief fails and where the real obstruction lives

*A graded research position. Every claim is marked PROVEN / PARTIAL / HEURISTIC / REFUTED / FOLKLORE, and cracks are graded ALIVE / SEMI-ALIVE / MIRAGE. No proof of RH is claimed.*

---

## (1) The barrier itself: theorem, heuristic, or belief?

**Verdict: "No finite / elementary / certificate proof of RH can exist" is an UNFOUNDED BELIEF — neither a theorem nor a well-supported heuristic.**

The distinction that settles this is complexity-theoretic. For P vs NP we *earned* pessimism with genuine metatheorems: **relativization** (Baker–Gill–Solovay 1975), **natural proofs** (Razborov–Rudich, *JCSS* 1997), and **algebrization** (Aaronson–Wigderson 2008). Each *proves* that an entire class of proof techniques cannot resolve the problem. **No analogue exists for RH.** There is no published theorem excluding elementary, finitary, or certificate-style methods from proving RH. The resistance is *purely empirical* — ~170 years of failed attempts, which is evidence of difficulty, not a proof of impossibility. Conflating the two is precisely the crank move.

Worse for the belief, the logical facts cut the *opposite* way:

- **RH is Π₁ (arithmetical). PROVEN** (Kreisel 1958; concretized by Robin 1984 and Lagarias 2002 as elementary inequalities on a single integer; Diophantine form via DMR 1976; explicit 5,372-state halting-iff-false Turing machine, Aaronson–Yedidia 2016, arXiv:1605.04343). Π₁ is the *most* finite-proof-friendly class: a false Π₁ sentence is refutable by a finite witness. RH *is* a finite-certificate condition — a counterexample is a finite, mechanically checkable object.
- **The one historical precedent for "no elementary proof" folklore was REFUTED.** Hardy (1921) argued no elementary proof of the Prime Number Theorem could exist — opinion, never a theorem. Erdős and Selberg (1949) gave one. The folklore was empirically falsified.

Honest counter-caveats, so this is not overclaimed: PA-provability of RH is **OPEN** (no theorem either way); no reverse-math (RCA₀/WKL₀/ACA₀) classification of RH exists; and arXiv preprints asserting RH is "independent/unprovable" are **non-vetted, crank-adjacent**. But none of this rescues the belief. **The wall was never built.**

---

## (2) The genuine cracks, graded

### CRACK A — Jensen–Pólya uniformity (GORZ 2019). **ALIVE — the sharpest crack.**

Griffin–Ono–Rolen–Zagier (*PNAS* 2019) proved **unconditionally**: for each fixed degree *d*, the Jensen polynomials J^{d,n} of Riemann's Ξ are hyperbolic for all large *n*, and the renormalized J^{d,n} converge to the **Hermite polynomials** H_d — hyperbolic *with a spectral gap*. Since RH ⟺ hyperbolicity for all (*d,n*) (Pólya), **finite structure genuinely captures RH degree-by-degree**, and *d* ≤ 8 is fully verified. This is a real counterexample to the *spirit* of the belief.

**Precise missing piece:** the threshold N(*d*) is not effective/uniform. The entire residual is one **scalar analytic error term**, controlled for fixed *d* as *n*→∞ but degrading as *d*→*n*, where the full arithmetic of the zeros re-enters. An effective-enough uniform-in-*d* bound *is* RH. This is the most *localized* obstruction in the literature — a finite hyperbolic skeleton (Hermite + gap) plus a single named estimate — but the estimate is governed by the same zero-density data as everything else.

### CRACK B — Li / Weil positivity as PSD-on-a-growing-chain. **SEMI-ALIVE.**

Li's criterion (1997; Bombieri–Lagarias 1999): RH ⟺ λ_n ≥ 0 ∀n, with λ_n = Σ_ρ[1−(1−1/ρ)^n] finite arithmetic sums. As a **bare sequence this is DEAD for induction**: a single off-line zero forces λ_n < 0 infinitely often *but with the negativity pushable arbitrarily far out* — failure is **delocalized in n**, so no finite window certifies anything and no naive positivity-preserving recurrence exists.

The **live** version: λ_n *is* the Weil quadratic form (Weil 1952) evaluated on the Li basis — i.e. PSD-ness of a Gram/Hankel matrix on a **growing chain of finite-dimensional subspaces**, where Schur-complement/Cholesky recursions *are* positivity-preserving *when they hold*. That is the right shape for a self-propagating certificate. **Missing piece:** "the Schur complements stay ≥ 0" ⟺ RH, and no unconditional bound on the entries (the σ_k power sums / secondary-zeta values) is known.

### CRACK C — Connes noncommutative-geometry / Weil positivity / prolate operator. **SEMI-ALIVE (deepest, but not a finitization).**

RH ⟺ global Weil positivity of the explicit-formula functional (Connes 1999). Genuine **PARTIAL** progress: Connes–Consani (*Selecta* 2021) **proved** the archimedean-place positivity; Connes–Consani–Moscovici (*Ann. Funct. Anal.* 2024, arXiv:2310.18423) exhibit a genuinely self-adjoint **prolate spheroidal wave operator** whose spectrum tracks low-lying zeros — the closest thing to a non-circular Hilbert–Pólya operator.

**Missing piece:** the **p-adic / arithmetic places contribute indefinite-sign terms**; controlling them against the proven archimedean positivity is open and equivalent to RH. The spectrum is inherently infinite-dimensional, so this is not a *finite* mechanism — but it is where a single structural positivity, partially proven, actually lives.

### CRACK D — de Bruijn–Newman Λ = 0 (Rodgers–Tao). **SEMI-ALIVE as a reframing, MIRAGE as a mechanism.**

RH ⟺ Λ ≤ 0; Rodgers–Tao (*Forum Math. Pi* 2020) **PROVED** Λ ≥ 0; Polymath15 (2019) gave Λ ≤ 0.2. So RH is rigorously an **inequality attained with equality** — "barely true if true" (Newman) is now a theorem, and RH = the sign of one real number. There is even a proven no-go: heat-flow monotonicity **cannot cross Λ = 0** (a one-way ratchet), a genuine "smooth method plateaus above the tie" fact. **But Λ ≤ 0 *is* RH** — the reframing removes nothing, and the number is exactly as hard as RH.

### MIRAGES — name them.

- **Bender–Brody–Müller (2017):** self-adjointness *assumed* not proven; the boundary condition pinning eigenvalues to zeros *already encodes ζ* (circular); the metric completion kills the eigenfunctions (arXiv:1704.02644). **MIRAGE.**
- **de Branges strong form:** the required positivity is **REFUTED** (Conrey–Li, *IMRN* 2000). De Branges *spaces* remain a legitimate toolkit; the route to RH is dead.
- **Bost–Connes:** encodes ζ as a *partition function*, not its zeros as a spectrum. **NIL for RH**; conflating it with Hilbert–Pólya is folklore-adjacent overclaiming.
- **Berry–Keating xp:** reproduces only the *average* counting function (PROVEN); the true fluctuating zeros are HEURISTIC. **MIRAGE as an operator program, high as intuition.**
- **Guth–Maynard 2024** (arXiv:2405.20552, real zero-density improvement, first in ~80 years): a *quantitative analytic estimate bounded away from exactness by construction*. Density theorems cannot reach "no off-line zeros." **Irrelevant to finitization**; mild negative evidence that SOTA progress is still purely analytic.
- **RG / self-similarity "proofs"; motivic/prismatic/condensed cohomology:** the former is **FOLKLORE** (statistics ≠ forcing); the latter is real infrastructure (Bhatt–Scholze) with **no archimedean ζ-spectral interpretation** and no RH consequence.

---

## (3) The sharpest single statement of the real obstruction

**The primes are the invariant hard core.** Weil's explicit formula splits the RH-equivalent positivity into an **archimedean (∞) piece + prime (p-adic) pieces**. Connes–Consani **proved the archimedean piece positive (2021)**. Every prime piece has **indefinite sign** and resists control — and *this same wall wears every costume*: Berry–Keating cannot produce the fluctuation (=prime) term; BBM smuggles ζ into a boundary condition; de Branges' prime-sensitive positivity is provably false; Bost–Connes sidesteps the zeros; the GORZ error term (Crack A) and Li's σ_k power sums (Crack B) *are* the prime data re-imported at the inductive step.

The honest one-liner, sharper than "no finite structure found": **there is no known spectral/geometric object over ℚ on which the prime contribution to Weil positivity is sign-definite** — the exact ingredient Frobenius + Hodge-index supplies for free over 𝔽_q.

---

## (4) The function-field lesson: the one missing ingredient

Over 𝔽_q, RH is a **PROVEN, finite** statement — |α_i| = √q for 2g explicit algebraic numbers (Weil 1948 for curves; Deligne, *Weil I* 1974, *Weil II* 1980). Three finite/algebraic ingredients force it:

1. **Frobenius as an operator on finite-dimensional cohomology** H¹_ét — the zeros *are literally eigenvalues*. (Hilbert–Pólya, here a theorem.)
2. **Poincaré self-duality** = the functional equation as an honest pairing (α_i ↦ q/α_i).
3. **A positivity theorem on a genuine surface** — Hodge-index / Castelnuovo on C × C. *This is the actual RH bound, and it is a positivity.*

Over ℚ, **all three are absent**: Spec ℤ is 1-dimensional; the sought surface "Spec ℤ ×_{𝔽₁} Spec ℤ" **does not exist as a scheme**; and the zeros are *infinitely many*, so any spectral object is **infinite-dimensional** (H¹ → Hilbert space). The finiteness is exactly what is lost.

**Programs manufacturing the missing ingredient — all PROGRAMS, no RH consequence:**
- **Deninger** — a foliated dynamical system with the right Lefschetz trace formula. The space is conjectural.
- **Connes** — the adele-class-space trace formula (Crack C); reduces to a positivity equivalent to RH, *without the surface that made Weil's positivity provable*.
- **Connes–Consani 𝔽₁ / scaling site** — genuinely built objects (arithmetic site, scaling site, a Riemann–Roch formula) making "Spec ℤ over 𝔽₁" partially concrete. **The most alive of the three**, and the honest reason the belief is empirical: **no Hodge-index positivity has been proven on these sites**, but no one has shown it *cannot* be.

---

## (5) The "RH-as-arithmetic-tie" thesis (Brualdi–Goldwasser analogy)

**Verdict: PARTIALLY survives — the tie half is earned and theorem-backed; the *arithmetic* half FAILS.**

**Survives (ALIVE):** RH genuinely *is* tie-shaped. Λ = 0 with the proven floor Λ ≥ 0 makes "an inequality attained with equality" a **theorem**, not a metaphor. And there is a real "smooth certificate plateaus above the tie" no-go: heat-flow monotonicity provably cannot cross Λ = 0. That much rhymes exactly with the BG experience where no finite-degree SOS closes a rational tie.

**Fails (MIRAGE) — the escalation to *arithmetic/integrality*:**

1. **No exact rational tie value exists at Λ = 0.** BG had a *named* rational coincidence (64·243·23 = 621·576) with an identifiable 23-adic obstruction. Λ = 0 is a **threshold of a real dynamical parameter**, not a value forced by an arithmetic identity; there is no Diophantine equation whose (in)solvability is Λ = 0. The thesis borrows the *word* "tie" but cannot exhibit the *arithmetic object*.
2. **BG's tie is FINITE; RH's is INFINITE.** BG lives on fixed finite graphs where "no degree-*d* SOS closes it" is itself a finite, provable fact. Λ = 0 is a statement about all zeros to arbitrary height — there is no finite object above which a certificate plateaus, only an infinite family. The analogy's premise fails to transfer.
3. **The mainstream heuristic points the *other* way — analytic/spectral, not arithmetic.** The reason RH is "barely true" is best read as **Montgomery–Odlyzko GUE rigidity** (pair correlation proven under RH for restricted test functions; Rudnick–Sarnak 1996). Rodgers–Tao's Λ ≥ 0 itself runs through zero-*spacing* rigidity, not any p-adic input. The proven no-go identifies the missing ingredient as **analytic** (control of high zeros), not p-adic.

**What would test it:** exhibit a *named arithmetic invariant* (a congruence, a p-adic valuation, a Diophantine object) that provably controls the sign of the prime-place contribution to Weil positivity — i.e. an integrality fact that forces Λ = 0. Absent such an object, "arithmetic tie" is a heuristic hope, explicitly separate from the proven Λ = 0 ⟺ RH tie.

---

## (6) The single most promising bold direction, with honest odds

**Direction: push CRACK A (GORZ) and CRACK B (Weil–Hankel PSD) together — treat the uniform-in-degree Hermite error term as a Schur-complement positivity on the growing Li–Weil Gram chain, and seek an *unconditional* entry bound (on the σ_k / secondary-zeta values) that propagates PSD-ness.**

Why this over the others: it is the *only* pairing where both halves are (i) genuinely finite per stage, (ii) proven partially (Hermite hyperbolicity with a gap; archimedean Weil positivity), and (iii) reduce the whole of RH to a **single, named, localized scalar estimate** rather than to an unspecified operator or a nonexistent surface. Crack C is deeper but inherently infinite-dimensional; Crack D removes nothing; the 𝔽₁ route needs an object no one can yet build.

**Honest odds:** low. The entry bound that would make the Schur complements stay ≥ 0 is *equivalent to RH* by the same explicit-formula decomposition that defeats every other route — the prime contribution's indefinite sign re-enters at exactly the inductive step. The bold bet is that the *Hermite gap* (a finite spectral margin, absent from bare-sequence Li) gives enough slack to absorb the prime oscillation for a *uniform* range of degrees where no prior method had margin to spare. That is a real, previously-unavailable lever — and still a long shot. Call it a lead worth pressing, not a proof in waiting.

---

*This rejects "the barrier is necessary"; it does not prove RH.* `conjecture1_proved = False`.