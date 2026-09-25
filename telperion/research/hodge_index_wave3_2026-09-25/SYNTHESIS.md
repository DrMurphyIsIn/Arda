# Hodge index for Spec Z, wave 3: synthesis of converse, mollifier, sonine, randomeuler and thetapf, cross-referenced with waves 1–2

**Bottom line.** None of the five wave-3 angles survives as a mechanism. That makes fifteen angles across three waves with no mechanism left standing. The five proposers and five independent skeptics agree on every verdict, and they reproduced the key numbers with different code.

Wave 3 still changes the combined picture in four specific ways:

1. **Where the nonlinearity has to live.** It moves from "the Euler product" to the Hecke-eigen / multiplicity-one condition together with reciprocity.
2. **The local-to-global gap becomes a number.** It turns into a conductor quantity that can be computed.
3. **The pole block is isolated.** The early failures of the counterfeit E sit in the pole direction.
4. **The linearity barrier is corrected.** D is only a weak counterfeit; E is the one that matters.

`conjecture1_proved = False`.

## 1. What died, and why (one line each)

- **converse (twisted-FE family).** E is the theta series of x²+5y², a weight-1 form of level 20 with character χ₋₂₀. It therefore satisfies every coprime twisted functional equation: the root-number identity holds for 62 primitive characters, with error below 2e−14. Beyond that:
  - The block form of the family is just the conjunction of its members' positivity.
  - The averaged form is provably blind once r > x, and it hides E: +0.345 at x = 45, where E alone is −0.655.
- **mollifier.** W_{LM} = W_L + W_M, and the mollified zero sum equals Q_X(f\*μ_M). So "mollified Weil positivity" is W restricted to a subspace, which can only delay detection: E's own mollifier moves its failure from 19.9 to about 105–110. The single nonlinear step, Jensen applied to 1/L, only reaches depth ½+δ at mollifier length y ~ exp(c/δ).
- **sonine (S-adelic Sonine / Toeplitz).** Each local symbol is ρ_p = h̄_p/h_p with h_p an invertible outer function, so Son_S = H_S · Son_∞. The finite primes change only the metric, never the structure. The "Sonin trace ≥ 0" step is a tautology, and on the window the semilocal form is exactly the pole-free W(x).
- **randomeuler (typicality).** P(pos) → 0 is exactly what GRH plus counting predicts: each ±1 vertex is some χ_d with |d| much larger than 20. Two of its "findings" are not new:
  - The conductor-shift identity is the explicit formula's log q·‖f‖² term.
  - The claim sup_x ℓ = log q is GRH in the ≤ direction and trivial in the ≥ direction.
- **thetapf (total positivity of the theta kernel).** By Schoenberg, PF_∞ would make Ξ zero-free, so it cannot hold. The kernel Φ_F is linear in the coefficients. Its PF order tracks conductor and Gamma factor, not arithmetic:
  - ζ_K is not PF₂.
  - D is PF₂ even though it violates RH.
  - The genuine L(χ₋₁₉) is not even PF₁.

  The Edrei moment form is equivalent to RH, and in its tail E and ζ_K agree to 1e−54.

Each fits one of the three wave-2 death classes: linear/asymptotic (converse, thetapf), circular (thetapf's Edrei form, randomeuler's C1) or restriction/tautology (mollifier, sonine).

## 2. Survivors: true statements, ranked by (value if true) × (tractability)

| # | Statement | Status | Gap | RH in disguise? |
|---|---|---|---|---|
| 1 | **Reciprocity kills local counterfeits in the pole class.** A degree-2 datum with a pole and Γ_S reciprocity must be ζ·L(χ), so α_p = 1 at every p. The wave-1 LEB witness (α₃ = β₃ = −1) and the Connes–Consani (CC) witness {3:−, 7:+, 11:−, 13:+} are therefore *not realizable*. What remains is the ±1/unitary cube c(p^k) = log p(1+ε_p^k). Some of its vertices are already negative at conductor 20 by x = 14: P(pos) = 0.875 at x = 14 and 0.66 at x = 20 with ramified primes fixed. Each vertex is a genuine χ_d of large \|d\|. The GRH-consistency check ℓ(ε,x) ≤ log d_min(ε) holds with 0 violations on 4608 vertices, and is tight only for small \|d\|. | Numerical (sonine, randomeuler, both skeptics). | Arb certification; an unconditional bound (see §3). | The all-x statement is equivalent to GRH for the family (§3). |
| 2 | **Pole-block diagnosis.** On the pole-free CC class (ĝ(0) = ĝ(±i/2) = 0), E's horizon moves from 19.82 to (23.5, 24]. ζ_K's margins there are O(1) (about 2 at x = 11–14, ≥ 0.9 at 24), against about 1e−3 on the full class. The LEB witness's negativity at x = 6 comes entirely from the pole direction (+2.22 on the CC class). | Reproduced independently. | Formal Schur-complement statement. | No. This is anatomy, but it supports a literal Hodge split into a hyperbolic pole block plus a primitive class, consistent with wave 1's Markov form and its Schur scalar. |
| 3 | **Converse-theorem barrier and counterfeit hierarchy.** No criterion built from twisted functional equations or twist averages can separate ζ_K from E. D is caught *linearly*: the twist-compatibility of its self-duality fails exactly for r ≡ ±2 mod 5. E is caught only by the quadratic Hecke relations (a(6) = 2 but a(2)a(3) = 0). | Proved at finite level via the root-number identity; numerics reproduced. | Lean lemma: w(χ)w(χχ₋₂₀) = w(χχ₋₄)w(χχ₅) with matching parity sets. | No. It is a barrier. |
| 4 | **New barriers for the ledger.** Mollifier restriction lemma M1 with its depth barrier y ~ e^{c/δ}; Sonine outer-multiplier lemma; TP-of-theta-kernel witnesses (Φ_E(0) = −0.07502, ζ_K log-concavity failure −1.294e−5, D's PF₃ minor, χ₋₁₉ PF₁ failure). | Reproduced. | Arb/Lean. | No. |

**Correction to the barrier statements.** The linearity barrier should name E as its reference counterfeit. E satisfies every linear identity (functional equation, twisted functional equations, Voronoi) satisfied by elements of the Hecke-stable space M₁(Γ₀(20), χ₋₂₀). D fails the twisted-FE identities, so it is only a weak counterfeit.

**What wave 3 did not test.** EFW (wave 1) and the kernel-split semilocal SDP KS-PSHR (wave 2) remain untested. Item 1 changes how EFW should be posed. In the pole class, its constraint (i) should be "ζ × a degree-1 unitary Euler datum", not free degree-2 Satake data. The free version is already known to be negative through non-realizable data.

## 3. A criterion that fails for counterfeits by construction

Items 1–3 combine into one precise reformulation. The ingredients:

- Let ε be a unitary pattern on the primes p ≤ x, with ramified primes fixed.
- Let c_ε(p^k) = log p (1 + ε_p^k). This is a pole-class, reciprocity-shaped datum.
- Let ℓ(ε, x) := −λ_min Q_x(c_ε; q=1).
- Let N_min(ε) be the least conductor of a Dirichlet character χ with χ(p) = ε_p for all p ≤ x (∞ if there is none).

> **Reciprocity–Conductor Inequality RCI(x):** for every pattern ε, ℓ(ε, x) ≤ log N_min(ε).

**Equivalence.** The window form Q_x sees only n ≤ x, so Q_x for χ equals Q_x(c_ε; cond χ). The conductor-shift identity then gives:

- RCI(x) for all x ⇔ W(x) for ζ·L(χ) for every Dirichlet χ and every x, i.e. RH plus GRH for Dirichlet L-functions.
- For real patterns, the ⇒ direction under GRH is exactly how Ankeny/Bach-type least-nonresidue bounds are proved from explicit-formula positivity. That the converse packaging is new is my inference, not checked against the literature.

**Why it is counterfeit-sensitive by construction.** E and D are not of the form c_ε: E violates the Hecke relations at n = 6, and D is not an Euler product. So they are excluded at the input, not through their zeros. The criterion turns Weil positivity into an *arithmetic* statement: a sign pattern that makes Q_x very negative must need a large conductor to be realized. That makes it a Linnik/least-nonresidue-type question. Unconditional tools exist there (Burgess, large sieve, Vinogradov), though they are far too weak today to give RCI.

**Honest status.** RCI is RH (plus GRH for Dirichlet L-functions) restated, not a proof route by itself. Two things make it the first reformulation in three waves that is both counterfeit-sensitive by construction and finitely testable:

- The randomeuler ledger is already a test of it at x = 25 and 40.
- The quantity to study is the slack gap(x) = min over ε of [log N_min(ε) − ℓ(ε, x)]. If there is an unconditional reason why this stays ≥ 0 at small x, it would be a large-sieve-type statement coupling Euler data to the functional equation across all primes at once. That is exactly the shape wave 1 said a proof must take.

## 4. Build lanes (two)

**Lane A: certified barrier ledger (kernel-checkable; wave 1 and 2 items plus these).**

- Root-number lemma for the converse barrier: finite Gauss-sum identities, decidable.
- CC local-symbol witness at x = 14 (−0.49 at N = 20). Its large margin at small N makes it cheap in Arb.
- Theta-kernel witnesses: Φ_E(0) < 0, the ζ_K PF₂ witness, the D PF₃ minor.
- E's sign change on [19.8, 19.9].
- **Close the D control.** Three waves and about fifteen teams have all hit float64 near-null noise for D beyond x ≈ 20. So far only the location of D's off-line zero has been confirmed. The x_D ≈ 31 threshold is unverified by anyone, and every "fails for D" claim rests on it. Rerun D at x ∈ {28, 31, 35} in mpmath/Arb with dps ≥ 40, and with enough modes that the top frequency exceeds 85.7.

**Lane B: RCI gap experiment, merged with EFW and KS-PSHR.**

1. At q = 20 in the pole class, enumerate ±1 patterns on primes ≤ x for x ∈ [10, 40]. Compute ℓ(ε, x) with the validated engine, and compute N_min(ε) by CRT/character search. Plot gap(x).
2. Controls: ζ_K must be tight (gap → 0⁺). E and D must fall outside the domain.
3. Re-run EFW with the corrected constraint (i), ζ × degree-1, together with the truncated Guinand–Weil identity. Ask whether the functional-equation truncation alone already excludes the negative vertices, or whether their exclusion needs the conductor.
4. If an SDP solver is installed, add the KS-PSHR feasibility check at the same points.

Lane B's outcome is informative either way. Either a finite truncation of the functional equation sees reciprocity, or positivity at finite x is carried entirely by the conductor lower bound, i.e. by Linnik-type arithmetic.

## 5. Bottom line

| Question | Estimate |
|---|---|
| Any wave-3 angle leads to RH | < 0.3% |
| All fifteen angles combined lead to RH | < 0.5% (unchanged) |
| Lane A kernel-certified within weeks | about 65% |
| D control resolved in Arb | about 80% |
| Lane B gives a clean, reproducible gap(x) curve with ζ_K tight | about 70% |
| That curve suggests a provable unconditional mechanism | about 2–4% |

What wave 3 adds is precision, not a proof:

- The separating input is Hecke-eigen/multiplicity one plus reciprocity, not "Euler shape" and not functional equations.
- E's early failures are pole-block phenomena.
- The local-to-global gap is a conductor.

A Hodge index theorem for Spec Z, if it exists, would have to be an inequality that reads a prime sign pattern together with the conductor needed to realize it. RCI is that statement in equivalent form, and Lane B is how to probe whether it has finite-scale structure.

Citations marked unverified in the reports (Conrey–Farmer 1995, Booker 2019, Bach, Low 1968, Mestre 1986) were not re-checked; the web-search budget was exhausted in all ten wave-3 runs. The verified ones are Connes–Consani arXiv:2006.13771 and 2106.01715, Michalowski arXiv:2602.20313 and 2607.16795, Harper arXiv:1703.06654, Bettin–Conrey–Farmer arXiv:1211.5191, and Burnol math/0407443 and math/0112254. Scripts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/`.