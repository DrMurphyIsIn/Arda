# Verification of two flagged literature claims in RH_ROUTES_ROADMAP_2026-09-16.md

Date: 2026-09-17. Scope: literature/citation accuracy only. Nothing here is or claims to be progress on RH.
Method: primary sources fetched and quoted (arXiv abstracts/HTML, the Polymath15 PDF text extracted locally with pdftotext, Tao's blog, GitHub repos, journal pages). Page/line references to the Polymath15 paper are to the arXiv v1 PDF of 1904.12438.

---

## CLAIM 1 — de Bruijn–Newman cost curve and "Gomila 2026"

**VERDICT: PARTLY INACCURATE.** The barrier formula, the P15 numbers (X ≈ 6·10^10, t₀ = y₀ = 0.2 ⇒ Λ ≤ 0.22), the Platt–Trudgian ⇒ Λ ≤ 0.2 step, Ki–Kim–Lee Λ < 1/2, and Rodgers–Tao's venue are all ACCURATE. Four specific corrections: (1) the brief's arXiv number 1904.12010 is wrong (that is a hyperbolic-manifold paper); Polymath15 is **arXiv:1904.12438**. (2) The Gomila bound is real, the arithmetic checks exactly, and it is NOT merely a "blog computation": it is a GitHub audit repository with 3,149,013 interval certificates, a 22-page release PDF, and an independent human review by Dan Romik. It is, however, **not peer-reviewed / not journal-published**, so the roadmap's refusal to use it as a sound anchor is the right posture. (3) A second, independent, also-unreviewed AI-assisted computation (Stefan Gordon, 2026) claims **Λ ≤ 0.1577 < 0.158** at the same Platt–Trudgian height. (4) The "single-anchor extrapolation" complaint is wrong in a different way: the peer-reviewed P15 paper itself contains a **12-row conditional table (Table 1, §10)** from Λ ≤ 0.21 down to Λ ≤ 0.10, which is the correct multi-point anchor for the cost curve, and it gives C ≈ 5.0–5.9 (natural-log, T-based), not 4.7–5.0. The "ninth thread warns estimates may fail below ~0.1" sentence is not supported by the ninth thread; the limit discussed there is about going below 0.22 at X ≈ 6·10^10.

### (a) The Polymath15 barrier theorem — exact statement

Paper: D.H.J. Polymath, "Effective approximation of heat flow evolution of the Riemann ξ function, and a new upper bound for the de Bruijn-Newman constant", Res. Math. Sci. 6 (2019), art. 31; **arXiv:1904.12438** (https://arxiv.org/abs/1904.12438). NOTE: the brief cited arXiv:1904.12010, which resolves to Huang–Jang–Martin, "Mass rigidity for hyperbolic manifolds" (CMP) — wrong identifier.

Theorem 1.1 (p. 2): "We have Λ ≤ 0.22."

Theorem 1.2 (Upper bound criterion), p. 2, quoted verbatim from the PDF text:
> Suppose that t₀, X > 0 and 0 < y₀ ≤ 1 obey the following hypotheses:
> (i) (Numerical verification of RH at initial time 0) There are no zeroes ζ(σ + iT) = 0 with (1+y₀)/2 ≤ σ ≤ 1 and 0 ≤ T ≤ X/2.
> (ii) (Asymptotic zero-free region at final time t₀) There are no zeroes H_{t₀}(x + iy) = 0 with x ≥ X + √(1 − y₀²) and y₀ ≤ y ≤ √(1 − 2t₀).
> (iii) (Barrier at intermediate times) There are no zeroes H_t(x + iy) = 0 with X ≤ x ≤ X + √(1 − y₀²), √(y₀² + 2(t₀ − t)) ≤ y ≤ √(1 − 2t), and 0 ≤ t ≤ t₀.
> Then Λ ≤ t₀ + ½ y₀².

So the form **Λ ≤ t₀ + y₀²/2 is correct**, with the conditions above. Two details the roadmap glosses: hypothesis (i) needs RH only up to height **X/2** (not X), and only in the strip σ ≥ (1+y₀)/2; and hypothesis (ii) is a zero-free region for H_{t₀} in the whole half-plane x ≥ X + √(1−y₀²) (the "canopy" to the right of the barrier), which is what the effective Riemann–Siegel estimates (Theorem 1.3, valid in the region (5): 0 < t ≤ 1/2, 0 ≤ y ≤ 1, x ≥ 200) plus Euler-mollifier bounds have to certify. The paper also says (p. 3) "In practice, we have found it convenient numerically to replace the barrier region in Theorem 1.2 with the larger and simpler region X ≤ x ≤ X + 1; y₀ ≤ y ≤ 1; 0 ≤ t ≤ t₀."

Numbers for Theorem 1.1 (p. 3 and §8.1, p. ~50): "We will obtain Theorem 1.1 by applying Theorem 1.2 with the specific numerical choices t₀ = 0.2, X = 6 × 10^10 + 83952 − 0.5, and y₀ = 0.2." Hence Λ ≤ 0.2 + 0.02 = 0.22. Hypothesis (i) is discharged by Platt (Math. Comp. 86 (2017)), RH verified to 3.06·10^10 (§8.2). Also p. 3: "The choices t₀ = 0.2, y₀ = 0.2 are then close to the limit of our ability to numerically verify hypothesis (ii) for this choice of X. (... hypothesis (iii) ... does not present the main bottleneck ...) Further upper bounds to Λ can be obtained if one assumes the Riemann hypothesis to hold up to larger heights than that in [18]: see Section 10."

Platt–Trudgian ⇒ Λ ≤ 0.2: P15 §10 Table 1 ("Conditional Λ Results"), row 2: X = 5×10^12 + 194858, t₀ = 0.186, y₀ = 0.16733, Λ = 0.20 — conditional on RH to height X/2 ≈ 2.5·10^12. Platt–Trudgian, "The Riemann hypothesis is true up to 3·10^12", Bull. LMS 53 (2021) 792–797, doi:10.1112/blms.12460, arXiv:2004.09765 (abstract: all zeros with 0 < γ ≤ 3·10^12 have β = 1/2; the Gomila repo quotes the precise height T_PT = 3,000,175,332,800) supplies hypothesis (i) for that row, so Λ ≤ 0.2 became unconditional in 2020. Wikipedia's DBN page records this as "further slightly improved in April 2020 by Platt and Trudgian to Λ ≤ 0.2" (https://en.wikipedia.org/wiki/De_Bruijn%E2%80%93Newman_constant). The PT abstract itself does not mention Λ; the deduction is P15 Table 1 + PT. **Roadmap statement accurate.**

### (b) "Gomila 2026", Λ ≤ 0.1787854 — found

- Author: **Jude Gomila** (not an academic number theorist; entrepreneur). Blog post "Λ ≤ 0.1787854 — a new bound for the de Bruijn–Newman constant, explained", dated 19 Aug 2026: https://www.judegomila.com/posts/riemann-lambda-0.1787854
- Audit repository: https://github.com/judegomila/dbn-lambda-01787854-candidate-audit (MIT code / CC-BY-4.0 docs), release PDF `gomila_dbn_lambda_01787854_release.pdf` dated 20 Aug 2026, pinned to commit 6222740e. Byline "Jude Gomila, with thanks to Dan Romik and Max Atkin".
- Parameters (quoted from repo README): "X = 6000000185827", "t₀ = 129/800 = 0.16125", "y₀² = 87677/2500000 = 0.0350708", "t₀ + y₀²/2 = 893927/5000000", i.e. "Λ ≤ 893927/5000000 = 0.1787854".
- **Arithmetic check: 129/800 + 87677/5,000,000 = 0.16125 + 0.0175354 = 0.1787854 exactly (= 893927/5,000,000). Checks out.** Height check: X/2 = 3,000,000,092,913.5 ≤ T_PT = 3,000,175,332,800, margin 175,239,886.5 — matches the repo's stated "exact margin of 175,239,886.5".
- Method: instantiates P15 Theorems 1.2 and 1.3 ("Polymath 15's Theorem 1.2 says: if the three hypotheses below hold, then Λ ≤ t₀ + y₀²/2"), hypothesis (i) from Platt–Trudgian, hypotheses (ii)/(iii) from "3,149,013 certified inequalities" in FLINT/Arb ball arithmetic with Python interval cross-checks.
- Review status (quoted): "This has not yet been peer reviewed." / "computer-assisted proof awaiting journal review". Dan Romik is credited as independent reviewer who "verified the analytic lemmas and reworked the material into journal-grade manuscripts"; an "adversarial AI audit panel" is also cited. No Lean formalization in this repo.
- The blog also mentions a companion retuned lane reaching 0.1782354 at the same height (not independently reviewed).
- **Second independent claim (new to the roadmap):** Stefan Gordon, https://github.com/stefangordon/dbn-upper-bound (manuscript/main.md): "Λ ≤ B = 3885632262767861213460393068710302759 / 24646172707879668706230182733520000000 ≈ 0.157656619095490606768 < 0.158", with X = 5,999,347,341,500, barrier time T ≈ 0.1576566, strip half-width 1/20 at time T, "De Bruijn's theorem gives a real spectrum at T + (1/20)²/2 = T + 1/800 = B". Uses Platt–Trudgian [PT21, Thm 1] and "the same classical heat-flow framework and finite-RH input" as P15 with "new analytic estimates". Status (quoted): "The paper has not undergone external peer review." "The research and initial drafts were produced with AI assistance." Partial Lean 4 audit: "The Lean theorem is conditional on explicit analytic inputs; this is not a complete formal proof of the numerical bound." It references Gomila's 0.1787854 as concurrent work.
- Neither claim appears on Wikipedia or (as far as the still-reachable copies show) the Polymath wiki (michaelnielsen.org page returned 404 today). No journal publication of either was found.

### (c) Cost-curve shape — is X ~ exp(C/ε)?

Yes, both P15's authors and the paper's own data support exp(C/ε), but the constant is larger than the roadmap's and it drifts.

- P15 §10 heuristic (p. 63): "this heuristic analysis therefore indicates that it is unlikely that one can significantly improve the bound Λ ≤ O(1/log T) without being able to exclude significant violations of the Riemann hypothesis at height T." Inverting Λ ≲ C/log T gives T ≳ exp(C/Λ).
- Tao, ninth thread comments (14 Jun 2018, https://terrytao.wordpress.com/2018/05/04/polymath15-ninth-thread-going-below-0-22/): "establishing an upper bound Λ ≤ Λ₀ is morally equivalent to establishing a certain zero-free region of diameter about exp(C/Λ₀) ... the time complexity of doing this will also be of the form exp(C'/Λ₀); one could hope to optimise the constant C' but I think it is unlikely that we can remove the exponential with current technology."
- P15 Table 1 (§10, p. 64) is the actual multi-point calibration (X, t₀, y₀, Λ), with RH assumed to height X/2:
  | X | t₀ | y₀ | Λ | Λ·ln X | Λ·ln(X/2) |
  |---|---|---|---|---|---|
  | 2·10^12 | 0.198 | 0.15492 | 0.21 | 5.95 | 5.80 |
  | 5·10^12 | 0.186 | 0.16733 | 0.20 | 5.85 | 5.71 |
  | 2·10^13 | 0.180 | 0.14142 | 0.19 | 5.82 | 5.69 |
  | 6·10^13 | 0.168 | 0.15492 | 0.18 | 5.71 | 5.59 |
  | 3·10^14 | 0.161 | 0.13416 | 0.17 | 5.67 | 5.55 |
  | 2·10^15 | 0.153 | 0.11832 | 0.16 | 5.64 | 5.53 |
  | 7·10^15 | 0.139 | 0.14832 | 0.15 | 5.47 | 5.37 |
  | 6·10^16 | 0.132 | 0.12649 | 0.14 | 5.41 | 5.31 |
  | 6·10^17 | 0.122 | 0.12649 | 0.13 | 5.32 | 5.23 |
  | 9·10^18 | 0.113 | 0.11832 | 0.12 | 5.24 | 5.15 |
  | 2·10^20 | 0.102 | 0.12649 | 0.11 | 5.14 | 5.07 |
  | 9·10^21 | 0.093 | 0.11832 | 0.10 | 5.06 | 4.99 |
  The paper states: "the final row of the table implies that one has the bound Λ ≤ 0.1 assuming that the Riemann hypothesis is verified up to the height T ≈ 4.5 × 10^21."
- Fit: C_eff := Λ·ln(T) runs 5.8 → 5.0 over Λ = 0.21 → 0.10 (natural log, T = X/2). It is monotone decreasing, so exp(C/ε) with fixed C is only a first approximation; the true curve is slightly sub-exponential in 1/ε over this range. The unreviewed 2026 points sit below the P15 table (Gomila: Λ·ln(X/2) = 5.14 at Λ = 0.179, where P15 needed X = 6·10^13 for 0.18; Gordon: 4.53 at 0.158), i.e. improved numerics lower C at fixed height — which is precisely why a constant fitted through P15 + Gomila (or Gordon) is not a curve-shape parameter but a numerics-quality parameter.
- Consequences for the roadmap's projections: with C = 5.0–5.8 (T-based), ε = 0.1 needs T ~ 10^21.7–10^25 (the paper's own row says 4.5·10^21); ε = 0.01 needs T ~ 10^217–10^250. The roadmap's "ε = 0.1 ~ 10^20" understates by 1.5–2 orders of magnitude relative to the paper's own table; "ε = 0.01 ~ 10^200" is the right order of magnitude but should be quoted as "~10^220 or more". Its C ≈ 4.7–5.0 is below every P15 table row and only matches the unreviewed Gordon point.
- The "single-anchor extrapolation" caveat: the intent (don't calibrate on an unreviewed point) is right, but the diagnosis is wrong — a peer-reviewed 12-point calibration already exists (P15 Table 1) and should replace both the single anchor and the blog point.
- "P15's own ninth thread warns the analytic estimates themselves may fail below ~0.1": NOT SUPPORTED. The ninth thread's warnings are about going below 0.22 at X ≈ 6·10^10: "In going below 0.22 we are beginning to need quite complicated mollifiers with somewhat poor tail behavior; we may be reaching the point where none of our bounds will succeed in keeping A+B bounded away from zero, so we may be close to the natural limits of our methods" (Tao, main post) and "sounds like it's going to be tough to push beyond t=0.2, y=0.2 then" (comment). No sentence in the post or comments says the estimates fail below 0.1; on the contrary, the published paper's Table 1 verifies hypotheses (ii)–(iii) down to Λ = 0.10 (t₀ = 0.093), and Theorem 1.3's effective estimates are stated for all 0 < t ≤ 1/2. The genuine analytic floor is different: the barrier needs y₀ > 0 and the effective bounds are proved for x ≥ 200, 0 ≤ y ≤ 1; the practical obstruction is that hypothesis (ii) requires lower-bounding |f_{t₀}(x+iy₀)| for ALL x ≥ X, which gets harder as t₀, y₀ shrink (the table's ~0.03 safety-margin column).

### (d) Λ < 1/2 and Λ ≥ 0 attributions — ACCURATE

- Ki, H., Kim, Y.-O., Lee, J., "On the de Bruijn–Newman constant", **Advances in Mathematics 222 (2009), no. 1, 281–306**, doi:10.1016/j.aim.2009.04.003 (https://www.sciencedirect.com/science/article/pii/S0001870809001133; Yonsei listing https://yonsei.elsevierpure.com/en/publications/on-the-de-bruijn-newman-constant/). P15 p. 2: "Ki, Kim, and Lee [10] sharpened the upper bound Λ ≤ 1/2 of de Bruijn [5] slightly to Λ < 1/2." (Wikipedia dates the result 2008, the journal issue is 2009; "Ki–Kim–Lee 2009" is fine.)
- Rodgers, B., Tao, T., "The De Bruijn–Newman constant is non-negative", **Forum of Mathematics, Pi 8 (2020), e6**, arXiv:1801.05914 (https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/de-bruijnnewman-constant-is-nonnegative/D4B85BA067E2D5A71D87E4FFB0D21E46). Roadmap's venue correction (not Annals) is right.

### Recommended replacement text for §4 "The cost curve"

> The Polymath15 barrier (Thm 1.2 of arXiv:1904.12438, Res. Math. Sci. 2019) converts RH verified to height X/2 in the strip σ ≥ (1+y₀)/2, plus a certified zero-free canopy at time t₀ and a certified barrier at X, into Λ ≤ t₀ + y₀²/2. Sound anchors: P15 itself (X ≈ 6·10^10, t₀ = y₀ = 0.2 ⇒ Λ ≤ 0.22) and P15 Table 1 row 2 + Platt–Trudgian (BLMS 2021, height 3·10^12) ⇒ Λ ≤ 0.2, the current published record. Two 2026 computer-assisted claims exist at the same height — Gomila Λ ≤ 0.1787854 (X = 6.000000185827·10^12, t₀ = 129/800, y₀² = 87677/2.5·10^6; GitHub audit repo, independently checked by Romik, not journal-reviewed) and Gordon Λ < 0.158 (partial Lean audit conditional on analytic inputs, not reviewed) — neither should be used as an anchor. The cost curve should be calibrated on P15's own 12-row conditional Table 1 (§10), which gives Λ·ln T ≈ 5.8 → 5.0 as Λ goes 0.21 → 0.10 (T = assumed verification height); i.e. T ≳ exp(C/ε) with C ≈ 5–6 and slowly decreasing, consistent with P15's heuristic Λ ≤ O(1/log T) and Tao's "exp(C'/Λ₀)" remark. Inverted: ε = 0.1 needs T ≈ 4.5·10^21 (P15's own figure); ε = 0.01 needs T ~ 10^220+. P15's ninth thread warned of the limits of the Euler-mollifier bounds near 0.22 at X ≈ 6·10^10, not of a failure below 0.1; the published table certifies the analytic hypotheses down to Λ = 0.10 conditionally. Unconditional baseline Λ < ½ (Ki–Kim–Lee, Adv. Math. 222 (2009)); any certified bound must beat ½ to be non-trivial and 0.2 to beat the published record (0.158 to beat the unreviewed one).

---

## CLAIM 2 — the Alpöge–Furman gloss

**VERDICT: ACCURATE (with one refinement).** arXiv:2608.13637 is Levent Alpöge and Ralph Furman (Anthropic), "More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line" (v1 13 Aug 2026, v2 19 Aug 2026), with the proof credited to Claude. Theorem A(i) is N₀ˢ(T,2T) ≥ (2/3 − o(1)) N(T,2T), so "≥ 2/3" (as a liminf of the proportion) is the correct reading of the theorem; the title's "more than" is justified by the Montgomery–Taylor-window refinement 0.6725 > 2/3. The roadmap's caveat on the "RH ⟺ n₋ = 0 for every finite compression" gloss is correct: **no such equivalence is stated in the paper.** The paper states the classical Weil equivalence (positivity of W on all of C_c²(ℝ) ⟺ RH, §1.2) and, attributing it to Bombieri (2000), that the negative index of finite truncations of W equals the number of off-line pairs seen by the truncation (§1.3, §7.1). The "signature (1,1)" language DOES appear in the paper (item (Z), §1.2; Prop. 4.1). The result is a record by a very wide margin over the prior 5/12 and is independently re-proved by Lamzouri (arXiv:2609.02882).

### (a) Identity, title, main theorem

- arXiv:2608.13637 (https://arxiv.org/abs/2608.13637; HTML https://arxiv.org/html/2608.13637v2). Authors: **Levent Alpöge, Ralph Furman** (both at Anthropic per Lamzouri's abstract). Title (v2, as printed in the paper): "More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line" (v1 listing title: "More than two thirds of the zeta zeros are simple and on the critical line"). Subject math.NT. v1 comments: "17 pages. Proof discovered autonomously by Claude (Anthropic); verified and communicated by the listed authors. See §1 for provenance. Lean formalization available". Title-page statement: "The mathematical argument in this paper was discovered and written by Claude, an AI developed by Anthropic. The listed authors verified the proof and take responsibility for its content."
- Abstract, first sentence (v2): "We prove unconditionally that at least two thirds of the nontrivial zeros of the Riemann zeta function, counted with multiplicity, are simple and lie on the critical line, and that at least five sixths are distinct; the previous unconditional records are 5/12 and 0.6603." Also: "With the Montgomery–Taylor window ψ_MT of ([2.6]) in place of the indicator window ψ₀, the constants improve to 2−c_MT⁻¹=0.6725… and 0.8362."
- Definitions (§1.1): N₀ˢ(T₁,T₂) := #{ρ : T₁<γ≤T₂, β=1/2, m_ρ=1} (simple zeros on the critical line); N_d := #{ρ : T₁<γ≤T₂} (distinct zeros); N₀* := distinct zeros on the line; N(T₁,T₂) counts with multiplicity.
- **Theorem A** (§1.1): (i) N₀ˢ(T,2T) ≥ (2/3 − o(1)) N(T,2T); (ii) N_d(T,2T) ≥ (5/6 − o(1)) N(T,2T). **Theorem B**: "Theorem A holds verbatim for L(s,χ) in place of ζ(s), for any fixed primitive Dirichlet character χ."
- ≥ vs >: the theorem is stated with "≥ (2/3 − o(1))", i.e. liminf of the proportion ≥ 2/3; the strict "> 2/3" is only via the 0.6725 refinement. The roadmap's "≥ 2/3" is the faithful rendering of Theorem A; note it as "≥ 2/3 − o(1) in dyadic windows; 0.6725 with the Montgomery–Taylor window" for full precision.
- Method (§1.2): RH in Montgomery 1973 "entered only to read the zero side termwise as a positive sum over real ordinates"; replaced by a "rank–trace inequality applied to a finite compression of Weil's Hermitian form, with Sylvester's law of inertia handling off-line pairs."
- Lean: §1.5 / Appendix A: "A Lean 4 formalisation of Theorems A and B accompanies the paper", "independent of [numerical certification] and depends only on the three standard axioms." Public repo: https://github.com/anthropics/formal-math (project `zeta23`); a mirror `mdumitrean/zeta-23-lean` also exists. (This is the same zeta-23-lean corpus that memory records as already distilled into Telperion emitters.)

### Does the paper state "RH ⟺ n₋ = 0 for every finite compression"?

**No.** The closest statements, verbatim:
- §1.2: Weil's form W "... its positivity on all of C_c²(ℝ) is equivalent to the Riemann hypothesis" — the classical Weil criterion, on the full test-function space, not on finite compressions.
- §1.2, item (Z): "Up to a tail of trace norm o(1), G̃ = P + Q: each distinct on-line zero contributes a rank-one positive form to P, each off-line pair {ρ, 1−ρ̄} a block of signature (1,1) to Q."
- §1.3: "The observation that the negative index of truncations of W counts off-line pairs is Bombieri's [Bom00]; see also Yoshida [Yos92] for the positivity of W on small support."
- §7.1: "That the negative index of finite truncations of Weil's form equals the number of off-line zero pairs seen by the truncation was observed by Bombieri [Bom00] (Introduction); see also Yoshida [Yos92] for the positivity of W on small support. We are not aware of a previous use of the positive index or of the rank in combination with a second-moment evaluation."
- Prop. 4.1 (Block structure): "P ⪰ 0 with rank P ≤ N₀*(I′) and tr P ≤ N₀(I′); and n₊(Q) ≤ ½ #off." (It bounds the POSITIVE index of the off-line block, which is what the argument actually uses.)

So the corpus gloss "RH ⟺ n₋ = 0 for every finite compression" is a paraphrase assembled from (Weil criterion) + (Bombieri's inertia count), and it is only correct with the qualifier "off-line pairs *seen by* the truncation" (a finite truncation of a given bandwidth/support detects only the off-line pairs within its window, up to the o(1) tail). It is not a theorem number in Alpöge–Furman, and Bombieri 2000 is the right citation for it. The "signature-(1,1) leakage" language is faithful to item (Z).

### (c) Cross-check against the established record

- On the critical line: Selberg (positive proportion), Levinson 1974 (1/3), Conrey 1989 (> 2/5), Bui–Conrey–Young 2011 (41.05%), Feng 2012, **Pratt–Robles–Zaharescu–Zeindler 2020 (> 5/12 ≈ 41.7% on the line; ≈ 40.75% simple and on the line)**, Res. Math. Sci. 7 (2020) art. 2, arXiv:1802.10521. AF §1.3 cites "[BCY11, Fen12, PRZZ20] the present record 5/12" and "5/12 for N₀ˢ/N [PRZZ20]".
- Simple zeros, conditional: Montgomery 1973 (≥ 2/3 simple under RH, from pair correlation); Conrey–Ghosh–Gonek (19/27 under RH+GLH); **Bui–Heath-Brown 2013 (arXiv:1302.5018): "at least 19/27 of the zeros ... are simple, assuming the Riemann Hypothesis"** — 19/27 ≈ 70.37%. So the brief's "Bui–Heath-Brown ≥ 70.37% on the line?" is a mis-remembering: it is 70.37% SIMPLE, CONDITIONAL on RH, not on-the-line and not unconditional.
- Distinct zeros, unconditional: Farmer (> 63.95%), **Wu, "Distinct zeros of the Riemann zeta-function", Quart. J. Math. 66 (2015) 759–: N_d(T) ≥ 0.66036 N(T)** — this is AF's "0.6603 [Wu15]".
- Therefore "≥ 2/3 simple AND on the line, unconditionally" is not merely consistent with the literature — it is a record by ~25 percentage points over PRZZ (41.7% on the line) and makes Montgomery's RH-conditional 2/3 unconditional. Independent confirmation: Y. Lamzouri, "A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line", arXiv:2609.02882 (2 Sep 2026, rev. 8 Sep 2026): "We obtain a new, conceptually simpler, unconditional proof that more than 67.25% of the non-trivial zeros ... are simple and on the critical line, and that at least 83.62% ... are distinct ... A proof of the bounds ... was very recently produced by an internal research version of Claude ... and subsequently verified by two mathematicians at Anthropic, Levent Alpöge and Ralph Furman". Neither paper is yet journal-published (arXiv only, Aug/Sep 2026).

### Recommended refinement to §2 text

> Alpöge–Furman arXiv:2608.13637 (Aug 2026; proof credited to Claude, Lean 4 formalization in anthropics/formal-math `zeta23`): Theorem A(i) N₀ˢ(T,2T) ≥ (2/3 − o(1)) N(T,2T) unconditionally — i.e. ≥ 2/3 of zeros simple and on the line as a liminf, 0.6725 with the Montgomery–Taylor window (whence the title's "more than"); 5/6 (0.8362) distinct. Prior records 5/12 (PRZZ 2020) and 0.6603 (Wu 2015); independently re-proved by Lamzouri arXiv:2609.02882. The "RH ⟺ n₋ = 0 for every finite compression" gloss is NOT a statement in the paper: it is a paraphrase of the Weil criterion (positivity of W on all of C_c²(ℝ) ⟺ RH, AF §1.2) combined with Bombieri's (2000) observation, quoted in AF §1.3/§7.1, that the negative index of a finite truncation equals the number of off-line pairs *seen by that truncation*; cite Bombieri 2000 for it. The signature-(1,1)-per-off-line-pair language is AF item (Z).

---

## Source list
- P15 paper: https://arxiv.org/abs/1904.12438 (PDF text extracted locally; Thm 1.1–1.2 pp. 2–3; §8.1–8.2; §10 heuristic + Table 1 pp. 63–64)
- Wrong id in brief: https://arxiv.org/abs/1904.12010 (Huang–Jang–Martin, hyperbolic manifolds)
- Tao ninth thread: https://terrytao.wordpress.com/2018/05/04/polymath15-ninth-thread-going-below-0-22/
- Platt–Trudgian: https://arxiv.org/abs/2004.09765 ; doi:10.1112/blms.12460
- Gomila blog: https://www.judegomila.com/posts/riemann-lambda-0.1787854 ; repo https://github.com/judegomila/dbn-lambda-01787854-candidate-audit
- Gordon repo: https://github.com/stefangordon/dbn-upper-bound (manuscript/main.md)
- Wikipedia DBN: https://en.wikipedia.org/wiki/De_Bruijn%E2%80%93Newman_constant (Polymath wiki page 404 today)
- Ki–Kim–Lee: https://www.sciencedirect.com/science/article/pii/S0001870809001133
- Rodgers–Tao: https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/de-bruijnnewman-constant-is-nonnegative/D4B85BA067E2D5A71D87E4FFB0D21E46 ; https://arxiv.org/abs/1801.05914
- Alpöge–Furman: https://arxiv.org/abs/2608.13637 ; https://arxiv.org/html/2608.13637v2 ; https://github.com/anthropics/formal-math
- Lamzouri: https://arxiv.org/abs/2609.02882
- PRZZ: https://arxiv.org/abs/1802.10521 ; Bui–Heath-Brown: https://arxiv.org/abs/1302.5018 ; Wu 2015: https://academic.oup.com/qjmath/article-abstract/66/2/759/1594406
