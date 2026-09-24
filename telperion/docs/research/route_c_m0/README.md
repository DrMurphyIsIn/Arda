# Route C, milestone M0: how small can Λ ≤ c0 go at X = 55/8?

Numeric scoping of the Polymath15 upper-bound criterion, 2026-09-23 (lane m0).

```
+--------------------------------------------------------------------------------------------+
| conjecture1_proved = False.  Everything in this directory is a bound of the form            |
| Lambda <= c0 with c0 > 0.  Lambda <= 0 is RH (Rodgers-Tao: RH <=> Lambda = 0), and nothing   |
| here moves it.  No Lean was written; no registry file was touched.                           |
+--------------------------------------------------------------------------------------------+
```

This is the M0 deliverable of `telperion/docs/ROUTE_C_SYNTHESIS_2026-09-23.md` (section 5.2, rank 2):
find the smallest certifiable c0 = t0 + y0²/2 via the Polymath15 criterion (D.H.J. Polymath,
arXiv:1904.12438, "P15", Theorem 1.2 / Proposition 3.3) at X = 55/8, the height the kernel height floor
makes hypothesis-free, and compare with X ≈ 1.28·10⁶, where the Arb-conditional zero ladder supplies
hypothesis (i). Everything below was computed in this lane with Arb ball arithmetic (python-flint 0.9.0)
and is reproducible from the scripts in this directory (section 9).

**Repair of 2026-09-23.** A skeptical review found that the first version of these certificates did not
fully cover their regions once x passed about 10⁴. The box balls were built around rounded float
midpoints and could miss a box endpoint by half an ulp. The ±10⁻¹² padding at the N-jumps of the P15
approximation was smaller than the ulp. Both defects were reproduced here. Every certificate below was
then re-run with code that builds an exact cover, audits it while running, and is re-checked by an
independent script with negative controls (section 4.6). The superseded records are kept in
`results/superseded_pre_repair/` for comparison only. Since the rerun, t0 and y0 are the exact decimal
rationals they are written as, so each certified c0 is the stated rational (12/25, 9/20, 21/50, 268/625,
4999989/10⁷).

---

## 1. The answer in one screen

**Yes: c0 < 1/2 is certifiable at X = 55/8, and three rows are certified here.** For each of
c0 = 12/25, 9/20 and 21/50 (y0 = 2/5, t0 = c0 − 2/25), all three P15 hypotheses were verified by
interval arithmetic, with a cover that is exact and audited (section 4.6). Hypothesis (i) is certified
directly here (U1). In the kernel it needs only the height floor and the T = 0 positivity lemma: the
first zeta zero is at 14.13 > 55/16.

**At X = 55/8, (i) and (iii) are free and (ii) is the whole cost.** Two parameter-free Arb
certificates (section 3) show that H₀ has no zeros in [0, 55/8] × [0, 1], and that H_t has no zeros in
[55/8, 63/8] × [0, 1] for every t in [0, 1/2]. So (i) and (iii) hold for *every* choice of (t0, y0).
The canopy (ii) is different. P15's analytic canopy argument (the Euler-mollified triangle inequality,
Lemma 8.5) only closes once the Riemann–Siegel length N reaches a threshold N_s(c0). Below
x_s = 4πN_s², the canopy must be verified numerically at time t0, all the way down from x ≈ 7.8. The
threshold never drops below N_s ≈ 136–146 for any c0 < 1/2, because t0 ≤ 1/2 caps how fast the
Dirichlet exponent grows. So every X = 55/8 certificate needs a numeric strip reaching at least
x ≈ 2.5·10⁵.

**Cost grows like x_s^1.55, and x_s grows like exp(≈6/c0).** The certified envelope and the
cost model (sections 4.3 and 5.1) give:

| c0 | N_s (y0=0.4) | x_s | strip boxes | Dirichlet terms | core-hours (measured if certified, else a projected range) | status |
|---|---|---|---|---|---|---|
| 0.48 = 12/25 | 183 | 4.21e5 | 1.81e6 | 1.21e9 | ~1.4 | **certified** |
| 0.45 = 9/20 | 265 | 8.83e5 | 4.69e6 | 4.53e9 | ~4.0 | **certified** |
| 0.42 = 21/50 | 408 | 2.09e6 | 1.61e7 | 3.04e10 | ~23.5 | **certified** |
| 0.40 | 562 | 3.97e6 | 4.1e7 | 1.2e11 | ~60–110 | projected |
| 0.38 | 805 | 8.14e6 | 1.1e8 | 4.4e11 | ~220–400 | projected |
| 0.36 | 1204 | 1.82e7 | 2.9e8 | 1.7e12 | ~0.9–1.6e3 | projected |
| 0.34 | 1896 | 4.52e7 | 8.9e8 | 8.3e12 | ~4–7e3 | projected |
| 0.30 | 5805 | 4.24e8 | 1.4e10 | 3.8e14 | ~2–3e5 | projected |

Projected core-hours are a range. The low end is the window-timed projection on a lightly loaded
machine. The high end allows for the 1.4–1.8 times the certified runs actually took on the shared
machine. The Dirichlet-term counts are the stable metric.

The empirical law is c0 · ln(x_s) ≈ 5.6–6.2. P15 section 10 predicts exactly this Λ = O(1/log X)
shape, and the roadmap calibrates its cost curve on the same product (Λ · ln T ≈ 5–6).

**The ladder (X ≈ 1.28·10⁶, Arb-conditional) gives c0 = 0.4288 with no canopy numerics at all.** That
row is certified here, modulo the ladder. The roadmap's projection "G1 ~ 0.36" is not reachable without a
canopy strip out to x_s(0.36) ≈ 1.8·10⁷ (y0 = 0.4) or 1.07·10⁷ (best y0). At that size the ladder removes
only about 2% of the strip work (section 5.2). Below c0 ≈ 0.42 the ladder hardly matters: the cost is
the canopy strip, and design A pays the same.

**The cheapest hypothesis-free c0 < 1/2 is not at X = 55/8.** The program already has a
kernel-proved effective de la Vallée Poussin region (`dlvp_zeta_region_rate_effective`,
c ≥ 9/1369088). Its packaged form `riemannZeta_ne_zero_region` also covers β ≥ 1, using Mathlib.
Together with the height floor it gives P15 Prop 3.3(i) up to height X/2 whenever
c0 > (1 − 2c/log(X/2))²/2. The design exploits that the barrier can sit exactly where the analytic
canopy takes over (X ≈ 2.47·10⁵). The entire numeric content then collapses to a 320-box barrier and
a 14-box left edge. **Certified here: c0 = 4999989/10⁷ = 1/2 − 1.1·10⁻⁶, hypothesis-free** (section 5.3).
The gap below 1/2 is set by the dVP constant. With the best published explicit constant
(Mossinghoff–Trudgian–Yang, R₀ = 5.558691, not formalized) the same design would reach c0 ≈ 0.471.

**Recommendation for M6** (a proposal only; section 7): register the design-B statement first. Its
numerics amount to about 10⁶ Dirichlet-term evaluations. It needs P15 Thm 1.3 only for x ≥ 2·10⁵, and no
small-x evaluator at all. The X = 55/8 design at c0 = 0.48 costs about 10⁹ term evaluations plus a
rigorous small-x evaluator. That is days of kernel time at current per-term costs, not "minutes to
hours".

---

## 2. What was asked, and what "certified" means here

### 2.1 The criterion

P15 Theorem 1.2 (p.2) and Proposition 3.3 (p.15) are quoted verbatim in the synthesis §5.1. With
z = x + iy, the hypotheses are:

- **(i)** H₀ has no zeros with 0 ≤ x ≤ X and √(y0² + 2t0) ≤ y ≤ 1 (Prop 3.3 form). This is implied by
  the ζ form of Thm 1.2(i): no ζ zeros with (1+y0)/2 ≤ σ ≤ 1 and 0 ≤ T ≤ X/2.
- **(ii) canopy.** H_{t0} has no zeros with x ≥ X + √(1−y0²) and y0 ≤ y ≤ √(1−2t0).
- **(iii) barrier.** H_t has no zeros with X ≤ x ≤ X + √(1−y0²), √(y0² + 2(t0−t)) ≤ y ≤ √(1−2t) and
  0 ≤ t ≤ t0.

Conclusion: Λ ≤ t0 + y0²/2, via Prop 3.3 plus de Bruijn's parametric Thm 3.2 (milestone M1).

Note that √(y0² + 2t0) = √(2c0). So the (i) requirement depends on c0 alone. This is what makes
design B work.

### 2.2 Standard of evidence

A statement marked **certified** here is a rigorous consequence of four things:

1. Arb's enclosure semantics. Every number is an Arb ball, and every inequality is checked on the ball
   endpoints. The parameters t0, y0 (and X) enter as Arb balls that contain the exact rationals.
2. The published P15 theorems that are used as black boxes:
   - Theorem 1.3 / Corollary 6.4 / Proposition 6.6: the A + B − C approximation and its error terms,
     valid for 0 < t ≤ 1/2, 0 ≤ y ≤ 1, x ≥ 200.
   - Lemma 8.2 (Dirichlet tails) and Lemma 8.5 (the improved triangle inequality, whose proof carries
     over verbatim to general y0; section 4.2).
   - Identity (35), the heat-kernel form of H_t, and definition (4).
3. Classical facts: Stirling-free crude Γ bounds (|Γ(a+ib)| ≤ Γ(a)), ζ(σ) ≤ ζ(2) for σ ≥ 2,
   ξ(s) = ξ(1−s), and the argument principle.
4. An exact cover. Every region is contained in the union of finitely many Arb boxes that were
   evaluated and accepted. In the canopy strip, each point also lies in a box that uses the N which
   Theorem 1.3 prescribes at that point. The cover is audited while the certifiers run and re-checked
   independently (section 4.6).

The P15 error analysis was not re-derived. Instead it was checked against an independent evaluator
(section 4.1): the true deviation |H/B − (f − C/B)| is 25–200 times smaller than the P15 bound at
x = 250–1000. The implementation of Lemma 8.5 reproduces two independent sources. It matches the
Polymath15 repository's own t = y = 0.4 thresholds (mollifier {2}, {2,3}, {2,3,5}: N = 340, 219, 191
there, against 340, 220, 190 here). It also matches P15's published F_{N−,N+} values (0.0263, 0.0470,
0.093) to within their unstated truncation convention (section 4.2).

Items marked **projected** extrapolate certified short windows (section 5.1). Items marked
**assumed** are hypotheses carried from outside this lane, namely the Arb ladder.

### 2.3 The Polymath15 public code

The repository `github.com/km-git-acc/dbn_upper_bound` (P15 ref. [20]) was cloned at `5fde84e`, but
its drivers were not run. Its certified pieces are PARI/GP scripts and Arb C programs tuned for X between
6·10¹⁰ and 10²¹, and neither toolchain is installed here. It served as the reference for the
re-implementation in this directory, which uses Arb through python-flint.

| file in the repo | used for |
|---|---|
| `pari/abbeff_largex_bounds.txt` | the Lemma 8.5 "sawtooth" bounds, cross-checked in section 4.2 |
| `pari/error_bounds.txt` | the Prop 6.6 error terms (source of the a − 0.125 observation in section 8) |
| `pari/Ht_eval.txt` | the small-x evaluator via a contour-shifted Φ integral |
| `python/research/Ht_small_x_fixed_mesh_verification.py` and `Writeup/lowx.tex` | the historical t = y = 0.4 "test problem", which is the Λ ≤ 0.48 bound that design A's first row reproduces in certified form |
| `python/research/mod_abbeff_lower_Nbounds.csv` | the threshold cross-check |

---

## 3. At X = 55/8, hypotheses (i) and (iii) are free

`uniform_small_x.py` evaluates H_t over boxes, in Arb, from the definition (P15 (4)): the Φ-integral,
truncated at n ≤ 6 and u ≤ 5/4. The tail bounds, stated in `p15_arb.Ht_phi`, are
Σ_{n>6}(2π²n⁴ + 3πn²)e^{−πn²} for the n-truncation and (2π² + 3π)e^{tU²+9U}cosh(|y|U)·2e^{−πe^{4U}}
for u > U. A box is accepted when its enclosure excludes 0. Each box goes to Arb as the hull of its
float corners. The initial grids have exact end breakpoints, and bisection children share the parent's
float midpoint (section 4.6).

| certificate | region | boxes | min certified \|H\| | consequence |
|---|---|---|---|---|
| U1 | H₀ on [0, 55/8] × [0, 1] | 112 | 0.0472 | Thm 1.2(i) and Prop 3.3(i) at X = 55/8, for **all** y0 ∈ (0,1], including T = 0 and T = 55/16 |
| U2 | H_t on [55/8, 63/8] × [0, 1] × [0, 1/2] | 160 | 0.0432 | (iii) at X = 55/8, for **all** (t0, y0), since the (iii) region lies inside this box |
| U2′ | H_t on [6.8, 7.8] × [0, 1] × [0, 1/2] | 200 | 0.0435 | the same at X = 6.8 < 55/8 (see below) |

The limits 55/8, 63/8, 0, 1 and 1/2 are binary doubles. The limits 6.8 and 7.8 of U2′ are not, so U2′ is
run on the outward-rounded doubles [6.8⁻, 7.8⁺]. That makes 5 initial x-cells instead of 4 (the first
version used the float values themselves, whose upper end lies below 39/5).

The nearest zero of H₀ is at x = 2γ₁ ≈ 28.27, and |H_t| stays near 0.045 on these boxes. So the
barrier at 55/8 is trivial, unlike P15's barrier at 6·10¹⁰.

**Kernel note (from the synthesis, not re-examined here).** U1 settles hypothesis (i) numerically. A
kernel proof would use the height floor instead, and that has two gaps. First, the registry node covers
0 < Im ρ < 55/16 only; the island theorem also covers the point 55/16. Second, the T = 0 line needs its
own argument, namely H_t(iy) > 0 by positivity of Φ. Taking X = 6.8 < 55/8 removes the T = 55/16
endpoint issue, and U2′ is the barrier for that choice. The
X = 55/8 canopy strips below start at 55/8 + √(1−y0²) = 7.79. At X = 6.8 the strip starts at 7.72, and
the gap [7.72, 7.79] lies inside U2. So every X = 55/8 row below is equally a certificate at X = 6.8.

---

## 4. The canopy is the whole story

### 4.1 The approximation and its error terms

Notation, with z = x + iy:

- s± = (1 ∓ iz)/2 and w± = s± + (t/2)α(s±).
- b_n = exp((t/4) log² n) and N = ⌊√(x/4π + t/16)⌋.
- γ = M_t(s−)/M_t(s+).

P15 (14) reads

  f_t(z) = Σ_{n≤N} b_n n^{−w+} + γ Σ_{n≤N} b_n n^{−w−},

where w+ = s* and w− = s̄* + κ − y. This is holomorphic in z on each N-segment [x_N, x_{N+1}), with
x_N = 4πN² − πt/4.

Theorem 1.3 and Corollary 6.4 give, for 0 < t ≤ 1/2, 0 ≤ y ≤ 1 and x ≥ 200:

  H_t/B_t = f_t − C_t/B_t + O≤(e_A + e_B + e_C) = f_t + O≤(e_A + e_B + e_{C,0}).

`p15_arb.py` evaluates f_t, f_t′, C_t/B_t and the exact error quantities (71)–(74) on Arb balls. Those
quantities are e_A, e_B, e_C, e_{C,0} with ε_{t,n} from (44) and ε̃ from (59).

**Independent check.** The direct evaluator of section 4.4 is exact up to Arb enclosure. At t = 0.4 it
gives the following:

| x | y | \|H/B − (f − C/B)\| | P15 bound e_A+e_B+e_C | \|H/B − f\| | bound with e_{C,0} |
|---|---|---|---|---|---|
| 250.7 | 0.40 | 9.8e-4 | 0.227 | 0.109 | 0.507 |
| 400.2 | 0.42 | 1.8e-3 | 0.132 | 0.093 | 0.349 |
| 1000.3 | 0.44 | 9.8e-4 | 0.046 | 0.096 | 0.174 |

### 4.2 The analytic part: P15 Lemma 8.5 for arbitrary (t0, y0)

The canopy for x ≥ x_L is handled exactly as in P15 §8.5: the argument principle for the single
holomorphic function E·H_t/B_t on the rectangle R = [x_L, x_R] × [y0, 1]. Here
E(z) = Π_{p∈P}(1 − b_p p^{−s*}) with P = {2, 3, 5, 7} fixed once for the whole rectangle. If E·H/B avoids
(−∞, 0] on ∂R, the winding number is zero and H_t has no zeros in R.

**Bottom edge y = y0 and top edge y = 1, per N-interval [N−, N+]** (`edge_interval`). On all segments
with N ∈ [N−, N+]:

- σ := Re s* ≥ σ_{N−}(y), from P15 (21) at x = x_{N−}.
- |γ| ≤ g := e^{0.02y}(x_{N−}/4π)^{−y/2}, from P15 (20).
- |κ| ≤ ty/(2(x_{N−} − 6)), from P15 (22).

With λ_d = Π_{p|d}(−b_p) and D = Πp:

- E · Σ_{n≤N} b_n n^{−s*} = Σ_n β_n n^{−s*}, where β_n = Σ_{d|(n,D), n/d≤N} λ_d b_{n/d}.
- The γ-part is γ Σ_{m≤N} m^{y} b_m m^{−s̄*}·m^{−κ}. Its κ-free piece has absolute value
  |γ|·|Σ α_n n^{−s*}|, with α_n = Σ λ_d (n/d)^{y} b_{n/d}. This step uses |E(s*)| = |E(s̄*)| (real
  coefficients). **It is exact only because the exponent of m equals the edge height y.** That is why
  Lemma 8.5 is an edge bound and not a pointwise bound in the interior, and why P15 needs the argument
  principle.
- The κ remainder is at most |E| · Z, with Z = g Σ_m m^{y} b_m m^{−σ}(m^{|κ|} − 1).

The proof of Lemma 8.5 (P15 p.54) is unchanged when N−^{−0.2}α_n is replaced by gα_n. It gives

  dist(E f, (−∞,0]) ≥ 1 − g − Σ_{n≥2} max(|β_n − gα_n|, c|β_n + gα_n|) n^{−σ} − |E| Z,
  c = (1−g)/(1+g),

and so dist(E·H/B, (−∞,0]) ≥ that − |E|_max · err.

The truncation n/d ≤ N varies with N inside an interval. It is handled rigorously: coefficients are
truncated at N−, and the extra terms with N− < n/d ≤ N+ are added in absolute value. The error `err`
bounds e_A + e_B + e_{C,0} on every segment of the interval (`err_segment`). Its ingredients are P15's
Prop 6.6(iv)/(v) with log²(x/4πn²) ≤ log²(x/4π); the Prop 6.6(vi) prefactor; ε̃ from definition (59)
with a − 0.865 (section 8); and the Dirichlet sum taken over n ≤ N+.

**Right edge and tail N ≥ N₁** (`crude_interval`, uniform in y ∈ [y0, 1]). The crude bound is
|H/B − 1| ≤ ρ, with

  ρ = (F(σ) − 1) + c_γ N^{−y0} F_{y0}(σ − |κ|) + err,  where |γ| n^y ≤ c_γ (n/N)^{y0} for n ≤ N and y ∈ [y0, 1].

F is computed exactly up to n = 6000, with P15 Lemma 8.2 tails beyond that. The piece is certified when:

- ρ < 1, which excludes zeros pointwise; and
- arcsin ρ + Σ_p arcsin(b_p p^{−σ}) < π, so E·H/B avoids (−∞, 0] on the right edge.

Geometric intervals run up to N = 10⁴⁰. Beyond that a monotone "far" bound applies: b_n ≤ n^{(t/4) log N}
for n ≤ N, which gives ρ ≤ (ζ(q) − 1) + c_γ(N^{−y0} + ζ(q − |κ|) − 1) + err with q ≈ (1+y0)/2 + (t/4) log N.

**Left edge x = x_L.** This edge is numerical (`smallx.left_edge`): Arb boxes on {x_L} × [y0, 1] check
that dist(E(f − C/B), (−∞,0]) > |E|·(e_A + e_B + e_C). The left edge is placed where this is largest,
following P15's §8.1 heuristic.

**Cross-checks.**

- At t = y = 0.4 the single-N bottom-edge thresholds match the Polymath15 repository's own table
  (`python/research/mod_abbeff_lower_Nbounds.csv`: 340, 219, 191 there; 340, 220, 190 here).
- P15 §8.5 reports F_{69098,8·10⁴} = 0.0263, F_{8·10⁴,1.1·10⁵} = 0.0470 and F_{1.1·10⁵,2.2·10⁵} = 0.093.
  The same formula with P15's constants gives 0.0576, 0.1185, 0.2395 with truncation at N−, and 0.0202,
  0.0408, 0.0867 with truncation at N+. P15's values lie between the two, so the formula is reproduced
  up to P15's unstated truncation convention.
- At P15 Table 1's first row (N₀ = 398942, X = 2·10¹²), Lemma 8.5 with P = {2,3,5,7} already closes the
  bottom edge at c0 ≈ 0.18–0.19, against P15's 0.21 obtained from the weaker Lemma 10.1. This is a
  single-N float check, recorded only as calibration. It is not a claim about Λ.

### 4.3 The certified envelope N_s(c0)

`envelope.py` certifies the whole analytic part for 15 values of c0, at two choices of y0: the
N_s-minimizing y0 found by a float pre-scan, and y0 = 0.4, which makes the numeric strip cheapest. All
30 certificates are OK (`results/envelope.json`). These rows certify the analytic part only, so they
contain no boxes and the coverage repair of section 4.6 does not touch them. They were computed for the
binary doubles of the listed parameters, which does not matter for thresholds. The rows of section 5
redo their analytic parts with the exact rationals and get the same N_s and N₁.

| c0 | best y0 | N_s | x_s = 4πN_s² | N₁ | N_s at y0 = 0.4 | x_s at y0 = 0.4 |
|---|---|---|---|---|---|---|
| 0.30 | 0.14 | 3326 | 1.39e8 | 102945 | 5805 | 4.24e8 |
| 0.32 | 0.16 | 2068 | 5.37e7 | 48151 | 3186 | 1.28e8 |
| 0.34 | 0.18 | 1354 | 2.30e7 | 26106 | 1896 | 4.52e7 |
| 0.36 | 0.18 | 923 | 1.07e7 | 16208 | 1204 | 1.82e7 |
| 0.38 | 0.18 | 653 | 5.36e6 | 11487 | 805 | 8.14e6 |
| 0.40 | 0.20 | 477 | 2.86e6 | 6945 | 562 | 3.97e6 |
| 0.42 | 0.22 | 358 | 1.61e6 | 4324 | 408 | 2.09e6 |
| 0.43 | 0.22 | 312 | 1.22e6 | 3767 | 350 | 1.54e6 |
| 0.44 | 0.22 | 275 | 9.50e5 | 3341 | 304 | 1.16e6 |
| 0.45 | 0.24 | 243 | 7.42e5 | 2682 | 265 | 8.83e5 |
| 0.46 | 0.24 | 216 | 5.86e5 | 2382 | 233 | 6.82e5 |
| 0.47 | 0.24 | 192 | 4.63e5 | 2137 | 206 | 5.33e5 |
| 0.48 | 0.26 | 172 | 3.72e5 | 1753 | 183 | 4.21e5 |
| 0.49 | 0.26 | 155 | 3.02e5 | 1569 | 162 | 3.30e5 |
| 0.4999989 | 0.30 | 140 | 2.46e5 | 1296 | 146 | 2.68e5 |

**The floor.** Adding primes to the mollifier barely helps. At c0 = 0.4999989, y0 = 0.3, the thresholds
are N_s = 147, 140, 138 and 136 for P = {2,3,5}, {…,7}, {…,11} and {…,13}. The edge bound needs
Re s* ≳ 1.75, and Re s* ≈ (1+y0)/2 + (t0/2) log N with t0 ≤ 1/2. So N_s ≈ 140 is a floor of this
method, whatever c0 < 1/2 is chosen.

### 4.4 The numeric strip [X + √(1−y0²), x_L] × [y0, √(1−2t0)] at time t0

The strip is covered by adaptive boxes z_c + W, W = [−h_x, h_x] × [−h_y, h_y]. The adaptive loop
works with float boxes [xa, xb] × [ya, yb]. Each float box goes to Arb as its hull ball, and z_c, h_x, h_y
are that ball's own exact centre and half-widths, so the set certified is the ball itself, which contains
the float box (section 4.6). Each box is checked with a first-order Taylor model (`canopy_mesh.py`). Let
B1 be an Arb enclosure of F′ over the box. Then

  min_W |F| ≥ |F′(z_c)|·dist(−F(z_c)/F′(z_c), W) − ρ·(rad B1 + |mid B1 − F′(z_c)|),  ρ ≥ √(h_x² + h_y²),

with ρ an Arb enclosure. The box is accepted when this exceeds the approximation error. Two evaluators
are used:

- **x ≥ 200: the A+B−C evaluator** (F = f_t). Every box uses one N. The N-segments come from
  `canopy_mesh.n_segments`, which uses directed rounding. So every point lies in a box whose N is the
  correct one on the closed segment [x_N, x_{N+1}], where Theorem 1.3's bound holds by continuity. The
  construction, the lemma and the audit are in section 4.6. Both criteria are tried: e_C with C_t/B_t enclosed over the box, and
  e_{C,0} without it. C₀(p) is evaluated through its removable singularities at p = ±1/2 by a
  mean-value form. How far down this evaluator reaches depends on the row. Its worst point is
  x ≈ 223.66 (the N = 4 segment), where the ratio |f − C/B| / (e_A+e_B+e_C) at y = y0 is 1.042 for
  (t0, y0) = (0.40, 0.40), 1.015 for (0.37, 0.40), and **0.987 for (0.34, 0.40)**. So the c0 = 0.42 row
  uses the direct evaluator up to x = 300 (`--xdirect 300`), above which the ratio is at least 1.55.
  An earlier attempt with the A+B−C boxes starting at 200 crawled towards x ≈ 223.66 with shrinking
  boxes instead of failing fast, and was killed. The drivers now cap evaluations per chunk
  (`max_evals`) and hand failing chunks below 5000 to the direct evaluator.
- **x < x_direct (200, or 300 for the c0 = 0.42 row): direct evaluation** by the heat-kernel identity P15 (35),
  H_t(z) = (1/(8√π)) ∫ ξ((1+iz)/2 + √t v) e^{−v²} dv, with H′ from the ξ′ power series. The v-tails
  are bounded by |ξ(s)| ≤ 0.825(σ′² + T²)π^{−1}Γ(σ′/2) for σ′ = max(σ, 1−σ) ≥ 2, plus a log-derivative
  argument (`p15_arb._tail_bound`). Arb's integrator tolerance is scaled to e^{−πx/8}; without that it
  stops early (section 8, footgun 1).

Strip limits are computed in Arb from the exact t0, y0 and X, then rounded outward to doubles: the start
X + √(1−y0²) down, the bottom y0 down, and the top √(1−2t0) up. The first version lifted a float
√(1−2t0) by a fixed 10⁻¹². No fixed epsilons remain (section 4.6).

### 4.5 Controls: the certifiers reject regions that contain zeros

A certifier that accepts everything proves nothing. `controls.py` runs each of the three box certifiers
twice: once on a small region containing a genuine real zero, located by a certified sign change on
the real axis, and once on the zero-free canopy region directly above it (`results/controls.json`).
For C2 the sign change is that of Re(f_t·e^{i arg B_t}), which approximates H_t/|B_t| to within the P15
error, so the zero it locates is of H_t up to that error.

| control | evaluator | zero located at | region with the zero | canopy region above it |
|---|---|---|---|---|
| C1 | direct (ξ heat kernel), t = 0.4 | x ∈ [28.00, 28.05] | rejects, as required | certifies |
| C2 | A+B−C Taylor boxes, t = 0.4 | x ∈ [1000.16, 1000.18] | rejects, as required | certifies |
| C3 | Φ-integral boxes, t = 0 | x = 2γ₁ ≈ 28.27 | rejects, as required | certifies |

### 4.6 Exact cover (the repair of 2026-09-23)

A box certificate is only as good as its cover. Every point of the region must lie in some Arb box that
was evaluated and accepted. In the canopy strip, that box must also use the N that P15 Theorem 1.3
prescribes at that point. A skeptical review found that the first version of this directory fell short
of this once x passed about 10⁴. Both defects were reproduced here with the original code, run on a
scratch copy.

- **Box balls missed their endpoints.** `box_ball` built the x-ball as arb(fl((xa+xb)/2), (xb−xa)/2).
  When the float midpoint rounds, the ball misses one endpoint by up to half an ulp: about 1.2·10⁻¹⁰
  near 10⁶, and 2.9·10⁻¹⁰ above 2²¹. Consecutive boxes then leave uncovered slivers. Reproduced
  (`coverage_check.py`, control NEG1): the window [2097200, 2097302] of the c0 = 0.42 row has 32 slivers,
  the widest 2.9·10⁻¹⁰. The review found all 60 t-slabs of the ladder barrier affected.
- **The padding at N-jumps vanished.** Segment ends were padded by ±10⁻¹² in double arithmetic. Above
  x ≈ 8·10³ that is less than the double ulp, so the padding rounds away. A sliver just above x_N was
  then covered only by boxes that use N − 1, which is outside Theorem 1.3. Reproduced (NEG2): at N = 408
  (c0 = 0.42) the N = 408 boxes start 4.2·10⁻¹¹ above x₄₀₈. The review found 4 of 6 checked boundaries
  wrong in the 0.42 row and 1 of 9 in the 0.48 row.
- **A third instance, found during the repair.** Chunk grids were computed as a + (b − a)k/n, whose last
  point need not equal b. In the pre-repair c0 = 0.45 row, the direct-evaluator chunks ended 2.8·10⁻¹⁴
  below x = 200, where the A+B−C chunks began (NEG3).

The margins were never the issue. The review measured margins of 0.2 to 0.6 on the boxes next to the
sampled slivers. But the certificates as run did not cover their regions, so every row was re-run with
the repaired code.

**The repair** (`rigor.py`, used by every certifier):

1. **Hull balls.** The float box [xa, xb] × [ya, yb] goes to Arb as acb(hull(xa, xb), hull(ya, yb)),
   where hull(a, b) = arb(a).union(arb(b)) contains the closed interval. The Taylor model of section 4.4
   uses the ball's own exact centre and half-widths, so the set certified is the ball itself. The t-balls
   of barrier slabs and the Φ-boxes of section 3 are hulls too.
2. **Directed rounding, no fixed epsilons.** Region limits are computed in Arb from the exact parameters
   and converted to doubles by f_down and f_up. These use exact Arb comparisons and nextafter steps.
   This covers the strip start, bottom and top, the barrier's right end X + √(1−y0²) (rounded up) and
   its curved y-limits over each t-slab (outward), and U2′'s limits.
3. **N-segments with a coverage lemma** (`canopy_mesh.n_segments`). Here x_N = 4πN² − πt/4 is an Arb
   ball, and t may itself be a ball. N₀ is the largest N with x_N ≤ x₀ for certain. The piece for N is
   [a_N, b_N], with a_{N₀} = x₀, a_N = max(x₀, f_down(lower x_N)) for N > N₀, and b_N = min(x₁,
   f_up(upper x_{N+1})). The construction stops at the first N with x₁ ≤ lower x_{N+1}. (The audit
   below checks the stricter a_N ≤ lower x_N for N > N₀. That holds in every run here.)
   *Lemma.* Every x ∈ [x₀, x₁] then lies in the piece of an N with x_N ≤ x ≤ x_{N+1}, for every t in
   the ball. *Proof.* Let x_M ≤ x < x_{M+1}. Then M ≥ N₀ because x ≥ x₀ ≥ x_{N₀}, and M ≤ N_last
   because x ≤ x₁ ≤ x_{N_last+1}; at equality, the closed segment of N_last contains x. The piece for M
   starts at or below max(x₀, x_M) and ends at or above min(x₁, x_{M+1}), so it contains x. ∎
   Every box in a piece uses that piece's N, so neighbouring pieces overlap by at least the Arb width of
   x_N, plus up to one ulp on each side.
4. **Exact tilings.** Every grid (`rigor.grid`) has bit-identical first and last breakpoints. This covers
   strip chunks, y-splits, left-edge pieces, initial Φ-grids and barrier t-slabs; the last t-slab is
   closed by the Arb ball of the exact t0. Bisection children share the parent's float midpoint.
5. **Exact parameters.** t0 and y0 are taken as the decimal rationals they are written as (0.34, 0.4,
   0.4549989, ...) and entered as Arb balls that contain them. So the certified bound is Λ ≤ c0 with
   c0 = t0 + y0²/2 exactly the rational 12/25, 9/20, 21/50, 268/625 or 4999989/10⁷. The first version
   certified the binary doubles, whose c0 lies about 3·10⁻¹⁷ higher.

**Audit while running.** `cover_strip` checks, by exact comparison, that:

- each accepted Arb box contains its float box;
- the y-pieces of each x-box tile [ya, yb];
- the x-boxes of each N-piece tile the piece;
- the pieces satisfy the hypotheses of the lemma (`audit_segments`).

The strip driver also checks that the certified chunks tile [x_start, x_L], and the barrier driver
checks that the t-slabs tile [0, t0]. Any violation fails the run. Every record carries these counts in
`coverage_audit`.

**Independent check** (`coverage_check.py`, `results/coverage_check.json`). This script records every
accepted Arb box exactly as the certifier returned it. It then asks only four questions:

- Does the union of the x-balls cover the region?
- For each N, do the balls evaluated with that N cover [max(x₀, x_N), min(x₁, x_{N+1})]?
- Do the y-balls of each x-box cover the y-range?
- For the barrier, do the t-balls cover each slab?

It does not rely on the construction's own claims. The results:

- All 40 slabs of the dvp barrier and all 60 slabs of the ladder barrier are covered.
- So are the two 0.42-row windows where the review found slivers ([2097200, 2097302] and
  [1500000, 1500060]), and 3-unit windows around the N-jumps 350, 380, 400 and 408 (c0 = 0.42) and
  170 (c0 = 0.48).
- **Whole strips** (`--full-row`, `results/coverage_full_*.json`). Every chunk of the certified strip
  was re-run with recording and checked, and the chunks were checked to tile [x_start, x_L]. All three
  strips are covered, with 0 gaps of any kind: 0.48 (261 chunks, 1,805,289 boxes), 0.45 (492 chunks,
  4,688,894 boxes) and 0.42 (1,123 chunks, 16,050,915 boxes). The re-run box counts equal the certified
  records exactly.

The negative controls behave:

- With the pre-repair ball, the check finds 32 slivers in [2097200, 2097302], and the run-time audit
  flags them.
- With the pre-repair padding, the check finds N = 408 uncovered for 4.2·10⁻¹¹, and the audit reports
  "piece N=408 starts ... above x_N".
- The pre-repair chunk grid of the 0.45 row fails to tile [x_start, 200]; the repaired grid tiles it.

---

## 5. Results

### 5.1 Design A: X = 55/8, hypothesis-free

All rows: (i) by U1, (iii) by U2 (and by a row-specific exact-region barrier run), P = {2,3,5,7},
Arb precision 80 bits. All three records come from the repaired code, run with the exact rationals
t0, y0 (2026-09-23, 21:53–22:53).

| | c0 = 12/25 = 0.48 | c0 = 9/20 = 0.45 | c0 = 21/50 = 0.42 |
|---|---|---|---|
| (t0, y0), exact | (2/5, 2/5) | (37/100, 2/5) | (17/50, 2/5) |
| canopy strip | [7.79, 423884.5] × [0.4, 0.4472] | [7.79, 885767.8] × [0.4, 0.5099] | [7.79, 2097302.2] × [0.4, 0.5657] |
| N range in strip | 4 … 183 | 4 … 265 | 4 … 408 |
| direct-evaluator range | [7.79, 200] | [7.79, 200] | [7.79, 300] |
| boxes (A+B−C / direct) | 1,803,891 / 1,398 | 4,686,732 / 2,162 | 16,046,339 / 4,576 |
| box evaluations | 2,487,915 | 6,476,591 | 28,305,409 |
| Dirichlet-term evaluations (≈ 4N per box evaluation) | 1.21e9 | 4.53e9 | 3.04e10 |
| CPU seconds (shared machine) | 5,166 | 14,327 | 84,633 |
| coverage audit: boxes checked / violations / N-pieces / chunks tile the strip | 1,805,289 / 0 / 392 / yes | 4,688,894 / 0 / 705 / yes | 16,050,915 / 0 / 1,453 / yes |
| independent full-strip cover check (`coverage_check.py --full-row`) | covered (1,805,289 boxes re-run) | covered (4,688,894 boxes re-run) | covered (16,050,915 boxes re-run) |
| min certified \|H_t/B_t\| at box centres | 1.6e-3 | 6.3e-4 | 2.7e-2 |
| min A+B−C box margin | 1.4e-6 | 4.3e-7 | 1.9e-8 |
| analytic: N_s / N₁ | 183 / 1530 | 265 / 2423 | 408 / 3682 |
| min bottom-edge margin | 1.75e-3 | 8.16e-5 | 1.88e-3 |
| max crude ρ | 0.970 | 0.960 | 0.996 |
| left edge x_L, boxes, min margin | 423884.462, 13, 1.071 | 885767.753, 13, 1.039 | 2097302.248, 13, 1.027 |
| (i) U1-type rectangle / exact-region barrier: boxes, min \|H\| | 84, 0.0472 / 160, 0.0437 | 84, 0.0472 / 160, 0.0437 | 84, 0.0472 / 160, 0.0437 |
| all certified | **yes** | **yes** | **yes** |

The minimum box margin is small by design. The adaptive loop accepts any box whose certified lower bound
is positive, so the smallest margin belongs to the box that only just passed. That bound is rigorous, and
coverage no longer relies on margins at all (section 4.6).

**What changed in the rerun.** The 0.48 and 0.45 rows reproduce the pre-repair box, evaluation and
term counts exactly. The 0.42 row has one more A+B−C box and three more evaluations. The hull balls are
at most an ulp wider, so the adaptive decisions barely move. The minimum A+B−C margins moved in the
third digit or less for 0.48 and 0.45. For 0.42 the new minimum is 1.9·10⁻⁸, against 2.7·10⁻⁹ before;
the just-passing box is now a different one. The design-A left edges have 13 boxes instead of 12,
because their y-range now starts just below 2/5, at the double 0.39999999999999997. The analytic parts, U1, U2, the dvp and ladder
rows, and the controls are unchanged. U2′ has 200 boxes instead of 160 (section 3). CPU seconds are
lower than in the first runs because the machine was less contended; the Dirichlet-term counts are the
stable metric.

**Projections for smaller c0** (`cost_model.py`, `results/cost_model.json`). The same box algorithm was
run on certified 12–40-unit windows at several x, the per-unit rates were fitted as powers of x, and the
fits were integrated from 200 to x_s. The model reproduces the three completed full runs to within 3%:

- c0 = 0.48: projected 1.795e6 boxes and 1.200e9 terms, against 1.805e6 and 1.207e9 actual.
- c0 = 0.45: projected 4.705e6 boxes and 4.59e9 terms, against 4.689e6 and 4.53e9 actual.
- c0 = 0.42: projected 1.560e7 boxes and 2.98e10 terms, against 1.605e7 and 3.04e10 actual.

Terms per unit length grow like x^0.52–0.55, so the total grows like x_s^1.55. The table in section 1
lists the projections. The cost model was re-run with the repaired code: 72 windows, all certified,
coverage audit clean. Its box, evaluation and term projections are identical to the first run's. Its
core-hour projections come from window timings, and this time the machine was lightly loaded. The
certified full runs took 1.4–1.8 times the projected core-hours on the shared 32-core machine (0.48:
1.44 against 0.84; 0.45: 3.98 against 2.57; 0.42: 23.5 against 16.8). The first, pre-repair model had
been timed under heavier load and projected 1.0, 3.7 and 29.5.

### 5.2 Design C: X ≈ 1.28·10⁶, (i) from the Arb ladder (assumed)

`barrier_large.py --design ladder`: **c0 = 0.4288 = 268/625** (t0 = 0.40675, y0 = 0.21 exactly;
re-run with the repaired code, `results/row_ladder_c0_0.4288.json`).

- Analytic part: N_s = 318, just below N = 319 at the canopy start. N₁ = 4226, crude ρ ≤ 0.977.
- Barrier location: X = 1,279,991 (≤ 1.28·10⁶, so T ≤ X/2 < 640000), chosen by P15's §8.1 heuristic.
- Barrier: 544 Taylor-model boxes over 60 t-slabs with N = 319, minimum margin 8.7·10⁻³. The coverage
  audit found 0 violations over the 544 boxes, and the t-slabs tile [0, t0]. The independent check
  (section 4.6) finds all 60 slabs covered. In the first version all 60 had x-slivers.
- Left edge at x_L = 1,279,991.978, which is X + √(1−y0²) rounded up and equals the barrier's right end:
  margin 1.05. The canopy start lies inside N = 319, as the code checks rigorously.

Nearby values fail. At c0 = 0.4285 (y0 = 0.2) the bottom edge fails exactly at N = 319. At c0 = 0.428
(y0 = 0.22 and 0.24) the thresholds are N_s = 321 and 322, both above 319. So 0.4288 is within about
5·10⁻⁴ of the best this design gives without a canopy strip.

**Below 0.4288 the ladder buys little.** The design needs the same canopy strip as design A, from
1.28·10⁶ to x_s(c0). Using the fitted power laws, the share of design A's strip terms that the ladder
removes is:

| c0 | 0.43 | 0.42 | 0.40 | 0.38 | 0.36 | 0.34 | ≤ 0.32 |
|---|---|---|---|---|---|---|---|
| share removed | 75% | 47% | 17% | 6% | 1.7% | 0.4% | ~0 |

So the roadmap's C8 projection "G1 ~ 0.36" (`RH_ROUTES_ROADMAP_2026-09-16.md:223`) costs about
1.7·10¹² Dirichlet terms (y0 = 0.4) with or without the ladder. It should not be read as a
ladder-enabled rung.

### 5.3 Design B: X ≈ 2.47·10⁵, (i) from the kernel dVP region, hypothesis-free

The kernel theorem `ZeroFreeBridge.dlvp_zeta_region_rate_effective`
(`examples/li_positivity/lean/DlvpZetaRateEffective.lean:34`) states the following for every ζ-zero
β + iγ with 3/4 ≤ β < 1 and |γ| ≥ 55/16:

  β ≤ 1 − dlvpRateC/log|γ|,  with  dlvpRateC ≥ 9/1369088 (`dlvpRateC_lower`, :294).

That statement stops short of β = 1. The packaged form `ZeroFreeBridge.riemannZeta_ne_zero_region`
(`DlvpZetaZeroFree.lean:57`) covers every β > 1 − dlvpRateC/log|γ| with |γ| ≥ 55/16, with no
multiplicity input. It gets β ≥ 1, including the line β = 1, from Mathlib's
`riemannZeta_ne_zero_of_one_le_re` (`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`). This is the
theorem design B consumes.

Prop 3.3(i) asks for no H₀ zero with 0 ≤ x ≤ X and y ≥ √(2c0). Equivalently, via ρ ↦ 1 − ρ̄, no ζ zero
with β ≥ (1 + √(2c0))/2 and 0 ≤ γ ≤ X/2. That region is covered by:

- the height floor, for 0 < γ < 55/16;
- ζ(σ) < 0 on (0,1) and ξ(1) = 1/2 ≠ 0 (the kernel has H₀(i) = 1/16, `H_zero_I`), for γ = 0;
- `riemannZeta_ne_zero_region`, for 55/16 ≤ γ ≤ X/2, as soon as (1 + √(2c0))/2 > 1 − c/log(X/2).

The design puts the barrier where the analytic canopy already works, so no canopy strip is needed.
**Certified: c0 = 4999989/10⁷ = 0.4999989** (t0 = 0.4549989, y0 = 0.3 exactly; re-run with the
repaired code, `results/row_dvp_c0_0.4999989.json`).

- Analytic part: N_s = 140, N₁ = 1296, crude ρ ≤ 0.963.
- Barrier location: X = 247102.678. The left edge sits at x_L = 247103.632, which is X + √(1−y0²)
  rounded up and equals the barrier's right end: margin 1.09. The canopy start lies inside N = 140, as
  the code checks rigorously.
- Barrier: 320 boxes (40 t-slabs, N = 140), minimum margin 0.72. The coverage audit found 0 violations,
  and the independent check finds all 40 slabs covered.
- (i): needs c0 > 0.49999887863. Here c0 = t0 + y0²/2 = 4999989/10⁷ exactly, and the Arb ball
  containing it clears that bound: **OK**.

The total numeric content is 334 boxes (about 1.9·10⁵ Dirichlet terms). The analytic content is
186 edge pieces (3.9·10⁵ coefficient terms) plus 125 crude pieces (about 1.5·10⁶ terms, mostly the
exact F-sums up to n = 6000, which could be shortened).

**The dVP constant sets the gap.** Solving (1 − √(2c0)) log(X/2)/2 < c along the certified envelope
(`summarize.py`) gives the constant each c0 needs:

| c0 | 0.4999989 | 0.49 | 0.48 | 0.47 | 0.46 | 0.45 | 0.44 | 0.42 | 0.40 |
|---|---|---|---|---|---|---|---|---|---|
| dVP constant needed | 6.4e-6 | 0.060 | 0.123 | 0.188 | 0.257 | 0.33 | 0.41 | 0.58 | 0.77 |

The kernel constant 6.57·10⁻⁶ reaches the first column only. The best published explicit constant of
this shape, c = 1/5.558691 = 0.1799 (Mossinghoff–Trudgian–Yang, arXiv:2212.06867, |t| ≥ 2; checked
against the abstract), would reach c0 ≈ 0.471 by interpolation. That value is not certified here and not
formalized anywhere in the repo. Below about 0.47 no known constant of the form 1 − c/log|γ| suffices at
these heights. Below that point the cost is the canopy strip (design A), whatever supplies (i).

---

## 6. What each design needs from the kernel (M6 / M7)

| | design B (dVP) | design C (ladder) | design A (X = 55/8) |
|---|---|---|---|
| c0 (exact rationals) | 4999989/10⁷ | 268/625 = 0.4288 | 12/25 / 9/20 / 21/50 |
| hypothesis (i) | kernel `riemannZeta_ne_zero_region` (dVP rate + Mathlib's β ≥ 1) + height floor + H₀(iy) > 0 (all exist or are small) | ladder, **assumed** (Arb binders) | height floor (+ T = 0 lemma); or X = 6.8 |
| barrier numerics | 320 boxes, N = 140 | 544 boxes, N = 319 | trivial (U2) |
| canopy numerics | left edge only (14 boxes) | left edge only (16 boxes) | 1.8e6 / 4.7e6 / 1.6e7 boxes up to N = 183 / 265 / 408 |
| Dirichlet terms | ~2e5 (+ ~1.9e6 analytic) | ~8e5 (+ ~2.5e6 analytic) | 1.2e9 / 4.5e9 / 3.0e10 |
| P15 Thm 1.3 needed for | x ≥ 2.47e5 | x ≥ 1.28e6 | x ≥ 200 |
| small-x evaluator (x < 200–300) | no | no | **yes**, but only on [X+√(1−y0²), 200] (300 for c0 = 0.42): 1,398 / 2,162 / 4,576 direct boxes, plus 272 Φ-boxes for U1/U2 |
| kernel time at ~250 µs/term (ANDURIL EM rate) | ~9 min | ~14 min | 3.5 days / 13 days / 88 days |

In all three designs the Lean-side content is: M1 (parametric de Bruijn); M4 (Prop 3.3 plus Thm 1.2
assembly); M5 (Thm 1.3 with Prop 6.6); Lemma 8.2; and Lemma 8.5 in the general-y0 form of section 4.2,
plus the argument principle for the rectangle. Design B additionally consumes the existing dVP theorem
(`riemannZeta_ne_zero_region`). It needs neither the ladder nor a small-x evaluator. A kernel
re-implementation of any box certificate must also rebuild the exact cover of section 4.6: hull balls,
directed rounding, exact tilings and the N-segment lemma. It must not trust float midpoints.

---

## 7. Proposed registry operations (text only; `telperion/missions/` untouched)

1. **New draft node `RH_dbn_lambda_lt_half_dvp`** (M6-B; milestone). Statement:
   `∀ t : ℝ, (4999989/10000000 : ℝ) ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0`.
   depends_on: `RH_dbn_p15_criterion` (M4), `RH_dbn_debruijn_parametric` (M1),
   `RH_dbn_effective_Ht_approx` (M5, x ≥ 2·10⁵ suffices), the dVP node carrying
   `riemannZeta_ne_zero_region` (`dlvp_zeta_region_rate_effective` together with Mathlib's
   `riemannZeta_ne_zero_of_one_le_re` for β ≥ 1), `AND_height_floor_kernel`, `RH_dbn_H0_eq_xi`.
   Numeral: 4999989/10⁷, with t0 = 4549989/10⁷ and y0 = 3/10. The certificate here was computed for
   exactly these rationals, as Arb balls containing them (section 4.6). Its margins are 2.1·10⁻⁸ in (i),
   1.8·10⁻³ on the edges and 0.72 at the barrier, with crude ρ ≤ 0.963. A kernel run would redo the
   numerics in its own arithmetic.
2. **Amend draft `RH_dbn_lambda_le_c0`** (M6-A, X = 55/8): record c0 = 12/25 as the smallest value
   certified cheaply (1.2e9 terms), and 21/50 as the smallest certified here. Both are certified for the
   exact rationals. Mark it "not minutes to hours" and record the small-x evaluator as a hard dependency.
3. **Amend M7 / roadmap C8**: replace "G1 ~ 0.36" with "0.4288 with no canopy numerics at X ≈ 1.28·10⁶
   (certified modulo the ladder); anything below ≈ 0.42 is canopy-strip-bound and ladder-independent".
4. **Synthesis §5.2 row M0**: mark done, pointing to this directory. Note the coverage repair of
   2026-09-23 (section 4.6): only the post-repair records in `results/` are certificates.

---

## 8. Caveats, errata and footguns

- **P15 (59) vs Prop 6.6(vi).** Definition (59) has ε̃ with 0.397·9^σ/(a − 0.865), but the proof of
  Prop 6.6(vi) (arXiv v2 p.35) writes 1.24·3^{±y}/(a − 0.125) with no justification for the change. The
  repo's `pari/error_bounds.txt` uses N − 0.125. **This lane uses (59), the conservative choice.** At
  P15's N ≈ 69098 the difference is immaterial. At the N = 4–400 used here it is up to about 24% of that
  term.
- **P15 §10 swaps the labels (ii) and (iii) in prose.** It says "verify the hypothesis in Theorem
  1.2(iii) for any choice of parameters" about the canopy, and "the barrier hypothesis (Theorem
  1.2(ii))". The theorem statement (p.2) is authoritative: (ii) is the canopy.
- **The LaTeX draft in the Polymath15 repo** (`Writeup/initial.tex`) has older constants. Examples are
  ε̃ with a − 0.125 and T′ − 3.33, and "x/2 − 6.66" in Prop 6.6(iv). Only the published arXiv v2
  constants were used here.
- **t = 0.** Thm 1.3 is stated for t > 0. The barrier at t = 0 uses the bound by continuity in t
  (H_t, f_t and the error terms are continuous in t). A t-slab is the Arb hull of its ends, so it can
  reach a rounding error below 0 or above t0. Every formula evaluated there is finite, and enclosing a
  superset of the slab is conservative.
- **Footgun 1: Arb's integrator.** `acb.integral` stops at max(abs_tol, rel_tol·|I|), with abs_tol
  defaulting to 2^−prec. For |H_t| ≈ e^{−πx/8} it returns a correct but useless wide ball. The fix
  scales abs_tol and precision with πx/8.
- **Footgun 2: float strip limits.** Always round region limits outward, with directed rounding and
  not a fixed epsilon (sections 4.4 and 4.6).
- **Footgun 3: macOS multiprocessing.** It uses spawn, so every driver needs `if __name__ == '__main__'`.
- **Footgun 4: float midpoints, sub-ulp padding and float grids (the 2026-09-23 repair).**
  - A ball arb(fl((a+b)/2), (b−a)/2) need not contain [a, b].
  - A padding of ±10⁻¹² is below the double ulp above 8·10³.
  - a + (b−a)k/n need not end at b.

  All three left uncovered slivers in the first version of these certificates. The fixes: build balls
  as hulls, round with f_down and f_up, grid with exact endpoints, and audit the cover (section 4.6).
  `results/superseded_pre_repair/` keeps the pre-repair records. They are not certificates.
- **Mesh counts are algorithm-specific.** They come from adaptive first-order Taylor boxes. A kernel
  implementation could do better, for example with P15's §7 Taylor multi-evaluation or higher-order
  models, or worse.
- **CPU seconds were measured on a shared machine** (load 30–70 from other lanes). The Dirichlet-term
  counts are the stable metric.
- **Not done here:**
  - design A below c0 = 0.42 (projected only);
  - the ladder design with an extended strip;
  - an independent re-derivation of P15's error analysis;
  - any check of the 2026 claims (Gomila 0.1787854, Gordon 0.158). The calibration note in section 4.2
    shows only that stronger canopy lemmas exist, which is consistent with such claims.

---

## 9. Reproduce

Environment: Python 3.12 plus `pip install python-flint==0.9.0 mpmath numpy`. The runs here used a
lane-private venv built from the designated venv312 interpreter.

```sh
cd telperion/docs/research/route_c_m0
python uniform_small_x.py                                    # U1, U2, U2'
python envelope.py                                           # certified N_s(c0) table  (~20 min, 6 workers)
python certify_route.py --design X55o8 --t0 0.4  --y0 0.4 --nscan 120,400  --out results/row_X55o8_c0_0.48_t0.4_y0.4.json
python certify_route.py --design X55o8 --t0 0.37 --y0 0.4 --nscan 150,800  --out results/row_X55o8_c0_0.45_t0.37_y0.4.json
python certify_route.py --design X55o8 --t0 0.34 --y0 0.4 --nscan 250,1200 --xdirect 300 --out results/row_X55o8_c0_0.42_t0.34_y0.4.json
python barrier_large.py --design dvp    --t0 0.4549989 --y0 0.3  --nscan 60,600  --nt 40 --out results/row_dvp_c0_0.4999989.json
python barrier_large.py --design ladder --t0 0.40675   --y0 0.21 --nscan 200,700 --nt 60 --Xmax 1280000 --out results/row_ladder_c0_0.4288.json
python controls.py                                           # certifiers must reject regions with zeros
python coverage_check.py                                     # independent cover check + negative controls (needs the dvp/ladder rows)
python coverage_check.py --full-row results/row_X55o8_c0_0.48_t0.4_y0.4.json 30    # whole-strip re-check (also 0.45, 0.42)
python cost_model.py                                         # projections (needs envelope.json)
python summarize.py                                          # results/summary.json + tables
```

`--t0`, `--y0` and `--X` are read as exact decimals or fractions, and every Arb computation uses balls
that contain them. The design-A commands above were run with `--workers 30`.

### Files

| file | role |
|---|---|
| `p15_float.py` | float/mpmath versions for exploration (not certificates) |
| `p15_arb.py` | Arb: α, M₀, M_t, f_t, f_t′, C_t/B_t, exact e_A e_B e_C e_{C,0}; direct H_t via (35) and via (4) |
| `canopy_analytic.py` | float Lemma 8.5 edge bound (exploration, cross-checks) |
| `canopy_analytic_arb.py` | certified Lemma 8.5 edges (N-intervals), crude tail, far bound, `analytic_certificate` |
| `rigor.py` | exact cover helpers: hull balls, directed rounding f_down/f_up, exact-endpoint grids, containment and tiling checks (section 4.6) |
| `canopy_mesh.py` | Taylor-model box certification of the canopy strip; `n_segments` + `audit_segments` (the N-segment lemma) and the run-time coverage audit |
| `coverage_check.py` | independent coverage check of the evaluated Arb boxes, with negative controls on the pre-repair constructions; `--full-row` re-checks a whole certified strip (section 4.6) |
| `smallx.py` | Φ-integral boxes for (i), the barrier at 55/8, and left edges |
| `certify_route.py` | design A driver (and generic analytic + left edge + strip) |
| `barrier_large.py` | designs B and C (large-X barrier, X selection, dVP arithmetic) |
| `uniform_small_x.py` | parameter-free certificates U1, U2, U2′ |
| `controls.py` | negative and positive controls for the three certifiers (section 4.5) |
| `envelope.py`, `cost_model.py`, `summarize.py` | envelope, projections, aggregation |
| `results/*.json` | one record per row, plus envelope, cost model, uniform certificates, controls, coverage check, summary |
| `results/superseded_pre_repair/` | the pre-repair records, kept for comparison only (not certificates) |

JSON row schema:

- `t0`, `y0` (exact decimal strings), `c0_exact` (the rational t0 + y0²/2), `code` (post-repair).
- `analytic`: N_s, N₁, minimum edge margins, maximum crude ρ, far bound.
- `left_edge`: x_L, y-range, boxes, minimum margin, audit counts.
- `cond_i` and `barrier`: kind, boxes, minimum \|H\| or margin, audit counts (the large-X barrier also
  has `coverage_audit` with the t-slab tiling).
- `strip`: boxes, evals, Dirichlet terms, CPU seconds, minimum margins, failures, and `coverage_audit`
  (chunk tiling, violations, boxes checked, N-pieces).
- `all_certified_here`.

conjecture1_proved = False.
