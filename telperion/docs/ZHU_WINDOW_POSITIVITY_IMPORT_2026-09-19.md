# Importing Zhu's certified-window Weil positivity (arXiv:2608.24827)

**Date:** 2026-09-19
**Paper:** Xuefeng Zhu, *Weil positivity in compact windows: a finite reduction, certified two-sided
bounds, and a Landau-Widom decay law*, arXiv:2608.24827. v1 submitted 2026-08-25, v2 revised
2026-09-02; the HTML rendering read for this memo is `arxiv.org/html/2608.24827v2`, LaTeXML document
date 2026-09-03.
**Status of this memo:** design + seam analysis. No RH progress is claimed. This is PRE-WALL work,
and the paper's own Theorem 1.4 is the reason: the route it certifies closes doubly exponentially
fast and never reaches the wall. **`conjecture1_proved = False`.**

---

## 0. Why this paper is in scope

A wall-assault facet claimed that no unconditional Weil positivity exists past the classical
threshold `(log 2)/2`. Its own skeptic refuted that with this paper. The refutation is correct: Zhu's
Theorem 1.2 is an unconditional positivity theorem at half-width `L = 0.8`, which is `2.3x` the
classical range.

The paper matters here for three separate reasons, which must not be conflated.

1. Its **method** is this program's certificate machinery almost exactly: a finite PSD matrix, a
   certified quadrature, explicit super-exponentially small tails, and a verified Cholesky residual.
2. Its **barrier** (Theorem 1.4) is a published, quantitative no-go for the positivity route, sharper
   and more explicit than anything this program's own barrier hunt produced. That hunt returned
   "sound and empty".
3. Its **numbers** are already cited on `main`, in `LI_LADDER_COST_MODEL_2026-09-17.md` and in
   `RH_ASCENT_PLAN_2026-09-18.md`. Section 6 below audits both citations against the paper. Both
   survive, with one wording correction.

---

## 1. The paper's statements, as printed

Notation as the paper sets it. `f` is the test function on the prime side, `F = f-hat`,
`g = f * f~` the autocorrelation, `psi = Gamma'/Gamma` the digamma function, `Lambda` von Mangoldt,
`N(T)` the zero-counting function.

### 1.1 The object

Equation (1), the window infimum:

```
lambda*(L) = inf { Q(f) / ||f||_2^2 : f even, real, supp f subset [-L, L] }
```

Equation (2), the geometric side of the explicit formula, for `supp f subset [-L, L]`:

```
Q(f) = 2 F(i/2)^2 + (1/2pi) * integral over R of |F(t)|^2 Psi_L(t) dt
```

Equation (3), the Weil symbol:

```
Psi_L(t) = Re psi(1/4 + it/2) - log pi - sum over {n : log n < 2L} of (2 Lambda(n)/sqrt(n)) cos(t log n)
```

The prime sum is finite because `supp(f * f~) subset [-2L, 2L]`. The comb mass is

```
A_L = sum over {n : log n < 2L} of 2 Lambda(n)/sqrt(n)
```

and the prime comb itself is `P_L(t) = sum over {n : log n < 2L} of (2 Lambda(n)/sqrt(n)) cos(t log n)`.

The paper records the prior record honestly: Yoshida proved positivity for `2L <= log 2`;
Connes-Consani re-proved that range. The paper adds, in its own words, "Claims beyond `log 2` exist
in unrefereed preprints; we do not rely on or compare against them beyond noting their existence."

### 1.2 Theorem 1.1 (One-stroke reduction)

Let `L > 0` and set `T_1 := 2 pi e^{A_L}`. Fix any `T#` for which

```
beta* := log(T# / 2pi) - 1/T# - A_L  >  0.
```

The right-hand side increases in `T#`, so this holds above a unique threshold, which exceeds `T_1` by
an `O(T_1^{-1})` amount (`120.1` against `T_1 = 119.1` at `L = 0.8`). In particular `T# > T_1` is
necessary. Then for every real even `f` with `supp f subset [-L, L]`, equation (4):

```
Q(f) >= R(f) := 2 F(i/2)^2 + (1/pi) * integral from 0 to T# of (Psi_L(t) - beta*) |F(t)|^2 dt
                + beta* ||f||_2^2
```

Moreover, in the Legendre basis of `L^2[-L, L]` the quadratic form `R` is represented by
`beta* I + 2 p p^T + C`, where `C` has entries supported, up to explicitly bounded
super-exponentially small tails, on orders `n <~ e L T# / 2`. Consequently, cutting the basis after
`N` even modes `0, 2, ..., 2N-2` with first discarded order `2N >~ e L T# / 2`: if the leading
`N x N` block has `lambda_min >= lambda_0 > 0`, then

```
Q(f) >= ( min(lambda_0, beta* - eps_D) - eps_B ) ||f||_2^2   for all f with supp f subset [-L, L],
```

where `eps_D` (tail-block deviation) and `eps_B` (leading-tail coupling norm) are explicit,
super-exponentially small constants bounded in the proof; in the certified run of Section 5 both are
below `1e-100`.

The proof (Section 4) is four moves: split `integral from 0 to infinity` at `T#`; apply the envelope
Lemma 3.1 on `[T#, infinity)` where `Psi_L(t) >= log(t/2pi) - 1/t - A_L >= beta*`; localize `C` using
`|j_n(x)| <= x^n / (2n+1)!!`, equation (12); and lift from the leading block by the two-block bound,
equation (13):

```
lambda_min(M_R) >= min( lambda_min(A), lambda_min(D) ) - ||B||
```

for `M_R = [[A, B], [B^T, D]]`, with `lambda_min(D) >= beta* - eps_D` by Gershgorin and
`||B|| <= (||B||_1 ||B||_inf)^{1/2} <= eps_B` by the Schur test.

Remark 4.1 is the property that makes this a certificate rather than an estimate: the proof discards
three quantities, each with a definite sign or an explicit bound, so finer quadrature or larger `N`
can only improve the certified constant, never invalidate it.

### 1.3 Lemma 3.1 (Crude envelope) and Lemma 3.2 (Optimality of the crude constant)

Lemma 3.1. For all `t >= 15/4`,

```
Re psi(1/4 + it/2) - log pi >= log(t/2pi) - 1/t,   hence   Psi_L(t) >= log(t/2pi) - 1/t - A_L.
```

Proved by Binet's second formula, with every constant explicit.

Lemma 3.2. `sup over t in R of P_L(t) = A_L`. Consequently the crude constant `C = A_L` of Lemma 3.1
is already optimal among all pointwise bounds `P_L(t) <= C` valid for every `t`, which is the only
information about the comb that the reduction of Theorem 1.1 uses. The proof is Weyl
equidistribution: `{log p}` is linearly independent over `Q` by unique factorization, so the phases
`(t log p_1, ..., t log p_r)` equidistribute mod `2pi` on the full torus, and `t` can be chosen so
that every `k theta_p` lies simultaneously arbitrarily close to `0`.

Remark 3.3 is load-bearing for this import and is discussed in Section 4.2 below: a per-prime
"sharpening" `A_eff = sum_p mu_p` with `mu_p = -min_{theta in [0,pi]} sum_k c_{p,k} cos(k theta)`
satisfies `inf_t P_L(t) = -A_eff` and is often much smaller than `A_L` (at `L = 1.19`,
`A_eff = 4.6948` against `A_L = 7.0750`). Substituting it into Lemma 3.1 **is wrong**: it bounds the
comb from below, hence the symbol from above, whereas the envelope needs an upper bound for `P_L`.
An earlier draft of the paper made exactly this substitution, and the resulting support-`2.38` claim
is retracted.

### 1.4 Theorem 1.2 (Certified positivity, support 1.6)

For every real even `f` in `L^2(R)` with `supp f subset [-0.8, 0.8]`,

```
Q(f) >= 8.9e-18 * ||f||_2^2.
```

In particular the Weil form is positive on all autocorrelations `g = f * f~` with
`supp g subset [-1.6, 1.6]`.

The certificate (Section 5): `T# = 200`, `beta* = 0.5134667...`, `N = 200` even Legendre modes
`0, 2, ..., 398`, working precision 50 digits. The `C`-matrix is integrated over `[0, 200]` in 800
panels of width `1/4` with 32-point Gauss-Legendre quadrature; spherical Bessel values by Miller's
backward recurrence; the pole vector by Gauss quadrature of order 320. Error budget:

| quantity | bound | source |
|---|---|---|
| per-entry quadrature error `eps_Q` | `<= 1.03e-44` | Lemma 5.1, Bernstein ellipse `rho = 6.55`, strip `|Im t| <= 0.4` |
| error-matrix spectral norm `c_err = N eps_Q` | `<= 2.06e-42` | same |
| tail-block deviation `eps_D` | `<= 1e-100` | Gershgorin on rows of `D`, cut order 400 |
| coupling norm `eps_B` | `<= 1e-100` | Schur test |
| Cholesky residual `r` | `1.06e-50` | Lemma 5.2 |
| product-rounding slack `s` | `3.6e-43` | Lemma 5.2 |
| shift `lambda_0` | `9e-18` | the Cholesky is run on `A~ - (lambda_0 + c_err) I` |

Lemma 5.2 (Cholesky residual) is the whole verified-PSD step: if a floating-point Cholesky produces
`L~` with `||M' - L~ L~^T||_inf <= r`, then `lambda_min(M') >= -(r + s)`. Proof: `L~ L~^T >= 0` and
Weyl's inequality. Feeding `lambda_min(A) >= 9e-18 - 4e-43` into Theorem 1.1 gives the `8.9e-18` of
Theorem 1.2, "with an explicit positive margin of `1e-19` to spare".

Independent checks are reported in Section 5.5: a second certification at `T# = 150`
(`beta* = 0.2241`) giving `lambda_min >= 1.2e-18`; monotonicity of `R_{T#}` in `T#`; a reference
non-certified spectrum of `R_150` with bottom eigenvalues
`1.356e-18, 2.32e-12, 2.9e-7, 2.1e-3, beta*, ...`; and the external agreement of the certified upper
bound `2.27e-17` with the measured window floor `1.656e-17`.

### 1.5 Theorem 6.2 (Simple even ground state, support 1.6) and Corollary 6.3

```
8.9e-18 <= lambda_1^even <= 2.523e-16,     lambda_2^even >= 2.085e-12,
8.206e-15 <= lambda_1^odd <= 2.347e-14.
```

The bottom of the window spectrum lies in the even sector with clearance at least a factor 32 against
the odd sector and `8e3` against the second even value: the ground state is simple, and even.
Corollary 6.3 removes the parity and reality restriction: for every complex `f` in `L^2(R)` with
`supp f subset [-0.8, 0.8]`, `Q(f) >= 8.9e-18 ||f||_2^2`.

The paper states that this is the first of the two missing spectral hypotheses in the operator
program of Connes-Consani-Moscovici and Connes-van Suijlekom, verified at a fixed scale with explicit
constants. That scoping ("at a fixed scale") is the paper's own and must be preserved in any citation.

### 1.6 Theorem 1.3 (conditional upper bound) and Conjecture 12.1 (the decay law)

Theorem 1.3. Assume RH. There is an `L_0` such that for all `L >= L_0`,
`lambda*(L) <= exp(-L e^L)`.

Conjecture 12.1. As `L -> infinity`,

```
-ln lambda*(L) = 2 pi^2 * N(T*) / ln N(T*) * (1 + o(1)),
T* = 2 pi e^{2L},   N(T*) = e^{2L} (2L - 1) + O(L).
```

Remark 12.2 is explicit that **the constant is fitted**: "The shape `N/ln N` is what the data above
discriminate; the constant `2 pi^2` is read off the plateau and is not derived here." The evidence is
`R_1 = 1.015, 1.020, 1.027, 1.020` at `L = 1.4, 1.6, 1.8, 2.0`, flat to within `1.3%`, with the
caveat that `R_1` has overshot 1 and is drifting slowly upwards and that four points at `L <= 2`
cannot separate a finite-size correction from a slightly larger asymptotic constant.

### 1.7 The two-sided enclosure

```
8.9e-18 <= lambda*(0.8) <= 2.27e-17,        a factor 2.6.
```

The paper claims this is, to its knowledge, the first RH-equivalent quantity whose window profile has
been enclosed from both sides by certified computation.

---

## 2. Independent numeric check of the finite part

Everything in the paper that is a *finite arithmetic function of `L` and `T#`* was recomputed here
from the definitions, in `mpmath` at 40 digits, with no reference to the paper's code. This is the
only part of the paper that can be checked without reproducing its quadrature, and it checks out
exactly.

| quantity | recomputed | as printed in the paper |
|---|---|---|
| `A_L` at `L = 0.8` | `2.94197352522` | `2.9419735...` |
| `beta*` at `T# = 200` | `0.513466774915` | `0.5134667...` |
| `beta*` at `T# = 150` | `0.22411804` | `0.2241` |
| `T_1 = 2 pi e^{A_L}` at `L = 0.8` | `119.09` | `119` |

The full `T_1` threshold table of Remark 3.3 reproduces at every row:

| `L` | recomputed `A_L` | recomputed `T_1` | paper `A_L` | paper `T_1` |
|---|---|---|---|---|
| 0.8 | 2.9419735 | 119.09 | 2.9420 | 119 |
| 1.0 | 5.8524684 | 2187.1 | 5.8525 | 2187 |
| 1.19 | 7.0750056 | 7427.0 | 7.0750 | 7.4e3 |
| 1.2 | 8.5209909 | 31535 | 8.5210 | 3.2e4 |
| 1.4 | 10.290342 | 1.8502e5 | 10.290 | 1.9e5 |
| 1.6 | 14.323245 | 1.044e7 | 14.323 | 1.0e7 |
| 2.0 | 24.383292 | 2.4418e11 | 24.383 | 2.4e11 |

Conclusion: the finite skeleton of the reduction is exactly as printed, and the strict inequality
`log n < 2L` (not `<=`) is the one the paper uses. This matters for the emitter in Section 5, because
re-deriving `A_L` from `L` is the check that separates a real window-floor certificate from the
retracted one.

**What this check does NOT establish.** It does not verify the quadrature, the Cholesky, the tail
bounds, or `lambda_0 = 9e-18`. Those are reproducible only by rerunning the paper's pipeline, and
they are the numerical-certification seam of Section 4.3.

---

## 3. What the program already has that makes a window statement expressible

`RH_limit_explicit_formula` is `status = "proved"` in the `rh` mission, discharged by
`telperion/examples/rvm_bridge/lean/E6Bridge4.lean`, with read-back testimony in
`AUDIT_TESTIMONY_E8_2026-09-18.md`. It states, for `g` smooth and compactly supported:

```lean
theorem limit_explicit_formula (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
    Integrable (WeilExplicit.archIntegrand g) ∧
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel g ρ)
      (WeilExplicit.archSide g - WeilExplicit.primeSide g)
```

The `weil_form_enclosure` island adds `WeilForm.weilForm f = archSide f - primeSide f` and
`WeilForm.crossCorr` / `WeilForm.autocorr`. So the program can already *write down* Zhu's `Q`:

```
Q(f)  =  (WeilForm.weilForm (WeilForm.autocorr f)).re
```

This is what makes a window statement expressible at all. It is also the limit of what is free: the
identity `Q(f) = 2 F(i/2)^2 + (1/2pi) integral |F|^2 Psi_L`, Zhu's equation (2), is a *rearrangement*
of the proved explicit formula into frequency variables, and that rearrangement is not proved
anywhere on `main`.

---

## 4. SEAM ANALYSIS

This is the section the import stands or falls on. The question is not "is the paper right" (it
appears careful, and its finite skeleton checks out exactly), but "which parts of it can enter this
program as kernel-checked theorems, which as named hypotheses, and which as declared numerical trust
boundaries".

**Verdict up front.** The load-bearing step, "infinite-dimensional problem -> one finite PSD matrix",
is *not* one step. It is a chain of four analytic moves and one numerical certification, and only the
last analytic move is within reach of this program today. A Lean node that claims Theorem 1.2 as a
theorem would be a certified NUMBER masquerading as a proved THEOREM. The node must be conditional,
and its title must say so.

### 4.1 Genuinely finite and kernel-checkable (category i)

These are exact arithmetic on rationals and integers, decidable, with no analysis in them.

| item | why it is finite | status |
|---|---|---|
| `A_L = sum_{log n < 2L} 2 Lambda(n)/sqrt(n)` | a finite von Mangoldt sum; at `L = 0.8` it is three terms, `n = 2, 3, 4` | recomputed exactly (Section 2); kernel-checkable as a rational enclosure |
| `beta* = log(T#/2pi) - 1/T# - A_L > 0` | one transcendental evaluation with an enclosure, then rational arithmetic | kernel-checkable from enclosures of `log` |
| `T_1 = 2 pi e^{A_L}` and the test `T# > T_1` | same | kernel-checkable |
| the cut-order condition `2N >~ e L T# / 2` | integer comparison | decidable |
| the closing arithmetic `min(lambda_0, beta* - eps_D) - eps_B > 0` | rational arithmetic on four literals | `norm_num` |
| the two-block bound, equation (13) | pure finite-dimensional linear algebra, an inner-product estimate plus `2|x||y| <= |x|^2 + |y|^2` | **provable in Lean today**; the only analytic move of Theorem 1.1 that is |
| Lemma 5.2 (Cholesky residual) | `L~ L~^T >= 0` plus Weyl's inequality | provable in Lean given a PSD-of-Gram lemma |

Two of these deserve emphasis. Equation (13) and Lemma 5.2 are *real theorems that this program could
hold in the kernel*, and they are the frame of the whole certificate. Everything else in the chain is
either analysis or arithmetic-on-enclosures.

### 4.2 Analytic theorems that must be proved or carried as hypotheses (category ii)

| item | what it needs | verdict |
|---|---|---|
| **Equation (2)**: `Q(f) = 2 F(i/2)^2 + (1/2pi) integral |F|^2 Psi_L` | Parseval plus the change of variables from `RH_limit_explicit_formula`'s `archSide - primeSide` into the frequency integral; `Psi_L` assembled from `Re psi(1/4 + it/2)`, `log pi` and the finite comb | **hypothesis.** Not proved on `main`. It is a rearrangement of a proved theorem, so it is the most likely of these to be dischargeable, but it is not free: it needs the Fourier-Plancherel bridge for the autocorrelation and the `F(i/2)` pole identification. |
| **Lemma 3.1** (the envelope): `Re psi(1/4 + it/2) - log pi >= log(t/2pi) - 1/t` for `t >= 15/4` | Binet's second formula for `psi`, a bound on `integral u du / ((u^2+z^2)(e^{2 pi u}-1))`, and `integral_0^infinity u du/(e^{2 pi u}-1) = 1/24` | **hypothesis.** Mathlib's digamma support does not reach Binet's second formula. This is a genuine, self-contained analytic lemma and a plausible standalone target, but it is not available now. |
| **Parseval on the half-line**: `integral_0^infinity |F|^2 = pi ||f||^2` for even real `f` | Plancherel plus evenness | **hypothesis**, though the cheapest of the four. |
| **Equation (6) / the Legendre transform identity** and `|j_n(x)| <= x^n/(2n+1)!!` (equation 12) | spherical Bessel functions, their Poisson representation, and Legendre coefficients | **hypothesis.** Spherical Bessel functions are not in Mathlib. This is the single largest missing apparatus. |
| **Lemma 5.1** (Bernstein-ellipse quadrature bound) | analytic continuation of the integrand to an ellipse, and the classical Gauss-Legendre error bound | **hypothesis.** The classical bound is not in Mathlib. |
| **Lemma 3.2** (`sup_t P_L(t) = A_L`) | linear independence of `{log p}` over `Q` (unique factorization) plus Weyl equidistribution on the torus | **hypothesis.** Needed only for the *barrier*, never for the positivity. |

The honest reading: the phrase "one-stroke reduction" describes the *shape* of the argument, not its
cost in a proof assistant. In Lean the reduction has five named analytic inputs, of which none is
currently available on `main`.

**The retraction is the reason to be ruthless here.** The paper's own earlier draft substituted
`A_eff` for `A_L` in Lemma 3.1 and thereby claimed a support-`2.38` theorem it has now withdrawn.
That error lived *precisely* at this seam: a finite, correct, independently meaningful number
(`A_eff = 4.6948`, the depth of the wells of `Psi_L`) was plugged into a slot that requires a
different finite number (`A_L = 7.0750`, its high-frequency floor). No amount of numerical
certification downstream catches it, because everything downstream was internally consistent. Only
re-deriving the constant from its definition catches it. That observation is what the emitter in
Section 5 is built around.

### 4.3 Numerical certification: the Arb / interval trust boundary (category iii)

These enter exactly as the existing zero-localization ladder's numbers enter, and on exactly the same
terms: **the emitted Lean never asserts the enclosure; it takes the enclosure as a named hypothesis
and the kernel proves only its consequence.** This is the discipline already written into
`emit_weil_form_enclosure.py` (the `henc` seam) and the Li ladder.

| item | value at `L = 0.8` | trust boundary |
|---|---|---|
| `lambda_0`, the leading `200 x 200` block floor | `9e-18` | mpmath/gmpy2 at 50 dps, verified Cholesky at a shift; **non-kernel** |
| `c_err`, error-matrix spectral norm | `<= 2.06e-42` | Bernstein-ellipse bound evaluated numerically; **non-kernel** |
| `eps_D`, `eps_B` | `<= 1e-100` each | Gershgorin / Schur sums over entry bounds; **non-kernel** |
| `r`, `s` (Cholesky residual and slack) | `1.06e-50`, `3.6e-43` | computed in the same arithmetic; **non-kernel** |
| the certified upper bounds of Table 3 | `2.27e-17` at `L = 0.8` down to `3.19e-283` at `L = 2.0` | `mpmath.iv` interval re-evaluation on the geometric side; **non-kernel** |

Three things about the upper-bound pipeline are worth importing as *method*, because they are better
practice than a bare "we computed it".

1. **Proposal versus certificate** (Remark 11.5). The eigensolver's output is treated as a mere
   proposal; the certified bound comes only from an interval re-evaluation of the Rayleigh quotient,
   which is valid for *any* coefficient vector whatsoever, so no property of the proposal needs to be
   trusted. This is the same move as this program's "the kernel only sees the consequence".
2. **The closure caught a real error** (Remark 11.6). At `L = 2.0` the interval re-evaluation exposed
   a proposal of `8.2e-281` as unattainable; the true Rayleigh quotient of that vector was
   `2.5e-276`, four orders of magnitude larger. The paper's conclusion is the one this program should
   adopt verbatim: "only a bound re-derived independently of the model deserves trust."
3. **Scope of the certification** (Remark 11.7). What is certified is that each number is an upper
   bound for `lambda*(L)`. What is *not* certified is proximity to `lambda*(L)`.

**One caution on the zeros-side data** (Remark 11.3). The 1000 zeros used are
`mpmath.zetazero` values, "high-confidence multiprecision computations, not formally verified
enclosures". The paper is careful that this never enters the unconditional claims: the zeros-side
assembly only *proposes* trial vectors, and the unconditional certificates of Table 3 are
geometric-side. Any import must preserve that separation. A citation of `3.2e-283` that attributes it
to a zeros-side computation would be wrong.

**One numeric discrimination to preserve.** Table 3's certified geometric-side upper bound at
`L = 2.0` is `3.19e-283` (the abstract's `3.2e-283`). Remark 11.6's `4.2e-283` is the *zeros-side*
cross-check at `J = 80`. These are different numbers from different pipelines and should not be
interchanged.

### 4.4 The seam verdict, stated plainly

The reduction "infinite-dimensional problem -> one finite PSD matrix" **cannot be proved with what is
available**. It decomposes as:

```
[proved on main]  RH_limit_explicit_formula
   -> [HYPOTHESIS]  equation (2), the frequency-side rearrangement
   -> [HYPOTHESIS]  Lemma 3.1, the digamma envelope
   -> [HYPOTHESIS]  Parseval on the half-line
   -> [provable]    the frequency split, equation (4)
   -> [HYPOTHESIS]  the Legendre/spherical-Bessel localization, equations (6) and (12)
   -> [PROVABLE]    the two-block bound, equation (13)
   -> [TRUST SEAM]  lambda_0, eps_D, eps_B from Arb/mpmath
   -> [kernel]      min(lambda_0, beta* - eps_D) - eps_B > 0 by norm_num
```

So the node carries the analytic chain as named hypotheses and says so in its title.

---

## 5. What an honest Lean node would claim

### 5.1 The node

Authored with the mission CLI into the `rh` campaign, `kind = "lemma"`, `status = "draft"`, statement
only, no proof, no `[proof]` block.

**Name:** `RH.weil_window_floor_of_certified_block`

**Vocabulary.** `RHDefs.lean` is GENERATED by `missions/rh/build_rhdefs.py` and must never be
hand-appended, so the new block is added there as `WEIL_WINDOW_BLOCK` and regenerated. It has two
parts. `WeilForm` (`weilForm`, `crossCorr`, `autocorr`) is a VERBATIM mirror of the
`weil_form_enclosure` island's `WeilFormDefs.lean`, checked byte-for-byte, so island and registry
cannot silently decouple; renaming those names into a fresh namespace would have created exactly the
divergence the mirror discipline exists to prevent. `WeilWindow` adds only what is genuinely new.
`WeilExplicit` already exists in `RHDefs.lean` and is reused unchanged.

```lean
/-- Zhu's window infimum predicate: the Weil form `Q(f) = Re weilForm (autocorr f)` is bounded
    below by `lam * ||f||_2^2` on every smooth compactly supported test function supported in
    `[-L, L]`.  `WindowFloor L lam` with `lam > 0` at a given `L` is a finite fragment of RH;
    `forall L, WindowFloor L 0` is RH-equivalent (Weil 1952; Bombieri 2000). -/
def WindowFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

/-- The comb mass `A_L = sum_{log n < 2L} 2 Lambda(n)/sqrt n` (a FINITE sum). -/
noncomputable def combMass (L : ℝ) : ℝ :=
  ∑' n : ℕ, if Real.log n < 2 * L then 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0

/-- Zhu's reduced form floor: the hypothesis that the finite Legendre head of the reduced form
    `R` of equation (4), cut after `N` even modes, has least eigenvalue at least `lam0`.  This is
    the Arb/mpmath TRUST SEAM, carried as a hypothesis and never asserted by the kernel. -/
def ReducedHeadFloor (L Tsharp lam0 : ℝ) (N : ℕ) : Prop := ...
```

**Statement:**

```lean
theorem weil_window_floor_of_certified_block
    (L Tsharp A beta lam0 epsD epsB : ℝ) (N : ℕ)
    -- the FINITE data, re-derivable by exact arithmetic
    (hA    : A = WeilWindow.combMass L)
    (hbeta : beta = Real.log (Tsharp / (2 * Real.pi)) - 1 / Tsharp - A)
    (hbpos : 0 < beta)
    (hcut  : (2 * N : ℝ) ≥ Real.exp 1 * L * Tsharp / 2)
    -- the ANALYTIC chain of Theorem 1.1, NAMED AND UNDISCHARGED
    (hQrep : WeilWindow.SymbolRepresentation L)        -- Zhu eq. (2)
    (henv  : WeilWindow.EnvelopeBound)                  -- Zhu Lemma 3.1
    (hloc  : WeilWindow.LegendreLocalization L Tsharp N epsD epsB)  -- Zhu eqs. (6), (12)
    -- the NUMERICAL certification, the Arb trust seam
    (hhead : WeilWindow.ReducedHeadFloor L Tsharp lam0 N)
    (hpos  : 0 < min lam0 (beta - epsD) - epsB) :
    WeilWindow.WindowFloor L (min lam0 (beta - epsD) - epsB)
```

**Title** (says what it assumes, in the style of the program's other honest conditional nodes):

> Zhu's one-stroke window reduction (arXiv:2608.24827 Thm 1.1), CONDITIONAL on four named,
> UNDISCHARGED inputs -- the frequency-side symbol representation (eq. 2), the digamma envelope
> (Lemma 3.1), the Legendre/spherical-Bessel localization (eqs. 6 and 12), and an Arb-certified
> least-eigenvalue floor `lam0` for the finite Legendre head -- concludes a positive window floor
> `min(lam0, beta* - epsD) - epsB` for the Weil form on `supp f subset [-L, L]`. STATED ONLY, not
> proved. Numerically instantiated at `L = 0.8` by Zhu's certificate (`8.9e-18`), but the kernel
> asserts NO number; `conjecture1_proved = False`.

### 5.2 What the node deliberately does NOT claim

- It does **not** claim `WindowFloor 0.8 8.9e-18` unconditionally. That would be the certified number
  masquerading as a theorem.
- It does **not** claim anything about `forall L`. `forall L, WindowFloor L 0` is the RH-equivalent
  clause and is untouched.
- It does **not** claim a lower bound on `lambda*(L)` is *sharp*, and it does not import the upper
  bounds as theorems at all. The upper bounds are a separate shape (a Rayleigh quotient of one
  explicit trial vector) and would be a separate node if wanted.
- It does **not** import Theorem 6.2 or Corollary 6.3. The parity result is the same reduction run on
  the odd sector, so it inherits the identical seam; there is no reason to author two conditional
  nodes with the same undischarged chain.

### 5.3 Trivial-close probes (recorded, as required)

Three probes were considered against the statement, to check it is not closable for a stupid reason.

1. **Empty-class probe.** Is the hypothesis set of test functions nonempty? Yes: smooth compactly
   supported bumps supported in `[-0.8, 0.8]` exist, so `WindowFloor` is not vacuously true by an
   empty quantifier. **Closes nothing.**
2. **Zero-function probe.** Does `f = 0` make the conclusion trivial? It satisfies it with both sides
   zero, but it does not make the `forall` trivial. **Closes nothing.**
3. **Empty-prime-sum probe.** The `RH_ASCENT_PLAN` correctly warns that `L* >= (log 2)/2` is the
   *empty-prime-sum range*: for `2L < log 2` every `Lambda(n)` term with `n >= 2` dies and only the
   archimedean term survives, so clearing that floor is vacuous. Does this node sit in that vacuous
   range? **No.** At `L = 0.8`, `2L = 1.6 > log 2 = 0.693`, and `A_L` has three live terms
   (`n = 2, 3, 4`). The prime side is genuinely present. **Closes nothing**, and this is the probe
   that matters.

---

## 6. Audit of the program's existing citations of this paper

### 6.1 `LI_LADDER_COST_MODEL_2026-09-17.md`

It says:

> **Window certification cost is doubly exponential in support** (Zhu 2608.24827: -ln lambda_min(L)
> ~ the Landau-Widom rate) -- the B3/B9 Weil-Gram route buys support only at that price; "grow L"
> has no known method (roadmap B9).

**Accurate in substance, with one wording correction.** The bullet fuses two distinct results of the
paper that have *different logical status*, and the fused form reads as though both were proved:

- the **certificate size** grows doubly exponentially in `L` (Theorem 1.4, **unconditional, proved**,
  via `A_L ~ 4 e^L` and `T_1 = 2 pi e^{A_L}`);
- the **margin** collapses at the Landau-Widom rate (Remark 1.5 and Conjecture 12.1, **measured, not
  proved**; the paper keeps it outside the theorem for exactly this reason, and Remark 12.2 says the
  constant `2 pi^2` is fitted).

The bullet's own parenthetical attributes the second to the paper as if it were the citation for the
first. The recommended correction is to split it, or to write "certificate size doubly exponential
(Thm 1.4, proved); margin collapse at the Landau-Widom rate (Rmk 1.5, measured)". Also,
the paper's symbol is `lambda*(L)`, not `lambda_min(L)`.

### 6.2 `RH_ASCENT_PLAN_2026-09-18.md`

Its item 2 under the "not the wall" list says:

> **`WeilPositiveOn L` for L beyond the certified window -- NOT the wall, but not staffed.** A
> finite, well-posed, genuinely open computational-analytic problem, blocked by the Landau-Widom
> decay law: certification cost is doubly exponential in L, the published enclosure at L = 0.8 is
> already 8.9e-18 ... 2.27e-17 and falls to ~3.2e-283 at L = 2. It buys about one decimal of L per
> major effort and never reaches the wall.

**Accurate.** Every number matches the paper (Section 1.7 and Table 3 above), including the correct
use of `3.2e-283` as the `L = 2.0` value. The characterisation "buys about one decimal of `L` per
major effort" is a fair reading of the `T_1` table.

Its refusal of the route-A facet's escalation is also **correct and should be preserved**:

> the route-A facet's "quantitative kill" -- that `lambda_min(L) -> 0` doubly-exponentially makes the
> instrument class *provably* the wrong shape -- is not carried. [...] The underlying observation is
> Zhu's own last abstract sentence, carefully scoped to *one-stroke certificates*.

This is exactly right, and it is the single most important scoping point in this whole import.
Theorem 1.4 is a barrier for **pointwise-envelope certificates**, and Lemma 3.2 is what makes it
tight *within that class*. It is not a barrier for positivity arguments in general. Under RH the
explicit formula gives `Q(f) >= 0` for every `L` with margin identically zero, and a closed condition
needs no uniform margin. Any import that upgrades Theorem 1.4 into "no positivity argument can reach
RH" is misquoting the paper.

---

## 7. The barrier, with its constants, and what it forecloses

### 7.1 Theorem 1.4 (Barrier for pointwise-envelope certificates), as printed

> Any application of Theorem 1.1 requires `T# > T_1(L) = 2 pi e^{A_L}`, and `A_L = (4 + o(1)) e^L` as
> `L -> infinity` by the prime number theorem; hence the matrix size `N ~ L T_1` and the number of
> quadrature nodes grow doubly exponentially in `L`. Moreover `sup_t` of the prime comb equals `A_L`
> exactly (Lemma 3.2), so within the class of certificates that bound the comb pointwise the
> threshold `T_1` cannot be lowered.

Unconditional. Proved in Section 14.1, in four lines: `beta* > 0` forces `T# > T_1`; Lemma 3.2 says
no pointwise bound beats `A_L`; PNT gives `A_L ~ 4 e^L`; hence `T_1 = 2 pi exp((4 + o(1)) e^L)`.

### 7.2 The constants

| constant | value | status |
|---|---|---|
| comb mass asymptotic | `A_L = (4 + o(1)) e^L` | proved, by PNT |
| frequency threshold | `T_1(L) = 2 pi e^{A_L}`, i.e. `2 pi exp((4 + o(1)) e^L)` | proved |
| matrix size | `N ~ L T_1` | proved |
| resolution height | `T* = 2 pi e^{2L}` | definition; its role is measured |
| decay law | `-ln lambda*(L) ~ 2 pi^2 N(T*) / ln N(T*)` | **measured, not proved** (Rmk 1.5, Conj 12.1) |
| Landau-Widom constant | `2 pi^2 = 19.74`; fitted value `20.13 +/- 0.10`, ratio `1.020` | **fitted** (Rmk 12.2) |
| zero count | `N(T*) = e^{2L} (2L - 1) + O(L)` | standard |
| conditional decay | `lambda*(L) <= exp(-L e^L)` for large `L`, **assuming RH** | proved, Thm 1.3 |
| practical ceiling | support `~ 3.2`, where `T_1 ~ 1e7` | Remark 1.6 |

Measured floor collapse, from Table 3 and Remark 1.5: `1e-17` at `L = 0.8`, `1e-48` at `L = 1.2`,
`1e-283` at `L = 2.0`.

### 7.3 What it forecloses for Route B, bluntly

1. **"Grow `L` until the window is everything" is dead as a method.** The cost is
   `2 pi exp(4 e^L)`. Past support `~ 3.2` the paper's own word is that pointwise-envelope
   certification is "computationally void". Route B cannot reach `forall L` by extending the
   certified window, and no engineering effort changes the exponent.
2. **The margin dies faster than precision can be bought.** Working precision must track
   `-ln lambda*`, which is `~ 2 pi^2 N(T*)/ln N(T*)`. At `L = 2` that is 283 decimal digits for a
   single *upper* bound; a lower bound at that support needs the doubly exponential matrix as well.
   The two exponentials are independent and both must be paid.
3. **Sharpening the envelope is provably closed off.** Lemma 3.2 is not a "we could not do better";
   it is `sup_t P_L(t) = A_L` exactly, by Weyl equidistribution. The paper's own retracted
   support-`2.38` claim is the worked example of what trying to beat it looks like.
4. **The escape route is arithmetic, and it is the thing being circumvented.** Remark 1.6 and
   Section 14.3: to improve on pointwise envelopes one must prove that the phases `(t log p)_p`
   cannot align, "an arithmetic statement about simultaneous Diophantine approximation of
   `{log p}`, of the same nature as the information carried by the zeros themselves". The paper's
   closing sentence is the one to quote: "the positivity route, continued past the wall, runs back
   into the arithmetic of the zeros it was trying to circumvent."
5. **What it does NOT foreclose.** Theorem 1.4 is scoped to certificates that bound the comb
   *pointwise*. It says nothing about limiting, compactness or interpolation arguments, and Section
   14.2 is explicit that converting the measured law into a proved lower bound on the cost of an
   *arbitrary* positivity certificate "remains open" and would require the sampling theory of low
   zeta zeros. The `RH_ASCENT_PLAN`'s refusal to carry the escalated kill is correct.

### 7.4 Three failed routes worth recording

Section 15 lists alternatives Zhu implemented and abandoned. They are free negative results for this
program, since two of them are shapes it has considered.

1. **Galerkin solve-lemmas**: inverses are rough in `L^2[-L,L]`, residuals decay only polynomially,
   and the required `1e-80` tolerances are unreachable.
2. **Symbol capping** (replace `Psi_L` beyond `T_delta` by a constant minorant): *provably fatal*.
   Once the window resolves the cap the form becomes indefinite, measured `lambda_min ~ -2.7`.
   "Capping the symbol amounts to admitting fake zeros."
3. **Order-space block certificates**: the prime terms are shift operators, so any hard cut in
   Legendre-order space leaves `O(1)` coupling across the interface; the collective edge directions
   lose `~ -2.4` against a supply that grows only logarithmically.

Point 3 is the direct justification for the frequency-space formulation, and it is the reason the
tail coupling `eps_B` in Theorem 1.1 is `1e-100` rather than `O(1)`.

---

## 8. Certificate-shape decision

`telperion/src/telperion/emitter_sensitivity.py` `REGISTRY` is keyed by emitter class name, and the
certificate kinds live in `certify.py`. The candidates named in the brief were checked directly.

| existing kind | what it does | why it does not cover this |
|---|---|---|
| `weil_form_enclosure` | Arb enclosure of `Re weilForm` for a *finite family of explicit test functions*; emits `positivity` (`0 < lo`) or `gram_minor` (2x2 Sylvester) | covers **one `f` at a time**, or a `2 x 2` Gram block. It has no uniform floor over a whole window, no `beta*`, no `A_L`, and no tail constants. Zhu's claim quantifies over *every* `f` in `[-L, L]`. |
| `interval_gram_inertia` | exact signature `(p, q)` shared by every Hermitian matrix in a rational interval box | certifies *inertia*, not a quantitative floor, and **explicitly refuses the definite case** (`p == 0` or `q == 0` are refused, delegated to `psd_form`). Zhu's block is definite and the number that matters is `lambda_0`, not a signature. |
| `psd_form` | exact rational PSD of one explicit matrix | no interval, no floor, no lift. |
| `rayleigh_gram` | a variational LOWER bound on `lambda_max` of a symmetric pencil, from one explicit direction | wrong end of the spectrum and wrong direction. Zhu needs a floor under `lambda_min`. |
| `tight_cap_enclosure`, `bragg_floor` | different shapes (cap enclosure; per-order Bragg-vs-floor inequality) | unrelated. |

**Decision: mint one new kind, `window_form_floor`.** The gap is real and specific: nothing in the
registry expresses *a finite certified block floor lifted to a floor on an infinite-dimensional form,
with the lift's tail constants and the reduction's threshold constant carried explicitly*. That
bundle, `(L, T#, A_L, beta*, lambda_0, eps_D, eps_B, N)` closing on
`min(lambda_0, beta* - eps_D) - eps_B > 0`, is the paper's contribution at the certificate layer.

### 8.1 The anti-phantom face, and why it is unusually strong here

The refusals are not decoration. The emitter **re-derives `A_L` from `L` by exact von Mangoldt
summation and `beta*` from `(T#, A_L)`**, and refuses any instance whose declared constants do not
match. That is the check that catches the paper's own retracted error: substituting
`A_eff = 4.6948` for `A_L = 7.0750` at `L = 1.19` yields a `beta*` that looks positive at a `T#`
far below `T_1 = 7427`, and every downstream number stays self-consistent. Only re-derivation from
the definition catches it.

The negative-control twin is therefore **the published retraction itself**: the forged certificate is
the retracted support-`2.38` instance built on `A_eff`, and the true twin is the real `L = 0.8`
certificate. A control keyed to a real, documented, published error is worth more than a synthetic
sign flip.

Full refusal list:

1. `beta* <= 0` -- the reduction's hypothesis fails; `T#` is below threshold.
2. `T# <= T_1 = 2 pi e^{A_L}` -- the barrier threshold, restated as a guard.
3. declared `A_L` disagrees with the exact recomputed comb mass for `L` -- **the retraction guard**.
4. declared `beta*` disagrees with `log(T#/2pi) - 1/T# - A_L` -- the constant is re-derived, never
   trusted.
5. `min(lambda_0, beta* - eps_D) - eps_B <= 0` -- no positive floor is implied, so nothing is emitted.
6. `lambda_0 <= 0`, or negative `eps_D` / `eps_B`, or `N` below the cut order `e L T# / 2`.

### 8.2 What the emitter emits, and what was built

Built on branch `feat/zhu-window-positivity`:

| file | role |
|---|---|
| `telperion/src/telperion/emit_window_form_floor.py` | the emitter, kind `window_form_floor` |
| `telperion/tests/test_emit_window_form_floor.py` | 30 tests, TDD, refusals first |
| `telperion/src/telperion/negctrl_adapters/adapter_window_form_floor.py` | the negative-control twin |
| `telperion/examples/window_form_floor/generate.py` | dogfood island generator with `--check` |
| `telperion/examples/weil_form_enclosure/lean/WindowFormFloorInstances.lean` | the emitted Lean |
| `telperion/examples/weil_form_enclosure/lean/AxiomGuardWindowFormFloor.lean` | the axiom guard |

The instances are emitted INTO the existing `weil_form_enclosure` island rather than a new one, so
they reuse the `WeilExplicit` / `WeilForm` vocabulary and that island's Mathlib v4.32.0 cache. This
is the same honest fallback `bragg_amplitude` uses against the zero-localization island, and it
avoids a fragile cross-package `require`.

**The emitted theorem.** Each instance concludes a window floor at the PUBLISHED constant from a
window floor at the RAW certified one, through a proved monotonicity lemma:

```lean
theorem zhu_window_floor_L08_T200
    (hred : WindowFloor ((4 / 5)) (min ((9 / 10^18)) (((5134667 / 10^7)) - eps) - eps)) :
    WindowFloor ((4 / 5)) ((89 / 10^19)) :=
  windowFloor_of_le hred (by norm_num)
```

So the kernel proves exactly one thing: **that the published rounding is sound**. That is the last
line of Zhu's Theorem 1.2 (raw `9e-18 - 4e-43 - 1e-100`, published `8.9e-18`), and it is the only
step of the chain the kernel can honestly own. Everything else arrives in `hred`.

Verified, not asserted:

- `WindowFormFloorInstances.lean` compiles green against Mathlib v4.32.0.
- All three theorems, including `windowFloor_of_le`, depend on exactly `[propext,
  Classical.choice, Quot.sound]`. No `sorryAx`.
- `generate.py --check` regenerates byte-for-byte.
- The negative control bites in both directions, run through the real kernel: the forged twin
  (published `1e-17` rounded UP past the certified floor) fails with `unsolved goals ... False`;
  the true twin (Zhu's `8.9e-18`) compiles on mathlib's three axioms.
- The certificate-layer control refuses Zhu's own retracted instance, naming the reason.

**A second refusal earned during construction.** The rounding guard fired on the author's own
second instance: Zhu's Section 5.5(a) cross-check at `T# = 150` gives `lam0 = 1.2e-18`, and
publishing `1.2e-18` was refused, because the raw floor is `1.2e-18 - 1e-100`, which is smaller.
The instance now publishes `1.1e-18`. A guard that only ever fires on synthetic forgeries is not
evidence; this one fired on real, honestly-intended input.

**Status.** Category-(b): finite, consistent with RH, proving nothing about RH. `lam0`, `eps_D`,
`eps_B` are Arb/mpmath enclosures, the documented non-kernel trust seam. The four analytic inputs of
Theorem 1.1 are undischarged and are itemized in the registry node, not hidden.

## 9. Summary for the ledger

- **Positive result imported:** Zhu Theorem 1.2, `Q(f) >= 8.9e-18 ||f||^2` for `supp f subset
  [-0.8, 0.8]`, unconditional, `2.3x` the classical `(log 2)/2` range; with Corollary 6.3 removing
  parity and reality, and Theorem 6.2 establishing a simple even ground state at that support.
- **Two-sided enclosure:** `8.9e-18 <= lambda*(0.8) <= 2.27e-17`, factor `2.6`.
- **Seam verdict:** the reduction is four analytic hypotheses plus one numerical trust boundary plus
  two genuinely provable linear-algebra lemmas. The node is conditional and says so in its title.
- **Barrier imported:** Theorem 1.4, unconditional, `T_1 = 2 pi exp((4 + o(1)) e^L)`, matrix size
  doubly exponential, threshold unimprovable within pointwise-envelope certificates by Lemma 3.2.
  Scoped to that class, and the scoping is preserved.
- **Decay law:** `-ln lambda*(L) ~ 2 pi^2 N(T*)/ln N(T*)`, `T* = 2 pi e^{2L}`, **measured and fitted,
  not proved**; fitted constant `20.13 +/- 0.10` against `2 pi^2 = 19.74`.
- **Independent verification done here:** every finite constant (`A_L`, `beta*`, the whole `T_1`
  table) reproduced exactly from the definitions.
- **No RH progress. PRE-WALL. `conjecture1_proved = False`.**
