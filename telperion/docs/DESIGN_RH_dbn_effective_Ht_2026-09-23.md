# M5, the effective approximation of H_t (Polymath15 Theorem 1.3): design memo and first bricks

*Authored 2026-09-23 by lane m5 (worktree `arda-rc-m5`, branch `rc/m5`, off `783998f1b`). Route C
synthesis §5.2 rank 4 and §7.2 (`ROUTE_C_SYNTHESIS_2026-09-23.md:421, :598-600`). Git read-only:
nothing was committed. Nothing under `telperion/missions/` was edited; every registry change below
is a proposal.*

```
+-----------------------------------------------------------------------------------+
| conjecture1_proved = False.                                                       |
| M5 is infrastructure. P15 Theorem 1.3 approximates H_t(x+iy) for x >= 200. It     |
| bounds no Lambda by itself, and nothing in this memo or its Lean bears on RH.     |
| Lambda <= 0 is RH; every Lambda <= c with c > 0 is strictly weaker than RH.       |
+-----------------------------------------------------------------------------------+
```

**Sources.**

- D.H.J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function,
  and a new upper bound for the de Bruijn-Newman constant*, Res. Math. Sci. 6 (2019) art. 31,
  arXiv:1904.12438v2 ("P15").
- The arXiv **LaTeX source** of v2 (`debruijn.tex`), fetched this session. All equation numbers
  below are P15's. Every definition was checked against the source, not against a PDF text
  extraction; section 5 explains why that matters.
- Sections 4-6 of P15 (pp. 16-35) were read in full from the PDF.
- The ANDURIL memo `ANDURIL_ARB_DISCHARGE_2026-09-23.md` and the modules of the `zeta_reflection`
  island that it names.

---

## 0. Summary

**What M5 is.** P15 Theorem 1.3 writes H_t(x+iy)/B_t(x+iy) as an explicit finite Dirichlet-type
sum f_t(x+iy), with explicit error e_A + e_B + e_{C,0}. It holds on the region (5):
0 < t <= 1/2, 0 <= y <= 1, x >= 200. Corollary 1.4 turns it into a finite non-vanishing check:
|f_t| > e_A + e_B + e_{C,0} implies H_t(x+iy) != 0. Every effective Lambda <= c0 < 1/2 by P15's
method consumes it through hypotheses (ii) and (iii) of Theorem 1.2, together with M1 and M4 (M6).

**Delivered by this lane.** Two new modules on the `dbn` island: 1,020 lines, 43 theorems, all
43 within `[propext, Classical.choice, Quot.sound]`.

1. **`DBNM5Alpha.lean` (brick 1, Mathlib-only, 769 lines, 35 theorems).** It covers layers L0-L2
   below:
   - the Stirling-phase vocabulary alpha, log M_0, M_0, log M_t, M_t, s_*, kappa and gamma, with
     `M0_eq_p15_eq6` tying M_0 to P15 (6) verbatim;
   - (log M_0)' = alpha and the formula (42) for alpha';
   - the alpha' bound (43);
   - the reflection symmetries alpha = alpha^*, M_0 = M_0^*, M_t = M_t^*;
   - **Theorem 1.3's explicit parameter bounds (20) |gamma|, (21) Re s_* and (22) |kappa|**, which
     are P15 Prop 6.6 (i)-(iii). Prop 6.6 (ii) is also proved in its own printed form, which differs
     from (21);
   - a corrected P15 (76), and a kernel-checked negative control showing that (76) as printed is
     false.
2. **`DBNM5Target.lean` (251 lines, 8 theorems).**
   - The M5 target `DBNM5.P15Thm13`: Theorem 1.3 (13) as a kernel-elaborated Prop over the
     island's `DBN.H`, with its whole vocabulary (f_t, e_A, e_B, e_{C,0}, B_t, N). **It is not
     proved.**
   - The unnormalized Corollary 6.5 as `DBNM5.P15Cor65`, also not proved.
   - Two proved reductions:
     - `P15Thm13_of_P15Cor65` (layer L13, the normalization step of P15 §6.3);
     - `H_ne_zero_of_P15Thm13` (Corollary 1.4, conditional).
3. **This memo**: the decomposition into 16 layers, line estimates, the ANDURIL sharing map, and six
   P15 findings. The findings are one false display, two proofs that need repair, and three textual
   slips. All six headline claims survive.

**The long pole.** The Riemann-Siegel integral representation (36) and Arias de Reyna's explicit
Riemann-Siegel remainder bounds (Prop 6.2) are unformalized anywhere. Together with an effective
complex Stirling (Lemma 5.1(v)), they are roughly 60-70% of M5. They are the same objects as
ANDURIL's B2, B3, B6 and K5.

**Estimate.** About 12.8k-23.9k lines remain, so M5 totals about 13.8k-24.9k. The synthesis figure
was 10k-20k, unanchored. Of the remainder, 8.5k-16.5k is shared with ANDURIL. The M5-only remainder
is 4.3k-7.4k. Section 7 gives the calibration.

**Recommendation.** Build the Riemann-Siegel representation and the Arias de Reyna bounds **once**:
for general sigma and general K, Mathlib-only, at one toolchain pin. They then serve ANDURIL
B2/B3/B6 and M5 L6/L10 together. A Titchmarsh-style B3 (sigma = 1/2, K = 0, constant 2) would not
serve M5 (section 4).

---

## 1. The target, kernel-elaborated

`telperion/examples/dbn/lean/DBNM5Target.lean:85`:

```lean
def P15Thm13 : Prop :=
  ∀ t x y : ℝ, 0 < t → t ≤ 1 / 2 → 0 ≤ y → y ≤ 1 → 200 ≤ x →
    ‖DBN.H t ((x : ℂ) + (y : ℂ) * I) / Bt t x y - ft t x y‖ ≤ eA t x y + eB t x y + eC0 t x y
```

`DBN.H` is the island's H_t (`DBNDefs.lean:413`), which is P15 (4) verbatim. The vocabulary, in
P15 numbering (all in namespace `DBNM5`):

| P15 | object | Lean | file:line |
|---|---|---|---|
| (9) | alpha(s) = 1/(2s) + 1/(s-1) + (1/2) Log(s/(2 pi)) | `alpha` | `DBNM5Alpha.lean:61` |
| (42) | alpha' | `alphaDeriv` | `:64` |
| (7) | log M_0 (branch on C \ (-oo, 1]) | `logM0` | `:67` |
| (6) | M_0 = exp(log M_0) (and = (6) verbatim, `M0_eq_p15_eq6` `:189`) | `M0` | `:72` |
| (10) | log M_t = (t/4) alpha^2 + log M_0, M_t = exp(log M_t) | `logMt`, `Mt` | `:75, :78` |
| (17) | s_* | `sStar` | `:81` |
| (18) | kappa | `kappa` | `:85` |
| (16) | gamma | `gammaP` | `:89` |
| (11) | B_t(x+iy) = M_t((1+y-ix)/2) | `Bt` | `DBNM5Target.lean:37` |
| (19) | N = floor(sqrt(x/(4 pi) + t/16)) | `NP` | `:40` |
| (15) | b_n^t = exp((t/4) log^2 n) | `bnt` | `:43` |
| (14) | f_t | `ft` | `:46` |
| (44) | eps_{t,n}(sigma + iT) | `epsTN` | `:53` |
| (68) | T' = x/2 + pi t/8 | `Tprime` | `:58` |
| (59), (49) | eps~(sigma + iT), a = sqrt(T'/(2 pi)) | `epsTilde` | `:62` |
| (71)-(72), (74) | e_A, e_B, e_{C,0} | `eA`, `eB`, `eC0` | `:67, :73, :78` |
| Cor 6.4 | A_{t,N}, B_{t,N}, E_A, E_B | `AtN`, `BtN`, `EA`, `EB` | `:113-:134` |
| Cor 6.5 | E_{C,0}; the A + B statement | `EC0`, `P15Cor65` | `:137, :144` |

**Three transcription decisions.** Each was checked against the LaTeX source; section 5 has the
details.

1. **(14) carries an overline**: f_t = sum b_n^t n^{-s_*} + gamma sum n^y b_n^t n^{-(conj(s_*) + kappa)}
   (`debruijn.tex:229`). PDF text extraction drops the overline.
2. **(71) and (72) print `n^{Re s}`**, but the derivation needs `n^{Re s_*}`, and so do Prop 6.6 (iv)
   and (v). `eA` and `eB` use `Re s_*`.
3. **eps_{t,n}(s_+) and eps~(s_+) are evaluated at the reflection (1+y+ix)/2 of s_+ = (1+y-ix)/2.**
   Corollary 6.4 applies Props 6.1 and 6.3 there through M_t = M_t^* and alpha = alpha^*, and the
   (T - 3.33), (T - 6) denominators need T = x/2 > 0.

**Numeric validation of the transcription** (mpmath at 30 digits; untrusted, design evidence only;
script `scratchpad/m5/p15_target_check.py`):

- **Two independent H_t computations agree to 30 digits** at (t, z) = (0.2, 10+0.3i),
  (0.4, 20+0.8i) and (0.3, 40+0.5i). One is P15's heat-kernel formula (35) over mpmath's xi. The
  other is the island's definition, the Phi Fourier integral. This also cross-checks C2's
  normalization.
- **The inequality holds at 7 points of region (5)**: (t, x, y) = (0.2, 200, 0.2), (0.5, 200, 0),
  (0.1, 250, 1), (0.3, 300, 0.5), (0.2, 1000, 0.2), (0.4, 520.5, 0.9) and (0.05, 400, 0.1). The
  largest err/bound is 0.565, so the bound is not vacuous: e_A + e_B + e_{C,0} is 0.2-0.74 against
  |f_t| of 0.5-4.8.
- **Negative control.** Dropping the conjugate in (14) (the extraction's reading) breaks the
  inequality at 5 of the 7 points.

**The unnormalized form.** `P15Cor65` (`DBNM5Target.lean:144`) is Corollary 6.5,
|H_t - (A_{t,N} + B_{t,N})| <= E_A + E_B + E_{C,0}. That is what the analytic layers actually
produce. The division by B_t is **proved**: `P15Thm13_of_P15Cor65 : P15Cor65 → P15Thm13`
(`:236`). It is built from:

- `Bt_mul_ft` (`:168`), B_t f_t = A_{t,N} + B_{t,N};
- `EA_div_Bt`, `EB_div_Bt`, `EC0_div_Bt` (`:193, :222, :230`);
- the exponent identity `conj_sStar_add_kappa` (`:149`), conj(s_*) + kappa = s_- + (t/2) alpha(s_-) + y,
  which is where decisions 1 and 2 are forced.

---

## 2. Proof map of P15 sections 4-6

```
 (4) H_t = int e^{tu^2} Phi cos        C2: H_0 = xi/8 (DBNXi, proved)
        |                                   |
        +---- Gaussian identity (27) -------+--> (35) heat-kernel form  H_t(z) = int (1/8) xi((1+iz)/2 + sqrt(t) v) e^{-v^2}/sqrt(pi) dv   [L5]
                                                  |
 Riemann's integral (36): xi/8 = R_{0,0}(s) + R*_{0,0}(1-s)      [L6 = ANDURIL B2]
 residues at w = 1..N:  R_{0,0} = sum_{n<=N} r_{0,n} + R_{0,N}   [L6]
                                                  |
 growth of r_{0,n}, R_{0,N} along horizontal lines  ------------> (39) H_t = sum r_{t,n} + sum r*_{t,n} + R_{t,N} + R*_{t,N}   [L7]
                                                  |
 Gaussian contour shift (40)/(41) with alpha_n, beta_N = i pi/4  [L8]
                                                  |
    +---------------------------------------------+-------------------------------------------+
    |                                                                                         |
 Prop 6.1 (r_{t,n})  [L9]                                                          Prop 6.3 (R_{t,N})  [L11]
   needs: Lemma 5.1(v) Stirling [L4 ~ K5], (43) alpha' [done],                       needs: Prop 6.2 Arias de Reyna + (58) |C_0| <= 1/2 [L10 = B3+B6],
          Taylor of log M_0 [L1, done], Gaussian moment (47)                                Lemma 5.1(v) [L4], Taylor of log M_0 at iT', Gaussian
                                                                                            integrals (27) for eps, delta_1, delta_2; delta_3 tail
    +---------------------------------------------+-------------------------------------------+
                                                  |
                               Cor 6.4 (A+B-C) / Cor 6.5 (A+B)  = P15Cor65   [L12]
                                                  |   divide by B_t  [L13, PROVED: P15Thm13_of_P15Cor65]
                               Thm 1.3 (13) = P15Thm13
                                  + bounds (20) (21) (22)  [L2, PROVED]
                                  + bounds (23) (24) = Prop 6.6 (iv)-(vi)  [L3]
                                                  |
                               Cor 1.4 non-vanishing criterion  [L14, PROVED conditionally]  --> M6 certificates
```

---

## 3. Decomposition into kernel lemmas

The status column refers to this lane's modules. The line estimates are this memo's; section 7
gives their calibration. "Shared" means the same mathematical object appears in the ANDURIL
Riemann-Siegel plan.

| Layer | Content (P15 source) | Lines | Status | Shared |
|---|---|---|---|---|
| L0 | vocabulary: (6)-(19), (44), (49), (59), (68), (71)-(74), Cor 6.4/6.5 | ~320 | **done** | no |
| L1 | alpha-calculus: (7)-(9), (42), (43), reflection symmetry, corrected (76), exact Re alpha(s_+) | ~330 | **done** | Mathlib-only, portable |
| L2 | parameter bounds (20)-(22) = Prop 6.6 (i)-(iii) | ~360 | **done** | no |
| L3 | error-quantity bounds (23), (24) = Prop 6.6 (iv)-(vi), corrected (77) | 700-1,200 | open | no |
| L4 | effective complex Stirling, Lemma 5.1(v) (Boyd 1994) | 1,500-2,500 | open | yes: K5 |
| L5 | heat-kernel representation (35), and its xi form via C2 | 300-500 | open | no |
| L6 | Riemann's integral (36) and the residue expansion R_{0,0} = sum r_{0,n} + R_{0,N} | 3,000-6,000 | open | yes: **B2** |
| L7 | termwise evolution (39): subgaussian growth of r_{0,n} and R_{0,N} on horizontal lines | 400-800 | open | partly (Gamma envelopes) |
| L8 | Gaussian contour shift (40), (41) | 350-700 | open | no |
| L9 | Prop 6.1 (r_{t,n} estimate) | 700-1,200 | open | no |
| L10 | Prop 6.2 = Arias de Reyna (2011) Thms 3.1, 4.1, 4.2, and (58) = his Thm 6.1 (n = 0) | 4,000-8,000 | open | yes: **B3 + B6** |
| L11 | Prop 6.3 (R_{t,N} estimate) | 1,500-2,500 | open | no |
| L12 | Cor 6.4 / 6.5 assembly (= `P15Cor65`) | 300-500 | open | no |
| L13 | Cor 6.5 implies Thm 1.3 (normalization) | ~110 | **done** | no |
| L14 | Cor 1.4 (non-vanishing criterion, conditional) | ~15 | **done** | no |
| L15 | Lemma 5.1 (i)-(iv), (vi) (O-notation calculus, monotonicity) | 0-200 | open, likely inlined | no |

### Per-layer notes and statement sketches

**L1/L2 (done).** Anchors are in section 6. Two points matter for later layers:

- `hasDerivAt_logMt` gives (log M_t)' = alpha + (t/2) alpha alpha'. Together with
  `norm_alphaDeriv_le`, it supplies the second-order Taylor bounds that L9 and L11 need.
- The real-part method used for (20) (section 5, item 1) is the template for repairing (77) in L3.

**L3 (Prop 6.6 (iv)-(vi)).** These bound the defined e_A, e_B, e_{C,0} by the closed forms (23)
and (24). Three inputs:

- the corrected (77), for |alpha((1 +- y + ix)/2) - log n|^2;
- Taylor of log M_0 between iT' and (1+y+ix)/2;
- the eps~ bound (1.73/(T-6), 1.24 x 3^{+-y}/(a - 0.125)).

Numerically (23) and (24) hold as printed, but they are **asymptotically tight**. Over a grid in
region (5) up to x = 10^9, the largest ratio of the defined quantity to the printed bound is
0.99927 for (23) and 0.99999 for (24), with the ratio tending to 1 as x grows (script
`scratchpad/m5/p15_bounds_2324.py`). So a kernel proof must carry the leading terms exactly; the
slack is only in the O(1/x) terms. P15's own chain has two defects here (section 5, items 1 and 6).
In the eps step it inherits the (76) error and misses by about 1e-5 at t = 1/2, x = 200. The true
margin there is 0.002, so a real-part refinement repairs it.

**L4 (effective complex Stirling).** Target: for |Im z| >= 1 or Re z >= 1,
`Γ(z) = √(2π) exp((z − 1/2) log z − z + E)` with `‖E‖ ≤ 1/(12(‖z‖ − 0.33))`.

- **Where it is used.** P15 applies it at z = s/2 with Im s > 2 (Prop 6.1) and Im s = T' >= 100
  (Prop 6.3). Re s ranges over all of R there, since v runs over R, so the |Im z| >= 1 branch with
  Re z -> -oo is needed.
- **Mathlib at the pin has none of it.** Stirling is proved there only for factorials
  (`Mathlib/Analysis/SpecialFunctions/Stirling.lean`). There is no complex log-Gamma, and
  `Gamma/Digamma.lean` has the definition, special values and the recurrence only.
- **Route.** Euler-Maclaurin on sum log(z + k), or Binet's formula, with an explicit sawtooth
  remainder. P15's constant comes from Boyd's R_2 bound, including the 1/|1 - e^{2 pi i z}| factor
  on Re z <= 0.
- **ANDURIL assets.** These are on a different pin; section 4 lists them.

**L5 (heat-kernel representation).** Statement sketch:

```lean
theorem heat_kernel_rep {t : ℝ} (ht : 0 < t) (z : ℂ) :
    DBN.H t z = ∫ v : ℝ, DBN.H 0 (z - 2 * I * Real.sqrt t * v) * (Real.exp (-v ^ 2) / Real.sqrt π)
```

- **Proof.** Complete the square with Mathlib's `integral_cexp_quadratic` to get
  e^{tu^2} cos(zu) = int cos((z - 2i sqrt(t) v) u) e^{-v^2}/sqrt(pi) dv. Then apply Fubini. The
  majorant is e^{2 sqrt(t)|v| u} e^{-v^2} |Phi(u)| e^{|Im z| u}, which is integrable by
  `integrableOn_exp_mul_abs_Φ` (`DBNHeatApprox.lean:95`) after integrating v out.
- **The xi form** follows from C2 (`dbn_H0_eq_xi`) and the Gamma/zeta bridge
  `riemannXi_eq_completedRiemannZeta` (`DBNDefs.lean:468`).
- **Numerics.** The two sides agree to 30 digits at three points (section 1).

**L6 (Riemann's integral and residues; ANDURIL B2).** Define the oriented line integral through c
in direction e^{5 pi i/4}:

```lean
def rsLine (c : ℝ) (F : ℂ → ℂ) : ℂ := ∫ u : ℝ, F (c + u * ω) * ω       -- ω = exp(5πi/4)
def R00 (s : ℂ) : ℂ := 1/8 * (s*(s-1)/2) * π^(-s/2) * Γ(s/2) * rsLine (1/2) (fun w ↦ w^(-s) * exp(πi w²) / (exp(πi w) − exp(−πi w)))
theorem rs_integral (s : ℂ) (hs : ∀ n : ℤ, s ≠ n) :
    (1/8) * LiCriterion.riemannXi s = R00 s + conj (R00 (1 - conj s))
theorem rs_residues (s : ℂ) (N : ℕ) : R00 s = ∑ n ∈ Icc 1 N, r0n n s + R0N N s
```

- **Proof sketch.**
  - Riemann's derivation (Titchmarsh §2.10 / Edwards ch. 7). Establish it in a half-plane where
    the Dirichlet series converges, then extend by the identity theorem (Mathlib's `AnalyticOnNhd`
    API). This is one route; the ANDURIL memo prices B2 the same way.
  - The residue expansion moves the line across the simple poles at w = 1, ..., N. At w = n the
    residue of w^{-s} e^{i pi w^2}/(e^{pi i w} - e^{-pi i w}) is n^{-s}/(2 pi i), since
    e^{i pi n^2} = (-1)^n.
- **Missing from Mathlib at the pin.** There is no residue theorem and no Hankel contour. Rectangle
  Cauchy (`integral_boundary_rect_eq_zero_of_differentiableOn`) is present, and slanted strips
  rotate to rectangles.
- **ANDURIL's estimate** for this brick is 3,000-6,000 lines.
- **Build it for general non-integer s.** ANDURIL on-line needs sigma = 1/2, but B6 and M5 need all
  sigma.

**L7 (termwise evolution (39)).** For fixed s with Im s = x/2 != 0:

- |r_{0,n}(s + sqrt(t) v)| and |R_{0,N}(s + sqrt(t) v)| grow like exp(O(|v| log|v|));
- so each piece is integrable against e^{-v^2}, and (39) is linearity plus L5 and L6.

Growth of Gamma along horizontal lines:

- for Re w > 0, `norm_Gamma_le_Gamma_re` (ANDURIL `KernelGammaEnvelope.lean:45`);
- for Re w <= 0, the recurrence Γ(w) = Γ(w+m)/∏(w+k) with |w + k| >= Im w.

|R_{0,N}| is bounded by C^{|sigma|} from |w^{-s}| on the fixed line.

**L8 (Gaussian contour shift).** Generic statement:

```lean
theorem gaussian_shift {F : ℂ → ℂ} {c : ℂ} (hF : DifferentiableOn ℂ F {w | w.im between 0 and c.im})
    (hgrow : subgaussian growth of F on that strip) :
    ∫ v : ℝ, F v * exp (-v^2) = ∫ v : ℝ, F (v + c) * exp (-(v + c)^2)
```

- **Uses.**
  - (40): c = (sqrt(t)/2) alpha_n, since e^{-(v+c)^2} = e^{-v^2} e^{-sqrt(t) v alpha_n} e^{-t alpha_n^2/4}.
  - (41): c = (sqrt(t)/2)(i pi/4).
  - The side condition "Im s and Im(s + (t/2) alpha_n) have the same sign" (P15 (46),
    Im alpha_n >= -0.15) keeps the strip off the real axis.
- **Template.** Mathlib's proof of `integral_cexp_neg_mul_sq_add_real_mul_I`
  (`Gaussian/FourierTransform.lean:133`), through `verticalIntegral` and
  `tendsto_verticalIntegral`.

**L9 (Prop 6.1).** Statement sketch:

```lean
theorem prop61 {σ T t : ℝ} (hT : 10 < T) (ht : 0 < t) (ht' : t ≤ 1/2) (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : ℂ, ‖E‖ ≤ epsTN t n σ T ∧
      rtn t n (σ + T * I) = Mt t (σ + T * I) * bnt t n / (n : ℂ) ^ (σ + T * I + t/2 * alpha (σ + T * I)) * (1 + E)
```

Inputs:

- L8 with alpha_n;
- L4 applied to r_{0,n} = M_0 n^{-s} exp(O(1/(6(|s| - 0.66))));
- second-order Taylor of log M_0 from `hasDerivAt_logM0` and `norm_alphaDeriv_le`;
- the exact Gaussian moment (47), `integral_gaussian`;
- the algebraic identity M_0 exp((t/4) alpha_n^2 - s log n) = M_t b_n^t / n^{s + (t/2) alpha}. This
  identity is short given L1.

**L10 (Arias de Reyna; ANDURIL B3 + B6).** P15 Prop 6.2 cites Arias de Reyna, *High precision
computation of Riemann's zeta function by the Riemann-Siegel formula, I*, Math. Comp. 80 (2011)
995-1009: Thms 3.1, 4.1 and 4.2 with (3.2) and (5.2), and Thm 6.1 (n = 0) for (58)
|C_0(p)| <= 1/2 on [-1, 1]. It needs three pieces:

- the expansion identity, with C_0(p) explicit (53) and C_k, RS_K defined by Arias de Reyna's
  auxiliary functions;
- the bounds (54)-(57) in both regimes, sigma > 0 and sigma <= 0;
- (58).

Prop 6.3 uses **K = 1 for u >= 0 and K up to about T'/pi for u < 0**. The Gaussian weight
e^{-(u-sigma)^2/t} does not make the u < 0 range negligible. P15's delta_2 decays at the same rate
1/a as delta_1 (it is about a tenth of it), so that range cannot be dropped without changing (59).
General k in (55) and (57) is needed.

(58) is tight: |C_0(+-1)| = 1/2 exactly (P15 Figure 10). Clearing the denominator 2 cos(pi p) gives
the equivalent 6c^2 - 4c^4 <= 2 sqrt(2) c sin(pi(p^2/2 + 3/8)) with c = cos(pi p/2). Equality holds
there at p = +-1 (c = 0), and also at the removable singularity p = +-1/2, where both sides agree to
second order. So a kernel proof needs care at both. This lane checked that reduction by hand and did
not formalize it.

Arias de Reyna Part I was not read this session. The `scratchpad/ar2201.txt` copy is Part II
(arXiv:2201.00342), the floating-point companion.

Estimate 4,000-8,000 lines. It is the long pole.

**L11 (Prop 6.3).** It uses L8 with beta_N = i pi/4, L10, L4, Taylor of log M_0 around iT' with
alpha(iT') = log a + i pi/4 + O(3/(2T')), and:

- closed Gaussian integrals for eps, delta_1 and delta_2 ((27) with linear terms);
- the delta_3 tail by Fubini-Tonelli;
- the numeric claim (1.1)^k Gamma(k/2) e^{-(k-4)^2 + (k-4) log 2} <= 10^{-30} for k >= 14.

This is about six pages of explicit constant-chasing in P15, hence the 1,500-2,500 estimate.

**L12 (Cor 6.4 / 6.5).** Inputs: (39), Props 6.1 and 6.3 at s_- and at conj(s_+), the reflection
lemmas `logMt_conj`, `logM0_conj` and `alpha_conj` (done), |U| = 1, and (58). The output is
`P15Cor65`, and L13 then gives `P15Thm13`.

---

## 4. Shared infrastructure with the ANDURIL Riemann-Siegel route

| M5 layer | ANDURIL item (`ANDURIL_ARB_DISCHARGE_2026-09-23.md` §4.3) | Existing assets (`zeta_reflection`, Lean v4.32.0) | Note |
|---|---|---|---|
| L6 Riemann's integral + residues | **B2** RS representation (3,000-6,000) | none ("no part of B2 or B3 has been attempted", memo §6) | the ANDURIL memo already recommends general sigma "from the start"; M5 needs exactly that |
| L10 Arias de Reyna expansion + bounds | **B3** saddle bound (2,000-5,000), **B6** general-sigma (+50-100%) | none | B3 may take either the Titchmarsh 1935 template (sigma = 1/2, K = 0, constant 2) or Arias de Reyna Part I. **Only the Arias de Reyna route serves M5**, and it also covers B6 |
| L4 complex Stirling | **K5** (largely superseded for Im log Gamma by `lam_bracket`) | `StirlingBinet.lean` (K = 1 Binet enclosure of logDeriv Gamma_R for Re z >= 1/4 via shifts; anchor discharged for Re >= 2 per the ANDURIL memo §1.1); `StirlingK4.lean` (`binetTail_height_norm_le`); `RSTheta.lean` `lam_bracket` (Im log Gamma(x+iy) bracket, x > 0); `EMZetaHigh.lean` (`abs_sawBernoulli_even_le`/`_odd_le`, `em_tail_step`: the sawtooth-Bernoulli Euler-Maclaurin kit) | M5 needs the modulus as well as the phase, with an explicit constant, for Re z -> -oo at Im z >= 1. ANDURIL B6 (FE-reflected, the chi factor) needs the same |Gamma| ratio |
| L7 Gamma growth | (none named) | `KernelGammaEnvelope.lean:45` `norm_Gamma_le_Gamma_re` (Re s > 0); `norm_Gamma_quarter_lower` `:116` (at 1/4 + iy only) | method reuse. The pin differs, and the file imports corpus modules |
| M6 evaluator (after M5) | **B4** Nat-only fixed-point main-sum evaluator (1,000-2,000; about 1,600 reusable from ArbEcon) | `Probes/ArbEconomics_{Eval,Sound}` | f_t is a Dirichlet sum with complex exponents n^{-s_*} and weights b_n^t = exp((t/4) log^2 n). The kernels are log n tables, cos/sin reduction and exp, as in B4 |
| (not needed) | B0 theta | `RSTheta.lean` | U appears in (13) only through \|U\| = 1, inside e_{C,0}. Theta is needed only for the refined A + B - C form (69) |

**Toolchain seam.** `zeta_reflection` is on Lean v4.32.0 and `dbn` is on v4.34.0-rc1 with Mathlib
`de5ce8a9`. A lake package cannot import across pins. There are three options, and the choice is
for the lead:

- **(A)** Build the shared core (L4, L6, L10) as Mathlib-only source that compiles on both pins,
  with a CI job that compiles it on each. `DBNM5Alpha` is already Mathlib-only in this sense.
- **(B)** Bump `zeta_reflection` to the dbn pin. That is a one-time port of 106 modules at unknown
  cost.
- **(C)** Build on the dbn pin only, and port to ANDURIL later.

(A) is recommended because B2/B3/B6 do not exist yet, so there is nothing to port. The existing
ANDURIL Stirling assets are not Mathlib-only: they import corpus modules (`DiffractionCore`,
`ZeroFreeBridge`). L4 would reuse their methods rather than their files.

---

## 5. Findings in P15 (errata and verification)

None of these changes P15's headline results. Each changes what a kernel proof must do. Every
proof-affecting finding comes with a kernel artifact or a reproducible script.

1. **(76) is false as printed, and P15's proof of (20) does not reach its constant.**
   - **The error.** P15 p. 32 writes alpha(ix/2) = (1/2) log(x/(4 pi)) + i pi/4 + O(2/x), counting
     1/(s-1) at s = ix/2 as O(1/x). Its true size is about 2/x. The exact remainder is
     1/(ix) + 1/(ix/2 - 1), whose imaginary part is -(3x^2 + 4)/(x(x^2 + 4)), about -3/x
     (sympy-verified). mpmath gives |remainder| * x = 2.99987 at x = 200, tending to 3.
   - **Kernel negative control.** `DBNM5.p15_eq76_fails_at_200` (`DBNM5Alpha.lean:346`) proves that
     (76)'s bound (2 + sigma)/(x - 6) fails at sigma = 0, x = 200. That point is in range: y = 1
     gives sigma = (1-y)/2 = 0.
   - **Corrected (76)**, proved: `norm_alpha_sub_main_le` (`:365`) gives (3 + sigma)/(x - 6).
   - **Effect on (20).** With 3 in place of 2, P15's chain for Prop 6.6 (i) gives the constant
     0.0235, not 0.02. The claim (20) is nevertheless true, with room: over the tested grid,
     [log|gamma| + (y/2) log(x/(4 pi))]/y <= 1.9e-5.
   - **The kernel proof** `norm_gammaP_le` (`:741`) uses only the real part of (log M_t)' on the
     segment. There the 1/(2s) and 1/(s-1) terms contribute O(1/x^2), and the proof reaches 0.02 via
     `gamma_numeric` (`:652`), whose bound is about 0.013 at x = 200.
2. **(21) (Thm 1.3) and Prop 6.6 (ii) are different inequalities, and P15 proves only the second.**
   - They differ by 4y(1-3y)/x^2 inside the positive part, so neither implies the other.
   - P15's proof of (ii) (`debruijn.tex:1032`) opens "it suffices by \eqref{res-bound} [= (21)] to
     show Re alpha(s_+) >= (1/2) log(x/(4 pi)) - (1-3y)_+/x^2 - 4y(1+y)/x^4". That target gives only
     a weaker bound than (21) when y > 1/3.
   - The body then computes Re alpha(s_+) exactly and ends at the 8y(1-y) form (ii), which does not
     imply (21). So (21), the form in the theorem statement, is not established by the written
     proof.
   - Both are proved here: `re_sStar_ge` (`:530`) and `re_sStar_ge_prop66` (`:546`). (21) goes
     through the identity (x^2(1-3y) + 4y(1+y)) A B - N_1 x^4 = x^2(1-y)^2 N_1
     + 4y(1+y)^3 x^2 + 4y(1+y)(1-y^2)^2 in `rat_part_ge_21` (`:439`).
   - (21) needs only y >= 0.
3. **(14) needs the overline on s_*.** It is present in the source (`debruijn.tex:229`,
   `n^{\overline{s_*} + \kappa}`) and in P15 (78). It is invisible in PDF text extraction. Without
   it the second sum has the wrong phase. The kernel identity `conj_sStar_add_kappa`
   (`DBNM5Target.lean:149`) shows which reading makes Cor 6.5 imply Thm 1.3, and the numeric
   negative control (section 1) shows that the other reading is false.
4. **(71) and (72) print `n^{Re s}` for `n^{Re s_*}`** (`debruijn.tex:970-971`). This is textual.
   `EA_div_Bt` and `EB_div_Bt` (`DBNM5Target.lean:193, :222`) fix the intended reading.
5. **(24)'s constant 10.44 should be 10.50 by P15's own derivation.** The derivation is Prop 6.6
   (vi) plus 1 + u <= e^u and 1/(x - 8.52) <= 1/(x - 12), giving 3.58 + 6.92 = 10.50. Numerically,
   (24) holds as printed on the tested grid with ratio below 1, tending to 1 as x -> oo. So the
   printed constant may well be true, but P15 does not derive it. L3 should prove the 10.50 form,
   or the printed one with a sharper step.
6. **The eps step of Prop 6.6 (iv), (v) inherits (76).** P15 derives
   (t^2/8)|alpha_n|^2 + t/4 + 1/6 <= (t^2/32) log^2(x/(4 pi n^2)) + 0.313 from the constant 0.667.
   With the corrected (77) that constant becomes 0.683, and the chain gives 0.31301 at t = 1/2,
   x = 200, just over 0.313. The inequality itself holds with margin 0.002 on the tested grid
   (`scratchpad/m5/p15_checks2.py`), so a real-part refinement suffices. By contrast, Prop 6.6 (vi)
   survives the correction, because P15 bounds (t/4)(3|...|) by 3|...|, a factor of 8 of slack.

---

## 6. What this lane built (anchors)

**`DBNM5Alpha.lean`** (Mathlib-only, 769 lines, namespace `DBNM5`):

- `M0_eq_p15_eq6` `:189`: M_0 is P15 (6) verbatim, for s != 0, 1.
- `hasDerivAt_alpha` `:118`, `hasDerivAt_logM0` `:147`, `hasDerivAt_logMt` `:177`: (42), (8), and
  (log M_t)' on C \ (-oo, 1].
- `norm_alphaDeriv_le` `:210`: (43).
- `alpha_conj` `:249`, `logM0_conj` `:263`, `logMt_conj` `:275`: reflection symmetry off the real
  axis.
- `norm_alpha_sub_le_of_im_eq` `:290`: alpha is 1/(x-6)-Lipschitz on Im w = x/2.
- **`norm_kappa_le` `:305`**: (22), for x > 6 and t, y >= 0.
- `alpha_I_sub_main` `:325`; **`p15_eq76_fails_at_200` `:346`** (negative control);
  **`norm_alpha_sub_main_le` `:365`** (corrected (76)).
- `re_alpha_sPlus` `:410` (exact Re alpha(s_+)), `rat_part_ge_21` `:439`, `rat_part_ge_66` `:482`.
- **`re_sStar_ge` `:530`**: (21). **`re_sStar_ge_prop66` `:546`**: Prop 6.6 (ii).
- `re_alpha_ge_of_im` `:571`, `norm_alpha_le_of_im` `:607`, `gamma_numeric` `:652`,
  `re_logMtDeriv_ge` `:683`, `hasDerivAt_gLine` `:712`, `norm_gammaP_eq` `:728`.
- **`norm_gammaP_le` `:741`**: (20) on region (5).

**`DBNM5Target.lean`** (imports `DBNDefs` and `DBNM5Alpha`; 251 lines):

- the definitions of section 1;
- `Bt_ne_zero` `:90`;
- `H_ne_zero_of_P15Thm13` `:95` (Cor 1.4, conditional);
- `conj_sStar_add_kappa` `:149`, `Bt_mul_ft` `:168`, `EA_div_Bt` `:193`, `EB_div_Bt` `:222`,
  `EC0_div_Bt` `:230`;
- **`P15Thm13_of_P15Cor65` `:236`** (L13).

**Verification (re-run in this worktree, 2026-09-23).**

- **Build.** `leanlock.sh lake build` in `examples/dbn/lean` reports "Build completed successfully
  (8763 jobs)". Both modules are registered as `lean_lib`s and in `defaultTargets`.
- **Axiom guard.** `lake env lean AxiomGuardDBN.lean` prints 368 axiom lines (325 before this lane
  plus 43 new). Every one is exactly `[propext, Classical.choice, Quot.sound]`. There is no
  `sorryAx` and no "does not depend".
- **CI scans.** The `dbn-compiles` sorry scan (`grep -rnwE "sorry|admit"`, which does **not** skip
  backticked words) is clean over the island. The CI 3-axiom subset check is clean.
- **Forbidden constructs.** No `native_decide`, `axiom`, `opaque`, `implemented_by`,
  `ofReduceBool` or `extern` in either file.
- **Names.** All new names live in namespace `DBNM5`, so there are no clashes with `DBN.*` or with
  other lanes.

---

## 7. Estimates, calibration, critical path

**Calibration.** Brick 1 is a measurement. It covered P15 (6)-(10), (42), (43) and the proofs of
Prop 6.6 (i)-(iii), about 1.8 pages of P15, in about 700 lines, which is roughly 350-420 lines per
page. That density includes derivative plumbing that P15 treats as obvious. Two further anchors:

- C3's design memo estimated 4,500 lines and the closure took 3,695.
- C2's kernel-calculus module overran 250-400 to 684.

The estimates above apply 350-420 lines per page to P15's §6 (15 pages). The cited results that P15
does not prove are priced separately: Arias de Reyna Part I (L10), Boyd's Stirling (L4) and
Riemann's integral (L6).

| | lines |
|---|---|
| done (L0, L1, L2, L13, L14) | 1,020 |
| remaining, M5-only (L3, L5, L7, L8, L9, L11, L12) | 4,250-7,400 |
| remaining, shared with ANDURIL (L4, L6, L10) | 8,500-16,500 |
| **M5 total** | **about 13.8k-24.9k** |

This is above the synthesis's unanchored 10k-20k. The differences are that Prop 6.3 is dense
(about 6 pages), and that L10 must cover the general-K, sigma <= 0 regime.

**Critical path with parallel staffing:**

```
L6 (Riemann integral, general s) --> L10 (Arias de Reyna, general sigma, K; incl. (58)) --> L11 --> L12 --> [L13 done] --> P15Thm13
L4 (Stirling) ---------------------------------------------------------------------------^  (also feeds L9)
L5, L7, L8, L9, L3: parallel, each 1-3 agent-weeks
```

The long pole is L6 then L10, which is the same pole as ANDURIL's (their critical-path estimate is
8-16 agent-weeks for B2 then B3). If ANDURIL builds B2/B3/B6 in the general form recommended in
section 4, M5's own remaining work is 4.3k-7.4k lines, about 6-10 agent-weeks.

**Pivots if L10 stalls.** A weaker-constant variant of Thm 1.3 could be registered separately.
Candidates are Titchmarsh-type RS bounds with larger constants, or a crude sigma <= 0 bound
(Gamma-envelope based) that costs the 1/a decay of delta_2. M6 needs only *some* valid effective
approximation. Weaker constants cost certification margin, not correctness.

---

## 8. Proposed registry ops (NOT executed; `telperion/missions/` untouched)

The registry statements use textual copies of island vocabulary (`Statements/RHDefs.lean:97-116`
copies `DBN.H`). Any node below needs the `DBNM5` vocabulary copied there verbatim first (op R0).

- **R0** (prerequisite; statement-file edit): copy the definitions of `DBNM5Alpha.lean:61-89` and
  `DBNM5Target.lean:37-87` into `RHDefs.lean` under a `DBNM5` namespace. This is a docs/registry
  change, and it needs the lead because it widens the trusted vocabulary copy.
- **R1** `mission add rh RH_dbn_p15_param_bounds`:
  - kind "lemma"; depends_on [].
  - Statement: the conjunction of `norm_gammaP_le`, `re_sStar_ge` and `norm_kappa_le` as stated
    (region (5) hypotheses verbatim).
  - Artifact `examples/dbn/lean/DBNM5Alpha.lean`, via "direct", closure_clean true.
  - Candidate for immediate grant after two blind audits. Low value alone; it records progress.
- **R2** `mission add rh RH_dbn_effective_Ht_approx`:
  - kind "milestone"; depends_on ["RH_dbn_H0_eq_xi", "RH_dbn_p15_param_bounds"].
  - Statement: `DBNM5.P15Thm13` verbatim (`DBNM5Target.lean:85`). Status draft.
  - Readback: "reduced to P15Cor65 by the proved `P15Thm13_of_P15Cor65`; P15 errata in the M5 design
    memo §5."
- **R3** `mission add rh RH_dbn_p15_cor65`: kind "lemma"; statement `DBNM5.P15Cor65` verbatim;
  draft. Edge R2 depends on R3, and the reduction artifact is `DBNM5Target.lean:236`.
- **R4** Shared analytic nodes. Avoid duplicating ANDURIL's proposed `AND_rs_representation` and
  `AND_rs_remainder_c0` (ANDURIL memo §5 step 2).
  - Recommended: widen `AND_rs_representation` to general non-integer s, and `AND_rs_remainder_c0`
    to Arias de Reyna's general (sigma, K) form. Then add rh-side dependency links to them.
  - If cross-mission edges are unsupported, register rh twins with byte-identical statements and a
    readback cross-reference.
  - This is a design decision for the lead and the ANDURIL owner.
- **R5** Drafts for the M5-only layers, each with a by-design placeholder:
  - `RH_dbn_heat_kernel_rep` (L5);
  - `RH_dbn_gaussian_shift` (L8);
  - `RH_dbn_p15_prop61` (L9);
  - `RH_dbn_p15_prop63` (L11);
  - `RH_dbn_p15_error_bounds` (L3, bounds (23)/(24), with the 10.50 form of (24) unless a sharper
    proof of 10.44 is found).
- **R6** attempts.jsonl rows for R1 (verdict Proved, session m5-2026-09-23) and for R2 (verdict
  Reduced, to R3).

---

## 9. Beyond M5: what M6 still needs

M5 alone certifies nothing. For a hypothesis-free Lambda <= c0 < 1/2 (M6) the program also needs:

- **M1**, parametric de Bruijn. Thm 1.2 closes with Thm 3.2.
- **M4**, the Prop 3.3 zero-dynamics criterion.
- **A certified evaluator** for f_t, e_A, e_B and e_{C,0} at the barrier and canopy mesh points
  (ANDURIL B4-type).
- **A separate small-x evaluator.** Thm 1.3 covers only x >= 200. At the hypothesis-free
  X = 55/8, the canopy of Thm 1.2 (ii) starts at x = X + sqrt(1 - y0^2), about 7.8, so
  7.8 <= x < 200 needs another tool. Candidates are rigorous quadrature of the heat-kernel form (35)
  (P15 Remark 4.1 calls it "fast and accurate" for moderate x) or a direct Phi-integral evaluator.
- **M0**, to learn whether any c0 < 1/2 is certifiable at that X at all (synthesis §7.3).

---

## 10. What was not checked

- **Arias de Reyna 2011 (Part I) was not read.** L10's content and its estimate rest on P15's
  restatement (Prop 6.2, (54)-(58)) and on the ANDURIL memo. Boyd 1994 was not read either; L4
  rests on P15 Lemma 5.1(v)'s proof sketch.
- **All numerics are untrusted design evidence.** They cover finite grids only (section 5 lists
  them); "holds on the tested grid" is not a proof. That includes the tightness ratios for (23) and
  (24) and the 0.002 margin in item 6.
- **Line estimates are projections**, calibrated on one brick (section 7). No part of L3-L12 was
  attempted.
- **(58) |C_0(p)| <= 1/2** was reduced by hand, not formalized, and its tangency at p = +-1/2 was
  checked only symbolically.
- **No registry op was run**, and no `statement_matches` pre-flight was run for the proposed
  statements. The R0 vocabulary copy does not exist.
- **Not re-checked:** the synthesis's figures, the ANDURIL memo's figures and P15's numerical
  sections 7-8.

conjecture1_proved = False.
