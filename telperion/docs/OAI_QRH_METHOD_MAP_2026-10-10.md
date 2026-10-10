# OpenAI's 7/8 half-plane: a map of the method, and where the slack is

Date: 2026-10-10. Session e9, first pass. Sources: OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free
Half-Plane Re(s) > 7/8*, OAI preprint of 30 September 2026 (199 pp., "paper1"); OpenAI, *The Quasi-Riemann
Hypothesis*, 5 October 2026 (49 pp., "paper2", the simplified 11/12 version); the Lean sources of
openai/math at adc7f124 (`lean/OAI/NumberTheory/DirichletL/`, 2,926 files, 486k lines), read in the
materialized workspace of `qrh-debruijn-newman`. This is a reading, not a verification: the theorem is
verified (Comparator, two kernels); the account of *why* it works below is my reconstruction from the
paper's outline sections and the Lean assembly files, and it should be checked against the body of the
paper before anything is built on it. conjecture1_proved = False.

The three questions this map was commissioned to answer (project_rh_next_direction, 2026-10-10):

## 1. Where does 7/8 come from?

**The object.** Not a single zero-free region but a supremum over a whole family. For F = Q(sqrt(-3)),

    beta_* = sup( {1/2} U { Re rho : L_F(rho, eta) = 0, 1/2 <= Re rho <= 1, eta a primitive finite-order
                            Hecke character of F } )

(paper1 eq. 2.1; Lean `SevenEighths.HeckeZeroSupremum.beta`, Hecke/ZeroSupremum.lean, with the 1/2
sentinel). Dirichlet L-functions, and zeta, come at the end by quadratic base change
L_F(s, chi o N) = L(s, chi) L(s, chi chi_{-3}) (paper1 §11.2, eq. 11.2). The family is essential even for
zeta alone, because the Poisson step introduces Hecke twists of the target.

**The engine (Prop. 2.1, "continuation from a common signal").** Fix a boundary sigma_0 in (1/2, 1) and
suppose Delta_0 = beta_* - sigma_0 > 0. Let C(s) = s + c. If for every primitive target eta there are a
finite excluded set S, a holomorphic H_eta on Re s > sigma_0 with |H_eta - 1| <= 1/2, and a "probe"
J_eta(Z) with

    |J_eta(Z)|            <<  Z^{C(sigma_0) + omega}     (direct bound),        0 < omega < Delta_0,
    |J_eta(Z) - f_eta(Z)| <<  Z^{C(beta_*) - sigma}      (power-saving comparison), sigma > 0,

where f_eta is the Mellin integral (2.3) of Z^{C(s)} e^{(s-5/6)^2} H_eta(s) / L_F^S(s, eta) on Re s = 2, and
omega, sigma do NOT depend on eta, then this contradicts beta_* > sigma_0. Proof: Mellin-invert, obtain a
holomorphic continuation of 1/L_F^S(s, eta) to Re s > beta_* - min(Delta_0 - omega, sigma), which some
target's rightmost zero forbids. The principle is stated for variable sigma_0; it is applied twice.

**Stage I (Part I, Thm 3.1): sigma_0 = 11/12, C_I(s) = s - 2/3.** The "balanced" probe: both averaging
scales Z^{1/2}; the completed cubic-theta sum over indices c n^3 (c, n = 1 mod 3), twisted by the sextic
residue symbols chi_n(u) = (u/n)_6 and the target. Reflection side: Kubota/Patterson cubic theta
transformation + quadratic large sieve (Goldmakher-Louvel) + planar additive large sieve. Poisson side: rows
u a^6, principal row u = 1 carries the Mellin signal; nonprincipal rows controlled by a zero detector
(Section 8) and the sextic large sieve (Lemma 9.1). The 1/12 is the cost of sextic twists: in paper2's
simplified version (eqs. 2.4-2.5, 3.2) one reproduces A_1(D) from the rows u = p^6 (chi_n(p^6) = 1), so only
Y = H^{1/6} of the H rows are usable and |A_1|^2 << D^{1+eps} H^{5/6} + D^2 H^{-1/3}, i.e.
A_1(D) << D^{11/12 + eps}, i.e. zero-free Re s > 11/12. Heuristically, k-th power twists would give
1 - 1/(2k): k = 6 is 11/12. (k = 2 would be 3/4 and k = 1 is RH; that is a statement about the cost of
this trick, not a route: the whole point of the sextic/cubic choice is that cubic Gauss sums are theta
coefficients, which is what makes the reflection side tractable.)

**Stage II (Part II, §§12-20): sigma_0 = 7/8, C_II(s) = s - 11/16, C(7/8) = 3/16.** Starts from
beta_* <= 11/12 (Stage I), so with Delta := beta_* - 7/8 one has 0 < Delta <= 1/24 and the bin ceiling
kappa = 3/4 + 2 Delta <= 5/6 (eq. 12.1-12.2). Fixed geometry (eq. 12.4):

    b = 1/8,  h = 13/16,  ell = 1/6,  l_x = 17/48,  l_y = 23/48,  X = Z^{l_x}, Y = Z^{l_y},  h = 1 - l_x + ell.

New ingredient: *prime compensation*. K prime slots P_i = Z^{ell_i}, sum ell_i = ell = 1/6, each with a
smooth annular weight W_i; the modified probe (12.5) subtracts, at each slot prime, a rescaled term from a
marked term, designed to cancel the scalar prime contribution on the high side. Two new moment estimates:
the inverse moment with prime factors (§17, Lemma 17.1) and the fourth moment with short prime factors
(§18, Lemma 18.1), both by finite Poisson-transform inductions; §19 turns them into row counts with
"prime amplitudes".

**Where the number 7/8 is pinned.** In §20, every nonprincipal row class gets a scale exponent E relative to
C(7/8), and the proof needs E(d) + eps_real(d) <= Delta - eps_hi uniformly (eq. 20.12). The key exponent
(eq. 20.4) for a row bin (d, a), delta = 2a - 1, main-slot mean q in [0, delta/2], ideal row exponent R:

    E(d) = a - 7/8 + h(17/50 - 1/6) - a l_y - (1-a) ell - (delta/2 - q) ell + d (R + delta/2 - 17/50)
         = C_0 + (2/3) delta + q/6 - h(1 - R) + (d - h)(R + delta/2 - 17/50),     C_0 = -1/48.

The certificates that make it negative at this geometry:
  - floor bin a = 51/100: E(h) <= C_0 + (3/4) delta_0 = -7/1200                              (20.5)
  - live endpoint delta = alpha = 5/6, no slots: E(h) <= -1/48 - delta/16                     (20.7)
  - 1/50 < delta < 5/6 with the balanced cutoff t of (20.8): Lemma 20.2, -E_* >= 49/440640,
    proved by the explicit completed-square identity (20.9)
        10368 v J (-E_*) = (3+5y){(4 v delta - 79)^2 + 49} + 4y{...}, v = 51 + 41y, y = 1/2 - x
    -- formalized verbatim as `SevenEighths.Endpoint.endpoint_identity` / `balanced_endpoint_margin`
       (DirichletL/Endpoint.lean, Mathlib-light, exact polynomial algebra: a Telperion-shaped certificate)
  - d_min <= d <= 1/2, R = 76/75 - (2/3) delta: E(d) <= -49/14400                              (20.11)
  - small rows: -63/800; large rows: z_infty large; principal contour margins m_w = 23/960, m_z = 13/9600.
Then m_lo = Delta, m_hi = (1 - h/4) Delta = 51 Delta/64, m_high = min(m_hi, 63/800), and all adjustable
losses (detector width e < 1e-3, amplitude width, slot mesh, capacity decrement, external orders, height
tau) are chosen in a fixed order (Prop. 20.3) to cost less than m_high/8 each. The Lean parameter structure
`Parameters.HighData` (ParametersHighData.lean) IS this order of choices: its fields `central_budget`
(... <= 49/440640), `floor_budget` (... <= 7/1200), `geometric_budget` (... <= 63/800), `principal_budget`
(... <= 17/48000), `count_budget`, `window_budget`, with t <= 1e-8 and (13/16) + 3t <= 7/8.

So: 7/8 is the boundary sigma_0 at which this particular geometry (h = 13/16, ell = 1/6, l_x = 17/48,
l_y = 23/48, b = 1/8, Mellin shift 11/16) makes the whole exponent system (20.4)-(20.11) negative with
small positive margins (1/48 at the top, 49/440640 at the endpoint). The geometry constants are tied to
7/8 through C(7/8) = 3/16 and h = 1 - l_x + ell. The margins are small: the geometry is near the edge of
what it can do at 7/8, which is what one expects of an optimized choice. Whether a *different* geometry
reaches a lower sigma_0 is a separate question (section 4).

## 2. Is the argument parametric?

**On paper: the engine yes, the stage no.** Prop. 2.1 is stated and proved for every sigma_0 in (1/2, 1)
and every affine C. Each stage is a fixed instance: a geometry, a Mellin shift, and a certificate that the
exponent system closes. Stage II consumes Stage I's output only through the bin ceiling kappa <= 5/6
(Delta <= 1/24). Nothing in the paper iterates further, and nothing in it says a Stage III at some
sigma_0' < 7/8 is impossible; it also gives no sign that the authors tried. The paper's own description:
"positive exponent margins chosen independently of the target character" -- the independence from eta is
the hard requirement, and the margins are what the geometry buys.

**In Lean: 7/8 is a literal, but the literals are concentrated.**
  - `Supremum.continuationMargin beta omega sigma := min (beta - 7/8 - omega) sigma` and
    `seven_eighths_of_uniform_margin_with_sentinel` (Supremum.lean) hard-code 7/8; the proofs are elementary
    sSup reasoning and generalize to any boundary in a few lines.
  - `HeckeZeroSupremum.beta_le_seven_eighths_of_uniform_margin` (Hecke/ZeroSupremum.lean): the formal Prop.
    2.1 conclusion, hypothesis = "if 7/8 < beta then there are uniform omega, sigma with every zero's real
    part <= beta - continuationMargin". Same remark.
  - The Stage II geometry appears as literals 13/16, 17/48, 23/48, 11/16, 17/50 in 56 files, mostly under
    PrimeRows/ and Detector/, plus `(7/8:ℝ)` in 57 places and 13/16 in the budgets.
  - `Endpoint.lean` carries the geometry inside `balancedExponent delta y := -(1/48) + (2/3) delta +
    delta (1/2 - y)/6 - (13/16)(1 - balancedRowCount delta y)` and the balance data
    (`denominator`, `primeWeight`, `balanceDenominator`, `balancedCutoff`) from Prop. 19.2.
  - The final assembly (`Detector/FinalAssemblyUnconditional.lean`) proves `DetectorCertifiedBands` by
    `terminal_certificate` with the numeric choices (1/4, 9/4, 33/50, 2, ...) and then
    `zeta_of_certified`, `dirichlet_of_certified` at 7/8.
So a parametric formal version is not a refactor of one file; it is re-threading a rational-geometry
vector through ~60 files whose statements carry the constants. Mechanical if only the constants change;
not mechanical if the structural estimates (Props. 8.3, 19.2, Lemmas 17.1, 18.1) have validity ranges that
move with sigma_0.

## 3. Where does the arithmetic enter (the Davenport-Heilbronn control)?

At the first step, and then everywhere. The direct bound / Mellin comparison compares a character sum with
an integral of 1/L_F^S(s, eta): that reciprocal is the Dirichlet series of mu(n) eta(n), i.e. the Euler
product. The Davenport-Heilbronn function has a functional equation and a Dirichlet series but no Euler
product, so Step 1 has no Mobius-twisted sum to bound and the method does not start. Downstream the
arithmetic is even more specific: the family is twisted by sextic residue symbols over Z[omega]; Poisson
summation produces sextic Gauss sums that the Gauss-Jacobi identities turn into cubic Gauss sums; those are
the Fourier coefficients of Kubota's cubic theta function (Patterson's formula 2.10, Dunn-Radziwill's cusp
expansions), whose automorphy is the reflection; the quadratic character chi_h^3 that survives is what the
quadratic large sieve needs; prime compensation uses Landau's prime ideal theorem in ray classes. Every one
of these is an arithmetic structure the Davenport-Heilbronn counterfeit lacks. The negative control fails
at step one, as it should for a method with content.

## 4. What this means for us

**The route to a Lambda record is a Stage III, and it is a finite, concrete question.** Through the verified
converter Lambda <= 2 (theta - 1/2)^2, a half-plane at theta < 0.8317 beats Polymath15 (0.22) and
theta < 0.8162 beats Platt-Trudgian (0.2); 13/16 = 0.8125 would give Lambda <= 25/128 = 0.1953, a new
record. A Stage III would (a) assume beta_* > sigma_0' for some sigma_0' < 7/8, (b) take beta_* <= 7/8 as
input (Delta' <= 7/8 - sigma_0', hence a bin ceiling kappa' = 3/4 + 2 Delta' < 5/6, which REDUCES the
retained row range and helps every count), (c) choose a new geometry and Mellin shift, (d) re-certify the
exponent system. Steps (c)-(d) are an optimization over a handful of rationals subject to polynomial
inequalities: exactly what Telperion's certificate finders (SDP/Positivstellensatz, exact rational SOS) and
AXLE-style negative controls were built for, and `Endpoint.lean` shows the output shape the formal side
wants. What I cannot yet state is the full constraint set: (20.4)-(20.11) are the tip; the row counts in
Prop. 19.2 (D_x, P_x, J, t, R_*, R_short, L), the detector hypotheses of Lemmas 8.1-8.2, the moment
estimates' admissible ranges (§§17-18) and the small/large-row bounds (§20.3) all carry the geometry.

**Concrete next task (bounded):** extract the Stage II exponent system as a symbolic model. Inputs:
paper1 §12 (12.1-12.5), §19.2 (Prop. 19.2 row counts, which `Endpoint.lean` already encodes as rational
functions), §20 (20.4-20.12), and the Lean `HighData` budgets. Output: a sympy/Python model
E(d, a, q, R; sigma_0, h, ell, l_x, l_y, b, c) with the constraint list, that (i) reproduces the paper's
certificates at (7/8, 13/16, 1/6, 17/48, 23/48, 1/8, 11/16) including the 49/440640 margin, then (ii) is
searched for the minimal sigma_0 admitting a certificate, with the Stage III ceiling kappa' in place of
5/6. If (ii) gives sigma_0 < 0.8317 inside the model, the next step is to read §§8, 17-19 for the
validity ranges the model is missing before believing it. If it gives nothing below 7/8, we have learned
that the geometry is not where the slack is, and the remaining lever is the moment estimates themselves.

**What not to conclude.** Nothing here moves RH: the bootstrap is a contradiction argument that needs new
estimates at every stage, and the family supremum beta_* can only be pushed by estimates that hold
uniformly over all Hecke targets. The converter's quadratic loss means even theta = 0.8 would only give
Lambda <= 0.18. The value of Stage III, if it exists, is a kernel-checked record on Lambda and a second
data point on how this method scales; that is worth having and is honestly described.

## Pointers

- paper1: Prop. 2.1 (p. 8-9), Thm 3.1 (p. 10), §12 (p. 85-86), §20 (p. 186-195); paper2: §2-3 (p. 3-12).
- Lean: Hecke/ZeroSupremum.lean (beta, beta_le_seven_eighths_of_uniform_margin); Supremum.lean
  (continuationMargin); Endpoint.lean (Lemma 20.2); ParametersCentralBudget.lean, ParametersHighData.lean
  (the order of choices as a structure); Detector/FinalAssemblyUnconditional.lean (the top);
  Nonvanishing.lean (the exported statements).
- Ours: telperion/examples/oai_qrh_bridge (the composition), docs/QRH_DBN_BRIDGE_2026-10-07.md.
