# The Li face of the wall: campaign brief (2026-09-21)

conjecture1_proved = False. Nothing in this campaign proves, or is meant to prove, anything
about the Riemann Hypothesis. Every target below is an identity, an implication with a named
hypothesis, or a finite unconditional inequality.

## 0. Two faces, one wall

The rh and mirrormere campaigns hold, in the kernel, two RH-equivalences:

* Weil positivity on the two-parameter Gaussian family F(c, lam) (rvm_bridge island,
  `RvMBridge10.rh_iff_gaussian_positivity`), with its wall map: free region = ladder (zeros
  verified on the line up to height T) plus the envelope lam <= lam_*(T); the diagonal is RH.
* Li's criterion, RH <-> for all n, 0 <= Re(taylorCoeff riemannXi n) (li_positivity island,
  upstream package `LiCriterion` at rev 35df682f, theorem `li_criterion_rh_iff`, hypothesis-free).

The Bombieri-Lagarias explicit formula (B7, `RvMBridge27.bl_explicit_formula`) says what each
Li coefficient IS. This campaign asks what its SIGN costs, rung by rung, and maps that cost
against the Gaussian face. The answer, derived below, is that the Li face is a ladder too, with
a clean exchange rate: zeros on the line up to height T buy every rung n + 1 <= pi T / 2.

## 1. Vocabulary (li island, upstream package)

* `NontrivialZero := {rho : C // riemannZeta rho = 0 /\ 0 < rho.re /\ rho.re < 1}`.
* `pairedZero rho` has value `1 - rho` (NOT the conjugate).
* `liSummand n rho = 1 - (1 - 1/rho)^(-(n+1))`.
* `liPairedSummand n rho = liSummand n rho + liSummand n (pairedZero rho)`.
* `taylorCoeff f n = deriv^[n] (logDeriv (phi f)) 0 / n!` with `phi f z = f (1/(1-z))`;
  `riemannXi s = (1/2) s (s-1) completedRiemannZeta_0 s + 1/2`.
* Upstream, hypothesis-free: `xi_hasFiniteOrder`, `xi_order_le_one` (XiOrderBridge), and from
  them `xi_weighted_genus_one_of_hadamard_order_one` (summability of m(rho)/|rho|^2) and
  `xi_factorization_prod_with_multiplicity_of_hadamard_order_one` (the Hadamard product).
  `weighted_paired_sum_formula_of_standard_hypotheses` then gives, for every n,

      taylorCoeff riemannXi n = (1/2) * sum' rho, m(rho) * liPairedSummand n rho,

  where m(rho) = analyticOrderNatAt riemannXi rho.val. Composing these is the first task.

Convention: rung index n (li island) <-> Li's lambda_{n+1} <-> `liLimit (n+1)` on the rvm island
(E6Bridge15, where `liKernel N rho = 1 - (1 - 1/rho)^N` and `liPaired` pairs rho with conj rho).

## 2. The pair term in polar form

Write N = n + 1 and w := rho / (rho - 1) = (1 - 1/rho)^(-1). Then, since
1 - 1/(1 - rho) = rho/(rho - 1) = w,

    liSummand n rho = 1 - w^N,   liSummand n (1 - rho) = 1 - w^(-N),
    liPairedSummand n rho = 2 - w^N - w^(-N).

With w = r e^{i theta} (r = |w| > 0, theta = arg w):

    Re liPairedSummand n rho = 2 - (r^N + r^(-N)) cos(N theta) = 2 - 2 cosh(a) cos(b),
    a := N log r,  b := N theta.

For rho on the line, |rho| = |rho - 1| so r = 1, a = 0, and the term is 2(1 - cos b) >= 0.

## 3. The termwise lemma (the whole Li ladder rests on this)

Lemma A. If |a| <= |b| <= pi/2 then cosh(a) cos(b) <= 1.
Proof: cos is decreasing on [0, pi/2], so cos b <= cos a, and cosh(a) cos(a) <= 1 on [0, pi/2]
because f(a) = cosh a cos a has f(0) = 1 and f'(a) = sinh a cos a - cosh a sin a <= 0
(equivalently tanh a <= a <= tan a).

Lemma B (geometry of a zero). Let rho = beta + i gamma with 0 < beta < 1 and gamma > 0
(gamma < 0 is the conjugate; the pair is symmetric under rho <-> 1 - rho, which sends
(log r, theta) to (-log r, -theta)). Then

    |theta| = arctan(beta/gamma) + arctan((1-beta)/gamma)          (exact),
    |theta| <= 1/gamma                                             (arctan x <= x),
    |log r| <= (1/2) |2 beta - 1| / (min(beta, 1-beta)^2 + gamma^2) <= 1/(2 gamma^2),
    and for gamma >= 1: |theta| >= pi/(4 gamma)  (arctan x >= (pi/4) x on [0,1]),
    hence |log r| <= |theta| whenever gamma >= 1. (Skeptic: this route needs gamma >= max(beta, 1-beta);
    the inequality itself holds down to gamma ~ 0.285, but state it for gamma >= 1, or for the box
    region of section 4. State Lemma B for arbitrary complex rho: w(conj rho) = conj(w rho).)

Theorem C (termwise nonnegativity). If rho is a nontrivial zero with |Im rho| >= max(1, 2N/pi)
then Re liPairedSummand (N-1) rho >= 0, whether or not rho is on the line.
Proof: a = N log r, b = N theta; |a| <= |b| by Lemma B, |b| <= N/gamma <= pi/2; apply Lemma A.

Theorem D (the Li ladder). Let T >= 1. If every nontrivial zero with |Im rho| <= T has real
part 1/2, then 0 <= Re(taylorCoeff riemannXi n) for every n with n + 1 <= pi T / 2.
Proof: every term of the paired sum is >= 0 (on-line zeros by section 2, the rest by Theorem C),
m(rho) >= 0, Re of the tsum is the tsum of Re (summable by the weighted genus theorem), and a
tsum of nonnegatives is nonnegative.

Corollary (composition, conditional): `AllZeros_h4000` gives all zeros with 0 < Im <= 4000 on the
line under its band hypotheses (Arb winding numbers etc., stated as hypotheses). Negative Im
follows by conjugation; real zeros in (0,1) are NOT covered by the capstone and a hypothetical
real zero beta /= 1/2 makes every even rung's pair term negative, so the composition also needs
Box 1 (section 4) or an explicit real-zero exclusion. Under those hypotheses, rungs n = 0 .. 6282
are nonnegative. The existing rung certificates carry one
Arb enclosure hypothesis per rung; the ladder replaces them by the height certificates and
extends the reach. It is still conditional. With T = 3 * 10^12 (Platt-Trudgian, NOT in kernel)
the same theorem would give n + 1 <= 4.7 * 10^12.

Rung 0 (Li's lambda_1) needs no height at all: N = 1 gives 2 - w - 1/w = 1/(rho (1 - rho)),
whose real part is (beta (1 - beta) + gamma^2)/|rho (1-rho)|^2 > 0 for every zero. So the open
node RH_li_rung0_kernel (roadmap B2) closes with no hypothesis.

## 4. The low-height box (folklore-level, new to the islands)

For Re s > 0, s /= 1: zeta(s) = s/(s-1) - s J(s), J(s) = int_1^infty {x} x^(-s-1) dx, and
|J(s)| <= int_1^infty {x} x^(-sigma-1) dx <= 1/(2 sigma) (the last by parts: the difference
from (1/2) int x^(-sigma-1) is (sigma+1) int B(x) x^(-sigma-2) with B = ({x}^2 - {x})/2 <= 0).
On the rvm island Zeta23's `Zeta0EqZeta` gives the representation; the {x}-kernel bound must be
proved on both islands by midpoint reflection on each unit interval (E6Bridge25 used the sawtooth
kernel with the trivial 1/2 bound, which only yields |t| >= 0.770; rung 4 needs gamma >= 0.806).

If zeta(s) = 0 with s = sigma + i t, 0 < sigma < 1, then |s|/|s-1| <= |s|/(2 sigma), i.e.
4 sigma^2 <= (1 - sigma)^2 + t^2. The functional equation makes 1 - conj(s) a zero too, giving
4 (1 - sigma)^2 <= sigma^2 + t^2. Adding: (sigma - 1/2)^2 <= t^2/3 - 1/4. Hence

    Box 1: no nontrivial zero has |Im s| < sqrt(3)/2.
    Box 2: every nontrivial zero satisfies (Re s - 1/2)^2 <= (Im s)^2 / 3 - 1/4.

Consequences: with Box 1 and 2, Lemma B's |log r| <= |theta| holds for every zero (gamma >= 0.866
> 2/pi and (1-beta)/gamma <= 0.91 <= 1 for gamma < 1), so Theorem D's proof also runs for T in [sqrt(3)/2, 1), which gains nothing beyond N = 1.
Rungs 0..4 (Li's lambda_1..lambda_5) should be nonnegative with NO hypothesis: for N <= 5 the
angle satisfies |b| <= 5 |theta| <= 5 pi/3 < 2 pi, and the only region where cos b > 0 with
cosh a > 1 is b in (3 pi/2, 5 pi/3], forced near gamma ~ 0.87 where the confinement pins beta near
1/2 and a is small (numerically cosh(a) cos(b) <= 0.4995 there; the Lean case work needs the EXACT bound
log r <= (1/2) log 1.661 = 0.2537 from |beta - 1/2| <= 0.266 at gamma < 0.981, since log(1+x) <= x
does not close). Skeptic numerics: minima of the pair term on the box region are 0.059, 0.23, 0.51,
0.88, 1.02 for N = 1..5, and rungs 1..4 need only Box 1 (beta free). Rung 5 (N = 6) FAILS termwise
(-0.71 at (0.30, 0.93); -0.53 at (0.64, 0.9)), so 0..4 is the honest hypothesis-free reach of this
method; beyond it the ladder needs height. This is kernel novelty, not new knowledge about lambda_n.

## 5. The rvm island copy

E6Bridge15's `liLimit N = sum' rho, m(rho) * Re(liKernel N rho)` runs over all rho with the
Zeta23 divisor and pairs rho with conj rho. Regroup by the involution rho <-> 1 - conj rho (the
divisor is symmetric under conj (E6Bridge15) and under s <-> 1 - s (functional equation)); the
pair (rho, 1 - conj rho) gives Re(liKernel N rho) + Re(liKernel N (1 - conj rho))
= 2 - (r^N + r^(-N)) cos(N theta), the same expression. So Theorems C and D transfer verbatim:
`liLimit_re_nonneg_of_line_below`, and with `RvMBridge27.liValue`, the closed-form inequality
0 <= Re(archSide N + finiteSide N) for those N. `liLimit 1` is nonnegative with no hypothesis.

## 6. What this is not

* Not an effective converse. An off-line zero forces some rung negative (upstream
  `li_pos_implies_rh`), but WHICH rung depends on the whole zero set; no clean N*(beta, gamma).
* Not new information about zeros. The ladder consumes zero localisation; it does not produce it.
* Not an attack on the diagonal. Rung N probes heights up to ~ pi T/2 with T the verified height;
  the Gaussian face probes offsets delta at width lam ~ 1/delta^2 at every height at once. Both
  are the same wall in different coordinates; section 7 of the wall map v2 will tabulate this.

## 6b. Skeptic pass

Reviewed 2026-09-21 (LI_FACE_SKEPTIC_2026-09-21.md): no item refuted; corrections above folded in.
Summability for Re-of-tsum on the li island: `summable_weighted_Li_paired_summand_of_weighted_genus`.
Divisor symmetry on the rvm island: `RvMBridge20.isNontrivialZero_one_sub_iff`, `zeroMult_one_sub`.

## 7. Workstreams

* li-rung0 (li island, v4.34): compose the upstream inputs into the hypothesis-free paired tsum;
  Lemmas A, B; Theorems C, D; rung 0; the h4000 composition.
* li-box (li island): Boxes 1 and 2 hypothesis-free from Mathlib or a port of Zeta0; then rungs
  1..4 hypothesis-free.
* rvm-li (rvm island, v4.33.0-rc2): section 5.
* survey-li: literature on Li coefficients (Keiper, Bombieri-Lagarias, Coffey, Maslanka, Voros,
  Arias de Reyna, Johansson, Sekatskii, Lagarias, Freitas) and on unconditional Weil positivity
  for Gaussian or small-support test functions (Connes-Consani, Yoshida, Burnol,
  Balanzario-Cardenas): is the exchange rate n + 1 <= pi T/2 known, and is anything stronger?
* numerics: lambda_n from the zero sum and from B7's closed form; the termwise lemma checked over
  the box region; the first failing rung per (beta, gamma).
* skeptic: break sections 3 and 4 before the Lean agents rely on them.
