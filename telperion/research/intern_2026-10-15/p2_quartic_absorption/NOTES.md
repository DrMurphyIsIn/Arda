# Pitch 2: does Mobius absorption need the quartic theta coefficient exactly? (2026-10-15)

Status: a reading pass, not a result. Nothing here is progress on RH. `conjecture1_proved = False`.

Sources read: `paper.tex` (Sept 30, 16,677 lines) and `paper2.tex` (Oct 5, 3,988 lines) from openai/math at
commit `1581d4cb` (cloned as untrusted data; only the .tex files were read). Line numbers below are
`paper.tex` unless marked `p2:`. Background: `telperion/docs/SEXTIC_BOTTLENECK_2026-10-11.md` (sections 4-7).
Script: `quartic_jacobi_check.py` (my own, in this directory; output in `quartic_jacobi_check.out`).

## Verdict first

The verdict is **(a) for the question as asked, plus a (c)-type relocation of the blocker.**

1. **(a) In the paper, the theta enters as an identity, not as a bound.** The Mobius absorption is a
   Gauss-sum identity (Gauss-Jacobi, Hasse-Davenport, and the cubic Jacobi-sum sign `gamma_2^3 = mu alpha`).
   The theta coefficient formula is then used to identify a sum of Gauss-sum coefficients exactly with a
   Fourier expansion of Kubota's cubic theta. That identification is what allows the automorphy (the
   transformation law) to be applied (l. 1987-2001, 2059-2066, 2303-2310). It is used again, as exact
   complete multiplicativity of the cube-completion weights, to Mobius-invert the cube completion
   (l. 9839-9856; p2: 427-484, Lemma `cube-reduction` p2: 1341). A mean-square bound cannot feed either
   step: a modular transformation law cannot be applied to a sequence known only in mean square, and
   Mobius inversion needs the exact weights. Size bounds are consumed only on the dual (reflected) side,
   where they already suffice: the paper uses a pointwise bound plus support structure, and a mean-square
   bound would do (classified S below).
2. **The theta gives no pole or residue in this paper.** The completed theta series `T(s, Psi)` is
   entire: the `d/d zbar` kills the constant term (l. 2331), the mask has `phi(0) = 0` (p2: 1716), and
   l. 1750 and 2362-2370 state it. There is no Heath-Brown-Patterson `X^{5/6}` term anywhere. The
   principal signal (`zeta_F^S(6z)` pole, `1/L^S(x, eta)`) comes from the Poisson side, through the
   Gauss-Jacobi identities (l. 3966-3975, 4117-4126 => 4042-4045), with no theta involved. One line of
   the bottleneck note (section 4: "its residue is the sparse X^{5/6} term") does not describe how
   paper.tex uses the theta.
3. **(c) At k = 4, absorption is not the blocker, and the one undetermined quartic coefficient is not the
   precise blocker either.** At k = 4, Mobius is absorbed exactly and elementarily, with no
   Hasse-Davenport step. The quartic Jacobi sum is `J(chi,chi) = -chi(-1) pi`, which gives
   `mu(p) gamma_{-1}(p) = conj(alpha(p)) gamma_1(p)` (checked numerically at 9 primes; see below).
   But the absorbed coefficient is the quartic Gauss sum itself: absorption does not lower the order. The
   k = 6 proof works because Hasse-Davenport lowers 6 to 3 and the cubic theta's multiplier then lowers
   the row kernel to quadratic (`chi^{-1} chi^{-2} = chi^{-3}`, p2: 410). For k = 4, no known automorphic
   object does both of these:
   - (i) carry `gamma_1(n) chi_n(h)` as directly summed coefficients, with known completion weights;
   - (ii) reflect the quartic row kernel into a quadratic one.

   The quartic theta has quartic Gauss sums only at SQUARE indices (Suzuki). At those indices the quartic
   row twist cannot be written as a periodic function of the index. Its other coefficients (the unknown
   `tau(nu)`) would enter the completion as exact, non-multiplicative weights. Kubota's quartic Eisenstein
   series carries the right coefficients exactly and needs no theta coefficient at all (its residues
   vanish for the twisted series). But its functional equation keeps the kernel quartic. So a mean-value
   theorem for the one undetermined coefficient would not rescue the architecture. Even Patterson's
   conjectured exact value (`tau(pi)^2 N(pi)^{1/4} ~ g_4(pi)`, a square root of a Gauss sum) would not
   make the squarefree-index coefficients into Gauss sums.

## 1. Use-by-use table (paper.tex unless `p2:`)

E = exact identity needed. S = only a size or average bound is consumed.

| # | Lines | What is used | Class | Why (short quote / reason) |
|---|---|---|---|---|
| 1 | 766-840 (Lemma "Prime Gauss identities"); key steps 803, 833-834 | `gamma_2(p)^3 = -alpha(p)` (from `J(H^2,H^2) = -p`) and `gamma_1 gamma_2 = conj(H(4)) gamma_3 gamma_2^3` (from `J(H,H^3) = H(4) J(H,H)`, the Hasse-Davenport step) | E (the source identity) | "the congruence forces `u=-1`. Finally, `tau_2^3 = J(H^2,H^2) tau_2 tau_4 = -pP`" (l. 833-834). The `-1` per prime IS the Mobius sign. |
| 2 | 965-967, 1040-1051 (eq. `signal`) | squarefree extension `gamma_2(c)^3 = mu(c) alpha(c)`, `gamma_1(c) gamma_2(c) = mu(c) alpha(c) G(c)` | E | proved "by induction on the number of prime factors" via CRT cross factors; p2 states the consequence as eq. `convert2` (p2: 850): `mu(n) gamma_{-1}(n) = chi_n(-1) G(n)^{-1} conj(alpha(n)) gamma_2(n)` |
| 3 | 1895-1901 | automorphy `theta(gw) = kappa(g) theta(w)`, `kappa = (c/a)_3` | E (input) | the multiplier is the CUBIC symbol (`chi_p^2` in sextic notation); this is where the `-2` in `chi^{-j-2}` comes from |
| 4 | 1987-1993, 1998-2001, 2059-2066, 2303-2310 | Patterson/DR coefficient `d_I(lambda^{-3} n b^3) = 3^{5/2} |b| g~_3(n)` and `g~_3(n) = chi_n(lambda)^{-2} gamma_2(n)` | **E** | "Combining Equations ... on the retained domain now identifies the direct Mellin series with the product `T`" (l. 2061-2064). Without this identification, the theta transformation says nothing about the Gauss-coefficient sum. |
| 5 | 1676-1850 (Prop. "Completed cubic reflection"), local factors 1783-1789 | the reflection identity itself, `B_p = chi_p^{-j_p-2}` | E | an equality of two series (eq. `reflection`); its local factor at `j=1` is the quadratic `chi_p^3`, which is what lets the quadratic large sieve in |
| 6 | 1827-1832 (eq. 4.3), 1945-1990; consumed at 2351, 2858-2864, 2680-2745, 7733, 8256, 11532 | dual cusp coefficients `d`: support `u lambda^k n b^3` and `|d| <= 27 3^{k/6} |b|` | **S** | "Their coefficient bound leaves the column normalization `q_n^{-1/2} q_b^{-1}`" (l. 2860). Lemma "Quadratic reduction for completed indices" takes "arbitrary complex coefficients" and outputs a bound in `sum |beta|^2` over arithmetic sub-supports. The pointwise bound is a convenience; an l^2 bound over those sub-supports would do. The support SHAPE (`n b^3`) is used structurally to split off the cube and the collision mask. |
| 7 | 1750, 2331, 2362-2370; p2: 1716 | constant term of theta | n/a (no pole) | "the derivative removes `C_H(v)` from every cusp expansion" (l. 2331); "continues `T` to an entire function" (l. 2370) |
| 8 | 3327-3420 (probe definition) | inserted correction `conj(G(cn^3))` and `R(A,s)` | E (design) | "the factor `R(A,s)` cancels the cross-prime reciprocity phases ... while `conj(G(A))` cancels the remaining pair phases" (l. 3376-3378): coefficientwise phase cancellation |
| 9 | 3847-4200, esp. 3966-3975, 4117-4126 => eq. `probe-high` 4042-4045 | `gamma_2 = mu alpha G / gamma_1`; `gamma_1 gamma_2 = -alpha conj(chi_p(4)) gamma_3`; `gamma_4/gamma_1 = -conj(alpha)/G` | **E** | needed to get the exact factorization `F = zeta_F^S(6z) L^S(w,.) / L^S(x, eta conj(chi(u))) H`; the principal row must contain `1/L` exactly, and no bound produces a reciprocal L-function |
| 10 | 9839-9856 (paper.tex cube inversion); p2: 427-484, p2: 1341-1480 | complete multiplicativity of the completion weight `w_h(b) = conj(alpha(b))^3 xi(b)^3 chi_b(h)^3`, inherited from `c_theta(n b^3) = |b| x (stuff)` | **E** | "one cannot simply discard the terms with `b != 1`, because the contributions from different `b` can cancel. We begin by undoing the addition of cube factors using Mobius inversion" (p2: 427); the identity's check uses `sum_{h|c} mu(h)` |
| 11 | 7264-7300, 7420-7434 (Part II marked completion) | same coefficients `a(n) = conj(alpha) gamma_2 nu rho`, reflection reused | E (inherits #4) | "finite inclusion-exclusion between compatible branches, not a new theta identity" (l. 7433-7434) |
| 12 | 10208-10240, 10772-10780, 11803-11806 (inverse-moment recursion and initialization) | twisted multiplicativity `gamma_2(ab) = gamma_2(a) gamma_2(b) chi_b(a)^4`; `mu(z) gamma_{-1}(z) = conj(alpha) gamma_2 chi_z(-1) conj(G)` | **E** | after each Poisson pair, the coefficients must return to the canonical family of Lemma `canonical-moment` (l. 9296), on which #4-#6 apply again; with unknown coefficients the induction does not close |

Summary: every forward use (1, 2, 4, 5, 8, 9, 10, 12) is E. The only S use is the reflected-side
coefficient size (6), and there an l^2 bound would already suffice.

## 2. Pole or bound?

Neither, in the sense the question intends. The theta supplies an exact transformation law of an entire
Mellin series. Its constant term is removed by construction (#7), so no residue or sparse main term is
taken from it. The paper's main term is the Poisson-side pole of `zeta_F^S(6z)` at `z = 1/6` and the
`1/L` in row `u = 1` (#9). These come from Gauss-Jacobi identities, not from the theta. So "the theta's
residue breaks the circularity" is not the mechanism in paper.tex. What the theta supplies is the
order-lowering reflection (#5): sextic mask times cubic multiplier gives a quadratic kernel, and the
quadratic large sieve has no `(KD)^{2/3}` term.

## 3. Why k = 6 works with only the cubic theta, and what k = 4 would need

**k = 6.** The 6-fold cover never appears. The only theta is Kubota's cubic theta on the 3-fold cover
(multiplier `(c/a)_3`, l. 1898-1901; "the Gauss sums use only the cubic symbol", l. 1951). The sextic
structure lives entirely in the twist `chi_n(u) = (u/n)_6`. Poisson in `u` produces the sextic
`gamma_{-1}(n)`. Hasse-Davenport (with the quadratic `chi^3`) plus the cubic sign `gamma_2^3 = mu alpha`
rewrite `mu gamma_{-1}` as (ray factor) x `conj(alpha) gamma_2`, an order-3 object (#1-#2). So the "two
undetermined coefficients of the 6-fold theta" are irrelevant to the paper. Two order reductions do the
work: Hasse-Davenport takes 6 to 3, and the cubic multiplier takes the row kernel to quadratic.

**k = 4 (over Q(i)).**
- *Absorption works exactly, without Hasse-Davenport.* For primary `pi` with `N(pi) = p = 1 mod 4` and
  quartic `chi`, one has `J(chi,chi) = -chi(-1) pi`. Hence `gamma_1(pi)^2 = -chi(-1) alpha(pi)` (times a
  quadratic Gauss-sum sign that is a ray-class factor). This is the exact quartic analogue of
  `gamma_2^3 = -alpha`, and it gives
  `mu(pi) gamma_{-1}(pi) = conj(alpha(pi)) gamma_1(pi)`.
  - CHECKED numerically: `quartic_jacobi_check.py` verifies `J = -chi(-1) pi` at p = 5..53 and the
    absorption identity at p = 5..73, with additive character `x -> e(x/p)` via `Z[i]/pi = F_p`. With the
    trace character the extra factor is a fixed ray-class phase (FROM MEMORY, not checked).
  - CHECKED in the literature: DDHL (1.2) records `g~_4(pi)^2 = -(pi/|pi|)^{-1} (-1/pi)_4 (pi/pi-bar)_4^{-2}`.
  - Extension to squarefree `n` via CRT and quartic reciprocity: routine, not done.

  So the bottleneck note's original "degenerate at k = 4" (already lifted in its 2026-10-15 update) is now
  sharper: Mobius is absorbed. But the absorbed coefficient is the quartic Gauss sum `gamma_1(n)`, and
  there is no order reduction (Hasse-Davenport with the quadratic character is degenerate, as the update
  says).
- *What the reflection would need.* An object on the 4-fold cover with the quartic Kubota multiplier
  (local factor `chi^{-1} chi^{-1} = chi^{-2}`, quadratic, at `j = 1`; this is my inference by analogy
  with l. 1783-1789). Its directly summed coefficients would have to be `gamma_1(n)` at squarefree `n`,
  with known multiplicative completion weights. The candidates:
  - **4-fold theta (route i).** Its coefficients at squarefree indices are the undetermined ones.
    Patterson's conjecture (Eckhardt-Patterson) is `tau(pi)^2 N(pi)^{1/4} ~ g~_4(pi)`, so not a Gauss
    sum even if true. Quartic Gauss sums occur at square indices: `psi(m^2 nu) = g_4(nu,m) N(m)^{-3/4}
    psi(nu)` (Suzuki Thm 5), and `psi(m^3 nu) = 0` (Suzuki Thm 4). Using them meets three walls:
    1. (Inference.) The row twist `chi_m(h)` is not a function of the index `m^2` mod `h`: a quartic
       character is not even when `p = 5 mod 8`. So no periodic mask on the theta index reproduces the
       quartic row character.
    2. Completing over the full support `nu m^2 k^4` brings in the unknown `tau(nu)` as slice weights.
       Each `nu`-slice carries the extra column twist `conj((nu/m)_4)`, i.e. a different row. The
       paper's inversion (#10) needs known, completely multiplicative weights at the SAME row, and
       squarefree-index theta coefficients for n = 4 are not expected to be multiplicative (Patterson's
       conjecture is phrased through Dirichlet series without Euler product, per DDHL p. 17).
    3. A mean-square bound `sum_{N nu <= V} |tau(nu)|^2 << V^{1+eps}` would only let one bound the
       `nu != 1` slices by Cauchy-Schwarz over rows that grow like `H N(nu)^3`. I do not see this
       closing, and the paper itself declines to bound `b != 1` slices even with exact weights
       (p2: 427). Not a proof of impossibility.
  - **Kubota's quartic Eisenstein series (route ii).** After absorption, the column sum is a smoothed
    partial sum of `psi^{(4)}(s, nu, l)` with `l != 0`. Here `nu = h` or `h^3`, depending on the
    orientation of the Poisson step (not settled here); this is my inference from
    `sum_x chi_n(x) e(nu x/n) = conj(chi_n(nu)) g(n)`. Its continuation and functional equation are known
    exactly (CHECKED, DDHL section 4; Diaconu 2004). It is holomorphic in `sigma > 1` for `l != 0`
    (CHECKED, DDHL 4.1), so no theta coefficient enters at all; for `l = 0` the residues are theta
    coefficients, entering only through size. So on this route the unknown quartic coefficient is not
    the blocker. The blocker is that the functional equation maps `psi(s, nu)` to `psi(., nu')` with the
    same `nu` up to `lambda`-powers (DDHL 4.16). The dual kernel stays QUARTIC, and the conductor is
    GL_1-type in `nu` (DDHL Remark 8.3). There is no `chi^{-1} chi^{-2}`-style conversion to a quadratic
    kernel, so the "reflected energy by the quadratic sieve" step (l. 2848-2870) has no analogue. The
    general quartic sieve carries extra mixed terms (dFDH lower bound `A^{3/4}B^{1/2} + ...`; FROM the
    bottleneck note section 7, not rechecked). (Inference; I did not attempt the exponent bookkeeping.)

Net: the precise blocker for k = 4 is the absence of an order-lowering reflection for quartic twists.
That is: no known 4-fold-cover object turns `sum_n gamma_1(n) chi_n(h)` into a dual sum with a quadratic
kernel. The single undetermined coefficient is one face of this (route i), not the whole of it.

## 4. Literature (with tags)

- David-Dunn-Hamieh-Lin, arXiv:2306.11875 v4 (read via alphaXiv, pp. 1-17, 25, 35). CHECKED
  (https://arxiv.org/abs/2306.11875):
  - n/2 - 1 undetermined coefficients (p. 5, citing Hoffstein 1993 and Broker-Hoffstein 2016);
  - Suzuki Thms 3-6: biquadrate periodicity, cube vanishing, the square formula (1.10)/(4.39), and the
    quadratic support condition (4.40)-(4.41);
  - Patterson 1984 / Eckhardt-Patterson 1992 Conj. 2.11: `tau(pi)^2 N(pi)^{1/4}` proportional to
    `g~_4(pi)`, "wide open", "shown to hold on average by Bump and Hoffstein [BH89, pp. 6-8]";
  - CFH 2012 sextic analogue and Broker-Hoffstein numerics;
  - `psi^{(4)}(s, nu, l)` holomorphic in `sigma > 1` for `l != 0`;
  - their Type II uses only twisted multiplicativity plus the quadratic sieve, and gets `X^{5/6}`.
- Mean-square bounds for quartic theta coefficients:
  - Bump-Hoffstein 1989 average result: CHECKED as cited by DDHL; content FROM MEMORY.
  - A Rankin-Selberg mean square `sum |tau(nu)|^2 ~ c V` follows from theta being square-integrable
    (residual spectrum) by unfolding `<|theta|^2, E>`. FROM MEMORY; no source checked.
  - Either kind of bound would serve only the S-type dual-side use (#6), which is not where the
    obstruction is.
- Suzuki 1983 (J. reine angew. Math. 340) and Eckhardt-Patterson 1992 (Proc. LMS 64): content CHECKED only
  as reported by DDHL.
- Hoffstein 1992, "Theta functions on the n-fold metaplectic cover of SL(2) - the function field case":
  existence CHECKED via a bibliographic listing (https://sugaku.net/oa/A5009347658). The claim that it
  proves Patterson's quartic conjecture over `F_q(T)` is FROM MEMORY / the project survey; I could not
  open the paper.
- `J(chi,chi) = -chi(-1) pi` for quartic `chi` (Ireland-Rosen ch. 9): CHECKED numerically here; the
  textbook citation is FROM MEMORY.

## 5. Function-field remark

Running the k = 4 architecture over `F_q(T)` (q = 1 mod 4) would be a legitimate, cheap test of one
thing. Granted the quartic theta coefficients are known there (Hoffstein 1992, FROM MEMORY), does the
completion-and-inversion step (#10) close when the slice weights `tau(nu)` are known but
non-multiplicative, and does the exponent system (law `1 - (1 + 3 ell)/(2k)`, high side) then close at
k = 4? It would prove nothing about zeta: RH holds over function fields, so the target zero-free strip
is known. Two cautions limit what the test would show:
- Even with Patterson's conjecture true there, `tau(pi)` is a square root of a Gauss sum, not a Gauss
  sum, so the row-twist obstruction (route i, wall 1) and the quartic-kernel obstruction (route ii)
  persist. The test would most likely fail for the same structural reason, not an exponent reason.
- Function fields add exactness the number field lacks (exact Poisson, discrete degrees, no archimedean
  gamma factors), so a success there would be weak evidence for Q(i).

It is worth doing only as a 1-2 day bookkeeping exercise to confirm the structural verdict, not as an
attack route.
