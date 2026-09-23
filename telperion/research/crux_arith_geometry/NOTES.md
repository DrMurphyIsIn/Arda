# NOTES -- lens: ARITHMETIC GEOMETRY / TRANSFER FROM WEIL
(re-run of a lens whose previous final answer overflowed; long material lives HERE, final answer is compact)
conjecture1_proved = False. RH is open. Nothing here proves or reduces RH.

## S0. Working plan
1. Pin down the missing ingredient precisely (dictionary Weil/Deligne/Bombieri-Stepanov <-> Spec Z).
2. Literature check (Connes-Consani scaling site / RR, Lagarias-Rains, Deninger, Kurokawa, Yoshida, Bombieri).
3. Candidate toy structures; kill weak ones with the four dossier tests (a) relabel (b) DH/Epstein blind (c) finite-height / small-width collapse (d) reflection-invariant.
4. Prove what can be proved in the toy; run python experiments here; keep scripts in this dir.

## S1. Initial dictionary (curve C/F_q  vs  Spec Z)
- Castelnuovo on C x C for D = m Gamma_F + n Delta gives g q m^2 + a m n + g n^2 >= 0 (a = q+1-N), i.e. |a| <= 2 g sqrt q.
  Normalized Frobenius-graph Gram matrix: M'_{ab} = q^{-|a-b|/2} + q^{|a-b|/2} - sum_i z_i^{|a-b|} (z_i = alpha_i/sqrt q).
  Hyperbolic plane (fibers) gives signature (1,1); H^1 (x) H^1 part must be negative definite  <=>  RH for C.
- Z-analogue: the intersection form on span{Gamma_{e^u}} is the Weil distribution; Hodge index = Weil positivity.
  Nothing new at this level (Connes, Deninger, Haran, Connes-Consani).
- Window-L Weil positivity for curves: test functions on Z (degrees) supported in [-L,L]; for L >= ~2g+1 it is
  equivalent to RH for C; for L << 2g it holds generically even for FE-only (DH-type) polynomials because one
  cannot isolate a zero (averaging over ~2g zeros).  Over Z: window L <-> zeros to height ~ e^{cL}.
  For curves, ALL windows follow from ONE uniform argument (Hodge index); for Z only small windows are known,
  by finite computation (Yoshida, Zhu), with collapsing margin.

## S2. Literature landscape (checked 2026-09-23)
- Connes 2026 survey arXiv:2602.04022 ("Letter to Riemann"): QW_lambda = Weil form on supp in [1/lambda, lambda];
  minimal eigenvector eta_x has Fourier zeros on the line (Connes-van Suijlekom Thm 6.1, assuming simple even
  minimal eigenvalue; FE-GENERIC: holds for ANY real even distribution kernel -> applies verbatim to DH).
  Strategy: prove eta_x -> Xi (Hurwitz). Remaining steps: simplicity/evenness for all lambda + convergence.
  Near-radical: range of E(f)(u)=u^{1/2} sum_n f(nu) (Poisson/ Mellin = zeta * fhat) is in radical of global form.
  Semilocal Y_S, semilocal trace formula; archimedean Weil positivity via Sonin space (supp in [2^-1/2,2^1/2]).
  Groskin arXiv:2605.20224: public implementation of the CvS Galerkin matrix, 300+ digits.
- Connes-Consani: Riemann-Roch strategy (1805.10501), RR for the ring Z (CRAS 2024), On the Jacobian of Spec Z
  (JNCG 2026): adele class space Riemann sector = monoidal extension of Pic of arithmetic curve.
- Lagarias-Rains (math/0104176): van der Geer-Schoof two-variable zeta Z_Q(w,s); no RH proved for w>0; w<0 has
  no zeros on the line (anti-RH), infinitely divisible semigroup. Not a route.
- DICTIONARY (function field): zeta numerator P(T) = char poly of Frobenius  <->  multiplier "zeta" on test fns;
  radical of the Frobenius-graph form = ideal (P(F)) (Cayley-Hamilton)  <->  range of E (Connes).
  Window 2g Toeplitz form has P in its kernel REGARDLESS of RH (FE + Cayley-Hamilton); Caratheodory-Fejer/Pisarenko:
  if PSD with 1-dim kernel then roots of P on circle. So positivity is exactly the missing input; C-F gives nothing.

## S3. Prior program docs read (do NOT re-propose)
- RH_F1_HODGE_INDEX_FRONTIER / RH_F1_SURFACE_BLUEPRINT / RH_BARRIER_CRACK / RH_ZERO_RIGIDITY (2026-08-30):
  identification already done: missing = Hodge-index signature on Spec Z x_F1 Spec Z (RH-equivalent rename);
  Connes-Consani square = semi-ringed topos (Newton polygons), Frobenius composition proven; Kurokawa tensor
  square = formal bookkeeping; Deninger Kaehler mechanism (Theta = 1/2 + skew) proven in models only;
  Deninger 2204.02714: no real-coefficient Weil cohomology for arithmetic curves.
- RH_BARRIER_FE_UNIFORMITY_DESIGN: Barrier I (FE-uniform bundle contains DH), Barrier II (Euler + growth caps at
  dlVP, DMV). Program's "sharpest statement": "Any proof must use both [Euler, FE], jointly and inseparably."
  => GAP I can fill: nobody checked whether Euler + exact FE JOINTLY suffice. Function field says NO (fakes).

## S4. Exploration log (discarded ideas, one line each; details were thought through, all collapse)
- 2x2 Castelnuovo block {phi, tau_{log p} phi}: contains the 1x1 block W(phi*phi*)>=0 = full RH. Relabel.
- Comb at p with tiny smoothing eps < p^-K: explicit formula involves ONLY local data at p and infinity
  (clean local-global identity) but provably blind: off-line pair term ~ eps p^{delta K} vs diagonal log(1/eps)
  >= K log p; detection needs delta >= 1. Discard (blind; = dossier test (c)).
- S-unit combs / prime-power-ratio-free supports: either tiny smoothing (blind) or prime-free window (known).
- Sign-constrained (Delsarte/LP) classes g(log p^k) <= 0: isolating a zero at height T needs Kronecker
  alignment of T log p => only astronomically high T => archimedean dominance. Dossier Kronecker floor.
- Kurokawa/Akatsuka/Tanaka absolute tensor square: has Euler product over prime pairs (Tanaka 2008.07752 Thm1.3)
  with small divisors 1/(m log p - n log q) (linear forms in logs; Baker = arithmetic Bombieri-Stepanov!),
  sign-indefinite; derived from zeta's own explicit formula => formal, carries no independent positivity.
- Bombieri-Stepanov over Z: missing absolute Frobenius (degree-multiplying ring endo fixing all residue fields);
  over Z residue fields F_p incoherent (orders p-1), uniform Frobenius x->x^{1+lcm(p-1)} kills economy.
- Base-change amplification (Deligne/tensor-power): over Z the 'base change' of zeta is zeta at a larger shift,
  so 'uniform first-Frobenius bound' = 'bound at all shifts' = RH (tautology).
- Pisarenko/Caratheodory-Fejer reading of Connes 2026: at window 2g the curve's minimal eigenvector IS the zeta
  numerator iff Hodge index; DH version being run by the crux-lee-yang lens (DH min eigenvalue -0.74 at lam^2=55).
  Not duplicated here.
- Selberg/graph toys: self-adjointness gives 'line or real axis'; for zeta real zeros are excluded elementarily,
  so a Selberg-type Laplacian would suffice = Hilbert-Polya (known).

## S5. CHOSEN IDEA: formal curves ("fakes") = Barrier III, and the periodicity obstruction
Formal curve of genus g over F_q: P in Z[T], P(T) = q^g T^{2g} P(1/(qT)), Z(T) = P/((1-T)(1-qT)) =
prod_d (1-T^d)^{-a_d} with all a_d in Z_{>=0}. Has every ZETA-LEVEL Weil ingredient (formal FE / curve RR,
Euler product with nonneg integer exponents, perfect integer counting, finite-rank q-symplectic Frobenius,
effective formal square via Dold/Witt closure, formal Lefschetz intersection numbers) but no SPACE-LEVEL
object (function field / surface / family). Claim: RH fails for most of them, zeros approach Re s = 1.
=> Euler + exact FE jointly decide nothing (upgrades program's Barrier I/II ledger).
Escape: fakes are q-periodic, cannot carry pi^{-s/2}Gamma(s/2) (poles of Gamma-ratio only on real axis).
Beurling-Hamburger rigidity conjecture: Beurling + exact Riemann FE => ordinary integers (uniformly discrete
case via Cordoba / Lev-Olevskii). If true: archimedean place turns fake-rich F_q situation into rigid one.

## S6. Formal curves: definitions, verified data (scripts in this dir)
Formal curve (q, g, P): P in Z[T], deg 2g, P(T) = q^g T^{2g} P(1/(qT)); Z(T) = P/((1-T)(1-qT)).
N_d := q^d + 1 - s_d, s_d = sum alpha_i^d (Newton, exact integers); a_d := (1/d) sum_{e|d} mu(d/e) N_e.
EFFECTIVE := all a_d in Z_{>=0}  <=>  Z(T) = prod_d (1-T^d)^{-a_d} (Euler product, nonneg integer exponents).
Completed xi(s) = q^{g(s-1/2)} P(q^{-s}): entire, order 1, xi(s) = xi(1-s), real on Re s = 1/2 (checked algebraically).
Scripts: formal_curves.py (genus 1), genus2_scan.py, cube_family.py, fake_detail.py, nonreal_trend.py.

Genus 1 (P = 1 - aT + qT^2), q in {5,...,101}: effective <=> -q <= a <= q (a = q+1 degenerate Z=1; a = -(q+1)
fails at d=2: a_2 = (q^2+q-a^2+a)/2 < 0). RH-true <=> |a| <= 2 sqrt q. Fakes = 2(q - floor(2 sqrt q)); q=101:
41 RH-true vs 162 fakes. Max Re rho over fakes (a = q): log((q+sqrt(q^2-4q))/2)/log q = 0.998 at q=101 -> 1.
(Real 'Siegel-type' zeros.)  Small-d conditions: a_1 = q+1-a, a_2 above, a_3 = (q^3-q-a^3+3qa+a)/3;
large d: |alpha| <= (q+sqrt(q^2-4q))/2 < q-1, dominance q^d(1-(1-1/q)^d) >> tail for d >= 5 (d<=5 exact).

Genus 2 scan (all c1,c2 in box): q=3: 57 RH / 9 real fakes / 8 NON-REAL fakes; q=25: 1369 RH / 14828 real /
22046 non-real fakes. Non-real fakes are the majority.

## S7. THEOREM (cube family, 'golden fake')
F(q,m): P = 1 + mT + (m^2-q)T^2 + qmT^3 + q^2T^4 = Phi_3(rT) Phi_3((q/r)T), Phi_3(x)=1+x+x^2,
r = (m + sqrt(m^2-4q))/2, m = r + q/r in Z. Frobenius quartet {r w, r w^-1, (q/r) w, (q/r) w^-1}, w = e^{2 pi i/3}.
For m > 2 sqrt q: r > sqrt q => off-line, NON-REAL (angles +-2pi/3); Re rho_max = log r / log q.
s_d = c_d t_d, c_d = 2cos(2 pi d/3) in {-1 (3 does not divide d), 2 (3|d)}, t_d = r^d + (q/r)^d (Lucas: t_d = m t_{d-1} - q t_{d-2}).
N_d = q^d + 1 + t_d (3 not | d), q^d + 1 - 2 t_d (3 | d).
Effectivity proof: a_1 = q+1+m >0; a_2 = (q^2-3q+m^2-m)/2 >= 0 (q>=3); a_3 = (q^3 - q - 2m^3 + 6qm - m)/3 >= 0
  is the BINDING constraint => m <= m*(q), m*/q -> 2^{-1/3}; d >= 4 with 3 not | d: N_d >= q^d, tail
  sum_{e<=d/2} |N_e| <= 6 q^{d/2} q/(q-1) <= 7.5 q^{d/2} => d a_d > 0 for q^{d/2} > 7.5; d >= 6, 3|d:
  N_d >= q^d(1 - 2 (r/q)^d) - 2 q^{d/2} >= q^d/2 - 2q^{d/2} (since (r/q)^3 <= 1/2 at m <= m*) => d a_d >= q^d/2 - 9.5 q^{d/2} > 0.
Numerics (cube_family.py): effective non-real for ALL m in [floor(2 sqrt q)+1, m*(q)], contiguous, q = 5..10007;
  m*/q -> 0.794; (1 - beta_max) log q -> 0.2310 = (log 2)/3.  => Re rho_max = 1 - (log 2)/(3 log q) + o(1/log q) -> 1.
Golden fake F(5,5): normalized zeros phi^{+-1} w^{+-1} (phi = golden ratio), Re rho = 1/2 + log(phi)/log 5 = 0.79899.
  N_1..N_4 = 11, 41, 26, 801; a_1.. = 11,15,5,190,748,1845,...; class number h = P(1) = 76.
  Castelnuovo |N_k - q^k - 1| <= 2g q^{k/2}: holds k=1 (5 <= 8.94), k=2 (15 <= 20), FAILS k=3 (100 > 44.7).
  In general for 2 sqrt q < m <= sqrt(6q): Weil bound holds at k=1,2 and fails at k=3 (AM-GM on t_3).
Zeta-level ingredients verified (fake_detail.py): formal square N_d^2 is Dold (a_d(square) integral, all >= 0 checked
  to d=30, dominance beyond); companion Frobenius preserves an integral nondegenerate q-symplectic form (solution space
  dim 2; example det 2500 for F(5,5), non-principal); Rosati involution F' = q F^{-1}; window-4 Toeplitz (Frobenius-graph)
  form has the formal numerator in its kernel (||T4 P|| = 4e-15, formal Cayley-Hamilton = exact radical) yet min eig -8.22.
  Min eigenvector (Connes/Caratheodory-Fejer approximant) has all roots on the unit circle at args +-0.6725 pi, +-0.1768 pi:
  NOT the fake's zeros (|z| = phi^{+-1}, args +-2pi/3).

## S8. Barrier III and its delimitation
Barrier III: any criterion whose hypotheses hold for every (entire, order<=1, self-dual, real-on-line) xi = G * E with E a
Beurling Euler product with nonneg integer exponents and perfect integer counting is refuted by F(5,5); no zero-free strip
follows from such hypotheses (F(q,m*) has non-real zeros with Re rho -> 1). Upgrades the program's sharpest statement
('must use Euler + FE jointly'): jointly is still not enough.
Periodicity obstruction (THEOREM): if all norms lie in q^Z then Z(s) is 2 pi i/log q periodic, so Z(1-s)/Z(s) is periodic;
with G = pi^{-s/2} Gamma(s/2) self-duality forces G(s)/G(1-s) = pi^{1/2-s} Gamma(s/2)/Gamma((1-s)/2) periodic; it has a pole
at s = 0 but none at 2 pi i/log q. Contradiction. So every formal curve (indeed any rank-1-norm Beurling system) is
excluded by the Riemann archimedean factor; Barrier III spares exactly arguments that consume Gamma(s/2) or N itself.
Beurling-Hamburger rigidity (CONJECTURE): Beurling system + exact Riemann FE (poles only 0,1, finite order) => N = {1,2,3,...}.
 Route: FE <=> nu = c delta_0 + sum_{n in N} (delta_n + delta_{-n}) self-dual (Bochner; Hilberdink-Lapidus Thm 3.2);
 if N uniformly discrete, Lev-Olevskii (Invent. 200 (2015)) => supp nu in finitely many cosets of a lattice; then residues of
 the multiplicative semigroup N mod beta finite => (to be proved) all primes integral => Hamburger => zeta. Not verified.
Interpretation (HEURISTIC): over F_q the formal (zeta-level) axioms leave a (g+1)-dim family dominated by fakes and the
geometric polarization excludes them; over Q the archimedean completion kills all commensurable fakes and (conjecturally)
all Beurling fakes, so the archimedean place is the unique zeta-level candidate for the role of Weil's polarization; the
only proven Q-positivity (Connes-Consani archimedean Weil positivity) is of this type. The wall = coupling it to primes.

## S9. Final answer summary (what was returned)
Single idea: formal-curve complement toy => Barrier III + periodicity delimitation + Beurling-Hamburger conjecture.
Key numbers to cite: F(5,5) golden fake (Re rho 0.79899, N_1=11, h=76, Weil bound ok k=1,2, fails k=3);
F(q,m*) Re rho_max = 1 - (log 2)/(3 log q) + o(1/log q) (verified q <= 10007); genus-1 effective <=> |a| <= q.
Connes corollary: F(5,5) window-4 Toeplitz min eig -8.22 with numerator in kernel; C-F nodes at +-0.6725pi, +-0.1768pi.
Self-score 3/10: correct, new as an explicit Euler-product control + ledger upgrade, but negative and elementary.
conjecture1_proved = False.
