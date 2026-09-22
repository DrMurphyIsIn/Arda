# The plain Gaussian face Theta and its heat monotonicity (2026-09-21)

Module: `telperion/examples/rvm_bridge/lean/E6Bridge17.lean` (namespace `RvMBridge17`, imports
E6Bridge14 and Mathlib's Gaussian Fourier file). Probe: `Probes/E6Bridge17_probe.lean`. Every
theorem prints `[propext, Classical.choice, Quot.sound]`; no `sorry`. Survey that motivated it:
`docs/research/FIXED_WIDTH_LENS_HEAT_2026-09-21.md`, lens 1'.

conjecture1_proved = False. Nothing here proves RH. The face gives RH a new equivalent shape and a
new instrument (width monotonicity); it does not remove the wall.

## 1. The object

    plainGauss c lam z := exp(-2 lam (z - c)^2)
    Theta c lam        := Re Sum_rho m(rho) plainGauss c lam (gamma_rho),   gamma_rho = (rho - 1/2)/i.

For a zero with gamma_rho - c = x + i y (x = Im rho - c, y = 1/2 - Re rho):

    |summand| = m e^{2 lam (y^2 - x^2)},    Re summand = m e^{2 lam (y^2 - x^2)} cos(4 lam x y).

The sum converges absolutely for every c and lam > 0 (`summable_plain_zeroSide`, from the strip
bound ‖G(z)‖(1 + |z|^2) <= e^{lam/2}(2c^2 + 13/4)/min(1, 2 lam) against the local zero count). Theta
is real (`zeroSide_plain_im`).

## 2. RH <-> Theta >= 0

`rh_iff_theta_positivity : RiemannHypothesis <-> forall c lam, 0 < lam -> 0 <= Theta c lam`.

Forward: under RH each summand is m e^{-2 lam (Im rho - c)^2} >= 0 (`theta_nonneg_of_rh`).

Converse (`exists_theta_neg_of_offline`): an off-line zero rho_0 gives a centre c such that for
every lam_0 there is lam >= lam_0 with Theta c lam < 0. This is E6Bridge7's argument with the
cosine bracket, with one new point. At the ordinate of an off-line zero (x = 0) the plain summand is
+m e^{2 lam y^2} > 0, the opposite sign from the F face, so the centre must avoid every window
ordinate: the generic centre now avoids the finitely many tying centres AND the finitely many
ordinates of window zeros (`badSet'`, `exists_generic_centre'`). Then the maximiser rho_1 of
phi_c = y^2 - x^2 on the window has x_1 != 0 and y_1 != 0, its pair term is
2 m_1 e^{2 lam M} cos(4 lam x_1 y_1), and lam = (pi + 2 pi k)/(4 x_1 y_1) with k chosen by sign
(`exists_lam_cos_neg_one`) makes the cosine exactly -1. The tail uses the plain majorant
(`pmajorant`, `ptail_bound`): e^{2 lam (M - eta)} times the window count plus the lam = 1 tail sum.

## 3. The heat identity (M)

Normalisation. e^{-2 lam' u^2} is the Gaussian convolution of e^{-2 lam u^2} with the kernel of
variance sigma^2 = 1/(4 lam') - 1/(4 lam) = (lam - lam')/(4 lam lam') (`heatVar`), up to the factor
sqrt(lam/lam'). In heat-semigroup time (variance 2s) this is s = (1/lam' - 1/lam)/8, as the survey
says.

Termwise (`plainGauss_heat`): for 0 < lam' < lam, every real c and every COMPLEX gamma,

    plainGauss c lam' gamma = sqrt(lam/lam') int heatKernel sigma^2 (c - c') plainGauss c' lam gamma dc'.

Proof: the integrand is a single Gaussian exponential in c' (`heat_integrand_eq`), Mathlib's
`integral_cexp_quadratic` evaluates it, and the prefactor (`hpre`) and exponent (`hexp`) identities
are field algebra with A = 1/(2 sigma^2) + 2 lam = 2 lam^2/(lam - lam'). No analytic continuation
argument is needed: the Gaussian integral with complex linear coefficient is available directly.

Summed (`theta_heat`): Theta c lam' = sqrt(lam/lam') int heatKernel sigma^2 (c - c') Theta c' lam dc'.
The interchange is `integral_tsum_of_summable_integral_norm`, which needs a countable index: the
nontrivial zeros are a countable union of finite windows (`nontrivialZeros_countable`, `NZ`), and
the zero sums are reindexed over that subtype. The majorant is
int ‖heatF rho‖ <= m e^{lam/2} sqrt(lam'/lam) e^{-2 lam' (Im rho - c)^2}
(`integral_norm_heatF_le`, from the real Gaussian heat step `real_gauss_heat`, itself the termwise
identity at a real point), summable by the strip bound at width lam'
(`summable_integral_norm_heatF`).

Corollary (`theta_pos_mono`): if Theta(., lam) >= 0 everywhere then Theta(., lam') >= 0 everywhere
for every 0 < lam' < lam (integral of a nonnegative function against a nonnegative kernel).

## 4. The constant Lambda_Theta

    ThetaFree lam  := forall c, 0 <= Theta c lam
    ThetaWidths    := {lam | 0 < lam and ThetaFree lam}     (Lambda_Theta := its supremum)

- `thetaFree_mono`: free widths are downward closed; `thetaWidths_Ioc_subset`: the free widths are
  an initial segment of (0, infinity).
- `rh_iff_thetaFree_all : RH <-> forall lam > 0, ThetaFree lam`;
  `rh_iff_thetaWidths_eq : RH <-> ThetaWidths = Ioi 0`. In words: RH <-> Lambda_Theta = infinity.
- `not_thetaFree_of_offline`: an off-line zero gives Lambda > 0 with not ThetaFree lam for EVERY
  lam >= Lambda (one negative width from section 2, then monotonicity kills all larger widths).
  `thetaWidths_bddAbove_of_offline`, and the dichotomy `rh_or_thetaWidths_bddAbove`:
  either RH, or the free widths are bounded.

This is a de Bruijn-Newman-type constant for the zero measure. Its status: the existential Lambda is
configuration-dependent (E6Bridge7-style constants); an explicit Lambda in the parameters
(y0, xmin, N, B, D) in the style of E6Bridge14 was NOT delivered for Theta (the E6Bridge14
mechanism uses the ordinate as centre, where the Theta summand is positive; the effective Theta
version needs an explicit off-ordinate centre and a phase, and is left named below).

## 5. What would certify a lower bound, and why it is a wall

> **Zero content, stated plainly (added 2026-09-21 after blind audit):** Lambda_Theta >= lam_cert asserts NOTHING detectable about zeros above the ladder at any reachable lam_cert. Theta is blind to a strip-edge zero until width about 3.6 (a strip-edge zero dips Theta by ~7e-4 at lam = 0.6 and ~0.024 at lam = 1 against an on-line background of order 2-3 at the ladder height), so a certified width is a clean restatement of what the ladder and the envelope already give, not new localisation.

Lambda_Theta >= lam_cert follows from ONE whole-line certificate Theta(., lam_cert) >= 0: the
ladder for |c| <= T - D, an envelope for |c| >= envelopeC(lam_cert), and the band between. Identity
(M) then gives every smaller width for free, which removes the sub-threshold band of the F face.
The certifiable width is capped by envelopeC^{-1}(T) with doubly exponential cost in lam (survey
section 1'). Pushing the certified lower bound to infinity is RH. That is a wall, not a crossing.

## 6. Not delivered (named)

- Effective Theta dominance: `not ThetaFree lam` for all lam >= an explicit expression in
  (y0, xmin, N, B, D). Needs the E6Bridge14 window estimate at a centre c = Im rho_0 + delta with
  0 < |delta| < |y_0| and a phase choice; the tail machinery (`pmajorant`) and the pair term are in
  place.
- The Theta versions of the region instruments (window on the line implies positivity with the
  envelope tail; the small-width regime via the explicit formula for the plain Gaussian test).
  The window direction is the same proof as E6Bridge12's with `re_plainGauss` on the line
  (each on-line window term is m e^{-2 lam x^2} > 0) and `ptail_bound`-style tails; the small-width
  regime needs the prime and archimedean sides of the plain Gaussian test, which are not
  formalised on this island for the Theta test.

## 7. Lemma ledger

- Face: `plainGauss`, `Theta`, `pterm`, `norm_plainGauss`, `norm_pterm`, `re_plainGauss`,
  `plainGauss_conj`, `plainGauss_ofReal`, `norm_plainGauss_mul_le`, `plainC`, `norm_pterm_le`,
  `summable_plain_zeroSide`, `zeroSide_plain_im`.
- Forward: `pterm_re_nonneg_of_rh`, `theta_nonneg_of_rh`.
- Converse: `exists_lam_cos_neg_one`, `badSet'`, `exists_generic_centre'`, `pmajorant`,
  `norm_pterm_le_pmajorant`, `pconstA`, `pconstB`, `tsum_pmajorant`, `ptail_bound`,
  `theta_le_pair_add_tail`, `exists_theta_neg_of_offline`, `rh_iff_theta_positivity`.
- Heat: `heatVar`, `heatKernel`, `heat_A_eq`, `heat_integrand_eq`, `plainGauss_heat`,
  `real_gauss_heat`, `heatF`, `integrable_heatF`, `integral_norm_heatF_le`,
  `summable_integral_norm_heatF`, `nontrivialZeros_countable`, `NZ`, `tsum_pterm_NZ`,
  `tsum_pterm_re_NZ`, `theta_heat`, `theta_pos_mono`.
- Constant: `ThetaFree`, `ThetaWidths`, `thetaFree_mono`, `thetaWidths_Ioc_subset`,
  `rh_iff_thetaFree_all`, `rh_iff_thetaWidths_eq`, `not_thetaFree_of_offline`,
  `thetaWidths_bddAbove_of_offline`, `rh_or_thetaWidths_bddAbove`.
