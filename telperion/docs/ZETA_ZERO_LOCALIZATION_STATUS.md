# Zeta Zero Localization -- Honest Status (Stage 1 MILESTONE)

conjecture1_proved = False.

## What is kernel-proven

The Lean theorem `XiLineZeros.lambda_five_zeros_10_35` (in
`examples/zeta_zero_localization/lean/XiLineZeros.lean`) states:

    Given 10 real enclosure hypotheses (the sign-definite Arb-certified bounds
    on gLine(t) at the 10 anchor sample points), there exist 5 strictly
    increasing reals x1 < x2 < x3 < x4 < x5 in [10, 35] with
    completedRiemannZeta(1/2 + x_k * I) = 0 for each k in 1..5.

This is kernel-verified by Lean 4 / Mathlib with axioms:
    {propext, Classical.choice, Quot.sound}
No sorryAx.  No placeholders.

Because Lambda's zeros are exactly the nontrivial zeros of the Riemann zeta
function (Lambda = pi^(-s/2) * Gamma(s/2) * zeta(s) has no other zeros), the
theorem LOCATES 5 nontrivial zeros of zeta on the critical line Re s = 1/2 in
the interval [10, 35].  The 5 located zeros match the 5 known nontrivial zeros:
    t ~ 14.1347, 21.0220, 25.0109, 30.4249, 32.9351.

This is the first kernel-verified on-line nontrivial-zero count for the
Riemann zeta function.

## Kernel-proven sub-lemmas (in LambdaLineReal.lean)

- `ZetaZeroLocalization.completedRiemannZeta₀_conj`: conjugation symmetry of the
  entire part Lambda_0.
- `ZetaZeroLocalization.completedRiemannZeta_conj`: conjugation symmetry of Lambda.
- `ZetaZeroLocalization.completedZeta_im_eq_zero`: Lambda(1/2 + t*I) is real for
  all t in R (proved via the functional equation Lambda(1-s) = Lambda(s) and the
  fact that conj(1/2 + t*I) = 1 - (1/2 + t*I)).

These three lemmas together establish the "real on the line" prelude that all
sign-change arguments consume.

## Arb-certified non-kernel input boundary

The 10 enclosure hypotheses in the MILESTONE theorem are the boundary between the
kernel-verified proof and the external oracle:

    henc8:  gLine 14     <= -(large negative rational)     -- Re Lambda < 0
    henc9:  (large positive rational) <= gLine (29/2)      -- Re Lambda > 0
    henc22: (large positive rational) <= gLine 21          -- Re Lambda > 0
    henc23: gLine (43/2) <= -(...)                         -- Re Lambda < 0
    henc30: gLine 25     <= -(...)                         -- Re Lambda < 0
    henc31: (...)        <= gLine (51/2)                   -- Re Lambda > 0
    henc40: (...)        <= gLine 30                       -- Re Lambda > 0
    henc41: gLine (61/2) <= -(...)                         -- Re Lambda < 0
    henc45: gLine (65/2) <= -(...)                         -- Re Lambda < 0
    henc46: (...)        <= gLine 33                       -- Re Lambda > 0

These are produced by `telperion.arb_enclosure.enclose_lambda` at 300-bit Arb
precision.  The rational endpoints are exact fractions.Fraction derived via
man_exp outward-rounded dyadic arithmetic from the Arb ball's midpoint and
radius.  Arb ball arithmetic is internally certified (interval arithmetic with
outward rounding), but Lean does not independently verify the constant's value.

The theorem is valid for ANY assignment of the function gLine satisfying the
hypotheses.  The enclosure hypotheses are the oracle boundary -- a user who
independently verifies them (by any means) gets the kernel-certified zero-existence
conclusion unconditionally from the Lean proof.

## What this does NOT prove

- It does NOT prove the Riemann Hypothesis.  RH asserts all nontrivial zeros lie
  on Re s = 1/2.  This theorem locates specific zeros ON the line from certified
  enclosures; it says nothing about zeros that might lie off the line.
  conjecture1_proved = False.

- It does NOT give an exact zero count in [10, 35].  The lower bound N >= 5 comes
  from odd sign changes (each sign change certifies at least one zero via IVT).
  The exact count requires computing the argument principle integral -- Stage 2.

- It does NOT prove that these are ALL the nontrivial zeros in [10, 35].  There
  could be additional zeros between the sampled sign-change subintervals (e.g. a
  pair of zeros that do not produce a net sign change with 0.5 spacing).

## Stage roadmap

- Stage 1 (COMPLETE): lower bound N >= 5 via sign changes + IVT.  This file.
- Stage 2B (COMPLETE, Task 7): the LOCAL Blaschke split of `zeta'/zeta` over the
  box B = [2/5, 3/5] x [10, 35] is now KERNEL-DERIVED (see below).
- Stage 2 (deferred): exact zero count via argument-principle emitter (pending
  the merged argument_principle emitter probe).
- Stage 3 (deferred): RH-in-a-box -- all zeros in a strip lie on Re s = 1/2
  (requires a complete zero-free region argument off the line; the polylog
  zero-free region in ZeroFreeBridge is the current frontier).

## Stage 2B: kernel-derived local Blaschke split (Task 7)

`BlaschkeBox.zeta_blaschke_split_box`
(`examples/zeta_zero_localization/lean/BlaschkeBox.lean`) DERIVES, in kernel, the
local principal-part split of `logDeriv riemannZeta` over the capstone box.  On
the open ball `U = ball(cB, 13)` (center `cB = 1/2 + (45/2) i`, radius 13) that
contains the closed box `B = [2/5, 3/5] x [10, 35]` and excludes zeta's only pole
`s = 1`, there is a finite set `s` of zeta zeros in `U`, the divisor `d`, and an
error `E` such that:

    at every z in U with zeta z != 0,
      logDeriv zeta z = (sum_{rho in s} (d rho)/(z - rho)) + E z,
    and E is HOLOMORPHIC on B  (DifferentiableOn C E B).

Mechanism: zeta is analytic on `{1}^c` (`analyticOn_riemannZeta`), hence
meromorphic on `U`; `divisor_ball_support_finite` (compact `closedBall`) gives a
finite divisor support; `MeromorphicOn.extract_zeros_poles` yields an analytic,
zero-free remainder `g` on `U` with `zeta =(codiscrete) (prod (.-u)^(d u)) * g`;
an in-file identity-principle transfer (`logDeriv_congr_of_codiscrete`, a
reproduction of the `zero_free_bridge/DlvpTransfer` germ lemmas) moves the
codiscrete factorization to a POINTWISE `logDeriv` identity on `U`; the finite
product's `logDeriv` is the residue sum, and `E := logDeriv g` is holomorphic on
`U` (hence on `B`) because `g` is analytic and non-vanishing.

Axioms: {propext, Classical.choice, Quot.sound}.  No sorryAx.

This DISCHARGES Task 5's H2 (E-holomorphy), previously a hypothesis.
`BoxArgPrincipleZeta.box_arg_principle_zeta`
(`examples/zeta_zero_localization/lean/BoxArgPrincipleZeta.lean`) instantiates the
capstone with the derived `E, s, d` and the kernel E-holomorphy; the four
per-segment boundary split identities (H1) are DERIVED from the kernel split, so
the only residual boundary input is that the four edges carry no zeta zero
(`hnz_*`) -- the SAME Arb-enclosure trust boundary as the numeric zero
enclosures, carried as named documented hypotheses (NOT faked).  Strict
interiority (H3), routine boundary integrability, and the winding value (H4, from
WindingCount / Task 9) remain the other inputs.

conjecture1_proved = False.

## Proof mechanism

For each sign-change subinterval [t_i, t_k] (t_i < t_k, gLine(t_i) and
gLine(t_k) have opposite signs):

1. The enclosure hypothesis pins the sign at each endpoint (hi < 0 for a
   negative box, lo > 0 for a positive box).
2. gLine is continuous (completedRiemannZeta is differentiable away from {0,1};
   1/2 + t*I is never 0 nor 1; continuity of Re follows).
3. The intermediate value theorem (intermediate_value_Icc or
   intermediate_value_Icc') yields a root r in [t_i, t_k].
4. The root is strictly interior: r = t_i would make gLine(r) = 0 at an endpoint
   where gLine is nonzero (contradiction); same for r = t_k.
5. Consecutive roots are strictly increasing: r_{m+1} < t_{k_m} <= t_{i_next} <
   r_{m+2} (the gap t_{k_m} <= t_{i_next} is a rational literal comparison
   discharged by norm_num).  The subintervals may be adjacent (t_{k_m} =
   t_{i_next}) or separated by straddling samples (t_{k_m} < t_{i_next}); the
   <= covers both, so distinctness holds either way.
6. lambda_eq_gLine (proved from completedZeta_im_eq_zero) rewrites
   completedRiemannZeta(1/2 + r*I) = gLine(r) promoted to C; gLine(r) = 0 gives
   the zero.

## Files

    examples/zeta_zero_localization/generate.py        -- interval driver + emitter
    examples/zeta_zero_localization/lean/LambdaLineReal.lean  -- Task 2 prelude
    examples/zeta_zero_localization/lean/XiLineZeros.lean     -- emitted theorems
    examples/zeta_zero_localization/lean/BlaschkeBox.lean     -- Task 7: kernel-derived local Blaschke split
    examples/zeta_zero_localization/lean/BoxArgPrincipleZeta.lean -- Task 7: capstone wiring (H1+H2 discharged)
    examples/zeta_zero_localization/README.md          -- usage + cert boundary doc
    src/telperion/arb_enclosure.py                     -- Task 1: enclose_lambda
    src/telperion/emit_xi_line_zeros.py                -- sign_change_count + emitter
    tests/test_zeroloc_end_to_end.py                   -- TDD gate: N >= 5 on [10,35]
    tests/test_xi_line_zeros.py                        -- emitter unit tests
