# Zeta Zero Localization (Stage 1)

On-line zero localization of the completed Riemann zeta function Lambda via
alternating-sign real enclosures and the intermediate value theorem.

conjecture1_proved = False.

## What is kernel-proven

The emitted theorems assert: given real enclosures of Lambda(1/2 + i*t) with
alternating signs, there exist N strictly increasing reals x_1 < ... < x_N in
[a, b] with completedRiemannZeta(1/2 + x_k*I) = 0.

These are genuine nontrivial zeros of the Riemann zeta function: Lambda's zeros
are exactly the nontrivial zeros of zeta (the completed function pi^(-s/2) *
Gamma(s/2) * zeta(s) has no other zeros).  So the theorems LOCATE nontrivial
zeta zeros ON the critical line Re s = 1/2.

The Lean kernel verifies:
- Lambda is real on the critical line (LambdaLineReal, Task 2 prelude): the
  functional equation and conjugation symmetry force Lambda(1/2 + t*I) to be
  real, so gLine(t) := Re(Lambda(1/2 + t*I)) equals Lambda(1/2 + t*I).
- gLine is continuous (completedRiemannZeta is differentiable away from {0,1};
  the line point 1/2 + t*I is never 0 nor 1).
- The intermediate value theorem (intermediate_value_Icc / intermediate_value_Icc')
  yields a root in each sign-change subinterval.
- The roots are strictly increasing (strict sign at each endpoint, back-to-back
  or separated subintervals bridged by norm_num gap lemmas).
- Each root gives a zero of Lambda, hence of zeta, on Re s = 1/2.

Axioms: {propext, Classical.choice, Quot.sound} -- no sorryAx, kernel-clean.

## Arb-certified non-kernel input boundary

The enclosure hypotheses -- e.g. "gLine 14 <= -(...)" -- are HYPOTHESES of each
theorem, not kernel-derived facts.  They record the Arb ball arithmetic result
(python-flint, outward-rounded rational endpoints via man_exp extraction) that
Lambda(1/2 + i*t) has a sign-definite real part at each sample point.

Arb ball arithmetic is internally certified (interval arithmetic with outward
rounding), but Lean does not independently verify the constant's value.  The
rational endpoints lo, hi are exact fractions.Fraction.  The theorem is valid
for any assignment of gLine satisfying the hypotheses -- the hypotheses are
the oracle boundary.

## Theorems

### lambda_zero_first_14_15 (case 0)

Two sample points: t = 14 (Re Lambda < 0), t = 15 (Re Lambda > 0).
One sign change: certifies 1 zero in [14, 15], bracketing the first
nontrivial zero at t ~ 14.1347.

### lambda_two_zeros_14_22 (case 1)

Three sample points: t = 14 (neg), t = 15 (pos), t = 22 (neg).
Two sign changes: certifies 2 zeros, bracketing the first zero (t ~ 14.1347)
in [14, 15] and the second zero (t ~ 21.022) in [15, 22].

### lambda_five_zeros_10_35 (case 2 -- MILESTONE)

51 half-integer sample points t in {10.0, 10.5, ..., 35.0} at 300-bit Arb
precision.  Five sign changes: certifies 5 strictly increasing zeros of Lambda
on the critical line in [10, 35], matching all 5 known nontrivial zeros:

    t ~ 14.1347, 21.0220, 25.0109, 30.4249, 32.9351

This is the first kernel-verified count of nontrivial zeta zeros on the critical
line in a real interval.

## What this does NOT prove

- It does NOT prove RH.  RH asserts ALL nontrivial zeros lie on Re s = 1/2.
  These theorems locate specific zeros ON the line; they say nothing about zeros
  off the line.
- It does NOT give an EXACT count of zeros in the interval (only a lower bound
  >= 5 from odd sign changes; the exact count requires the argument principle --
  Stage 2/3).
- conjecture1_proved = False.

## Stage structure

- Stage 1 (this file): lower bound N >= 5 via sign changes + IVT.
- Stage 2 (deferred): exact zero count via emitted argument-principle certificate.
- Stage 3 (deferred): RH-in-a-box (all zeros in a strip lie on Re s = 1/2).

## Usage

    # Write lean/XiLineZeros.lean (all three cases)
    python examples/zeta_zero_localization/generate.py

    # Drift check (byte-compare; no write)
    python examples/zeta_zero_localization/generate.py --check

    # Ad-hoc interval query (print certified N; no write)
    python examples/zeta_zero_localization/generate.py --a 10 --b 35 --n-samples 51 --prec 300

    # Build and verify
    cd examples/zeta_zero_localization/lean
    lake exe cache get
    lake build

## Files

    generate.py               -- interval driver + Lean emitter (certify -> emit -> write)
    lean/LambdaLineReal.lean  -- Task 2 prelude: Lambda is real on the critical line
    lean/XiLineZeros.lean     -- emitted theorems (DO NOT EDIT BY HAND)
    lean/lakefile.toml        -- lake project (Mathlib dependency)
    lean/lean-toolchain       -- pinned Lean version
