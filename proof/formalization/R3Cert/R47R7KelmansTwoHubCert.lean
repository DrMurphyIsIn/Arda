/-
  R47 / R7 -- KELMANS TWO-HUB VERTEX-BUDGET domination, machine-checked as an all-nonnegative
  Positivstellensatz certificate.  This is the load-bearing finite brick behind `Hdom`'s hardest
  node: the multi-hub-STUCK obstruction (a de-loaded second hub the ordered merge cannot dissolve).

  CONTEXT (proof/verification/kelmans_vertex_budget.py, `certify_two_hub_theorem`).  At matched
  vertex count `n = 2 + 2·cA + 11·(pA+pB)`, the stuck two-hub configuration
      S2(pA,pB,cA) = hub A (receiver load cA, pA five-cherry arms) -- hub B (load 0, pB five-cherry arms)
  is STRICTLY DOMINATED (in `pi = per(L)/∏deg`) by the same-n single-hub downgrade template
      T = de-loaded hub, K+1 = pA+pB+1 arms, (5-cA) arms at load 4 and the rest at load 5.
  Both `pi` values have exact closed forms (`pi_two_hub_closed`, `pi_template_closed`), with the
  common arm factor `V = F(1,5) = 621/64 = rho_B^11`; `W = F(1,4) = 513/80`, `z15 = 3/23`, `z14 = 3/19`.

  THE CERTIFICATE.  Divide out the common `V^K` and substitute `pA = 1 + x`, `pB = 1 + y`
  (`x, y ≥ 0` encodes `pA, pB ≥ 1`).  The gap `pi(T)/V^K − pi(S2)/V^K`, cleared to a single
  fraction, has a strictly positive denominator, so its sign is that of the numerator.  For each
  receiver load `cA ∈ {0,…,5}` the (integer-cleared) numerator is a polynomial in `x, y` with
  ALL-NONNEGATIVE coefficients and a STRICTLY POSITIVE constant term -- hence strictly positive on
  the nonnegative orthant.  That is a Positivstellensatz witness for `pi(T) > pi(S2)` at every
  `pA, pB ≥ 1`: the single hub beats every stuck two-hub configuration, uniformly in size.

  The polynomials below are emitted verbatim from the sympy certificate (exact rational arithmetic,
  denominators cleared by the per-cell lcm); each `nlinarith` discharge only needs the monomial
  nonnegativities `x, y, xy, x², y², x²y, xy² ≥ 0`, so the kernel check is cheap and robust.

  HONEST SCOPE.  This settles the TWO-HUB core of the vertex-budget domination for every arm count
  and receiver load -- the base case that (with the assisted-merge rule) dissolves two-hub
  stuckness.  It does NOT prove `Hdom`: the m-hub (m ≥ 3) general case remains open (reframed as the
  environment version of the local merge rules; 3-/4-hub probes pass with margins growing in m, but
  that is evidence, not proof).  It does NOT prove Conjecture 1.  Self-contained: `import Mathlib`
  only; imported by nothing (a self-building leaf brick, per the lakefile glob).
  `conjecture1_proved = False`.
-/
import Mathlib

namespace R3Cert.Step3

/-- **Two-hub vertex-budget domination, receiver load `cA = 0`.**  The integer-cleared gap
    numerator `pi(T)/V^K − pi(S2)/V^K` (over a positive denominator) at `cA = 0`, in the shifted
    arm counts `x = pA−1`, `y = pB−1`.  All coefficients nonnegative, constant `> 0`, so it is
    strictly positive for `x, y ≥ 0` -- the single-hub template strictly dominates the stuck
    two-hub configuration for every `pA, pB ≥ 1`. -/
theorem two_hub_gap_pos_c0 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (0:ℝ) < 2108756468*x*y*y + 2108756468*x*x*y + 7183219186*y*y + 24070628096*x*y
      + 7183219186*x*x + 28147580320*y + 28147580320*x + 13037927646 := by
  nlinarith [hx, hy, mul_nonneg hx hy, mul_nonneg hx hx, mul_nonneg hy hy,
    mul_nonneg hx (mul_nonneg hy hy), mul_nonneg (mul_nonneg hx hx) hy]

/-- Two-hub vertex-budget domination, receiver load `cA = 1`. -/
theorem two_hub_gap_pos_c1 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (0:ℝ) < 61375236*x*y*y + 61375236*x*x*y + 141144458*y*y + 596501000*x*y
      + 200116722*x*x + 631420876*y + 737223556*x + 410620170 := by
  nlinarith [hx, hy, mul_nonneg hx hy, mul_nonneg hx hx, mul_nonneg hy hy,
    mul_nonneg hx (mul_nonneg hy hy), mul_nonneg (mul_nonneg hx hx) hy]

/-- Two-hub vertex-budget domination, receiver load `cA = 2`. -/
theorem two_hub_gap_pos_c2 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (0:ℝ) < 1768572*x*y*y + 1768572*x*x*y + 2813538*y*y + 15078216*x*y
      + 5555394*x*x + 14558712*y + 19977144*x + 12740022 := by
  nlinarith [hx, hy, mul_nonneg hx hy, mul_nonneg hx hx, mul_nonneg hy hy,
    mul_nonneg hx (mul_nonneg hy hy), mul_nonneg (mul_nonneg hx hx) hy]

/-- Two-hub vertex-budget domination, receiver load `cA = 3`. -/
theorem two_hub_gap_pos_c3 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (0:ℝ) < 50544*x*y*y + 50544*x*x*y + 59670*y*y + 389664*x*y
      + 153738*x*x + 349920*y + 558252*x + 389610 := by
  nlinarith [hx, hy, mul_nonneg hx hy, mul_nonneg hx hx, mul_nonneg hy hy,
    mul_nonneg hx (mul_nonneg hy hy), mul_nonneg (mul_nonneg hx hx) hy]

/-- Two-hub vertex-budget domination, receiver load `cA = 4`. -/
theorem two_hub_gap_pos_c4 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (0:ℝ) < 32994*x*y*y + 32994*x*x*y + 32994*y*y + 237006*x*y
      + 97578*x*x + 204012*y + 367956*x + 270378 := by
  nlinarith [hx, hy, mul_nonneg hx hy, mul_nonneg hx hx, mul_nonneg hy hy,
    mul_nonneg hx (mul_nonneg hy hy), mul_nonneg (mul_nonneg hx hx) hy]

/-- Two-hub vertex-budget domination, receiver load `cA = 5` (degree 2: the fully-loaded receiver
    parks no arm downgrades, so the `x²`/`y²`/cubic monomials drop out). -/
theorem two_hub_gap_pos_c5 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (0:ℝ) < 21411*x*y + 21411*y + 61776*x + 61776 := by
  nlinarith [hx, hy, mul_nonneg hx hy]

end R3Cert.Step3
