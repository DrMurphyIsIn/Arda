# G1 kernel -> Lean: port design (2026-08-14)

Ready-to-paste statement shapes for formalizing the G1 rational-certificate layer
(g1_floor_certificates.py + g1_endpoint_certificates.py) in R3Cert, following the campaign's
established idiom (exact-rational corners as in `PotentialE2Small.lean`, integer identities as
in `LemmaA.lean`, log-algebra as in `Plainify.lean`).  The headline: EVERY analytic step of the
Python kernel reduces to two Mathlib lemmas plus rational arithmetic -- no derivatives, no
interval libraries, no bisection dumps.

## The two analytic workhorses (both in Mathlib)

1. `Real.add_one_le_exp : x + 1 <= Real.exp x` -- gives the exp lower bounds and, applied to
   `log`, the bound `Real.log x <= x - 1` (`Real.log_le_sub_one_of_pos`).
2. `Real.log_le_sub_one_of_pos : 0 < x -> Real.log x <= x - 1` -- THIS IS the anchored
   concavity bound: for `u >= u0 > -1`,
       log (1+u) - log (1+u0) = log ((1+u)/(1+u0)) <= (1+u)/(1+u0) - 1 = (u-u0)/(1+u0).
   One rewrite (`Real.log_div`) + one application.  The Python `log1p_upper` is exactly this.

For exp UPPER bounds (needed only for the three constants): the finite Taylor sum with
remainder.  Mathlib's `Real.exp_bound` covers |x| <= 1; for x = 11*L_lo ~ 2.27 use
`Real.exp_add` to split x = x/4 + x/4 + x/4 + x/4 with each piece <= 1 (or the
`Real.exp_one_lt_d9`-style numeric extension if available in the pinned Mathlib).  These are
THREE one-time lemmas, then never touched again.

## (A) the verified constants (three lemmas)

```lean
-- rhoB, L, T0 already exist in Reach.lean / Plainify.lean contexts; state the brackets:
theorem L_bracket : (206586 : ℝ)/10^6 <= Real.log (621/64) / 11
    ∧ Real.log (621/64) / 11 <= 206587/10^6 := by
  constructor
  · -- <=> exp (11 * lo) <= 621/64: Taylor upper via exp_add-split + norm_num
  · -- <=> 621/64 <= exp (11 * hi): Real.add_one_le_exp-chain or Taylor lower + norm_num

theorem T0_bracket : ((1 : ℝ) + 2294736/10^7)^11 <= 621/64
    ∧ (621 : ℝ)/64 <= (1 + 2294737/10^7)^11 := by
  norm_num   -- PURE RATIONAL: this one is literally norm_num on integers

theorem log32_bracket : (405465 : ℝ)/10^6 <= Real.log (3/2)
    ∧ Real.log (3/2) <= 405466/10^6 := ...  -- same shape as L_bracket
```
`T0_bracket` is free.  The other two are the only places exp-Taylor appears.

## (B) the slack lower bound and the DISCRETE MONOTONICITY reduction

Do NOT port the Python bisection trees.  In Lean, replace calculus/bisection with the
algebraic two-point estimate (all classes, one lemma shape):

```lean
-- for y <= y' (equal-children cavity), the slack difference is bounded algebraically:
-- slack y' - slack y >= m*(y'-y) * (11/50 - 1/(k+1+S(y)))     [on y > T0 pieces]
-- proof: log((1+u')/(1+u)) <= (u'-u)/(1+u) = m*(y'-y)/(k+1+S(y))   [log_le_sub_one]
--        and the hinge terms are linear.  field_simp; ring; positivity.
theorem slack_two_point (a nl m : ℕ) (y y' : ℝ) (h : y <= y') ... :
    slack a nl m y' - slack a nl m y >=
      m * (y' - y) * (11/50 - 1/(k+1+S a nl m y)) - hingeCorrection ... := ...
```

Consequences (mirroring the Python collapse lemma, now fully algebraic):
* `11/50 - cav >= 0` is a RATIONAL side condition (`norm_num` per class);
* for m >= 4: `cav <= 1/(m+1) <= 1/5 < T0_lo` (norm_num) kills the hinge, and the two-point
  estimate gives monotone-up on `y > T0` and monotone-down on `y <= T0` -- so each class floor
  is `slack` evaluated ON THE T0 BRACKET, a single rational-plus-log1p_upper computation;
* m in {1,2,3}: at most 4 monotone pieces (split at the two rationally-bracketed hinge
  points and at the `cav = 11/50` crossing, which is rational); each piece needs ONE
  endpoint evaluation.  Total per class: <= 5 point evaluations, each of the shape
      p * L_lo - a * log32_hi - log1pUpper u_hi - (11/50) * D_hi >= floor
  which after clearing `log1pUpper` (an anchored rational + one log_le_sub_one) is
  `norm_num`-closable.

## (C) the endpoint theorems

* HEAVY TOP: a finite conjunction over (cT, defect, j) of statements
  `forall dt >= dt_min, G dt < target`, where `G` is rational in `dt` except `F(dt,cT)`
  (rational!) -- so each is: finitely many norm_num checks (dt < 400) + a tail lemma
  `dt >= 400 -> G dt <= G_tail` with G_tail rational (F antitone in dt: an algebraic
  fraction comparison; z_t*sigma fractional-linear: same).  No analysis at all.
* MIXED LAYER: the convex-minorant validity is a finite list of rational piece
  comparisons (`norm_num`); Jensen for a piecewise-linear convex function over a finite
  sum is `inner_le_nnorm...` no -- use `ConvexOn.smul_le_sum` (Mathlib: Jensen for convex
  functions, `ConvexOn.inner_smul_le_norm_mul_norm` is wrong -- the right one is
  `ConvexOn.sum_le` / `ConvexOn.smul_le_sum` family; for a 3-piece linear function it may
  be easier to prove the pointwise bound `sum c_i >= m * chat (S/m)` directly by
  induction using chat's convexity as three slope inequalities).  Then the m in 2..7
  cases use (B)'s two-point machinery in S, and the m >= 8 uniform lemma is two
  norm_num checks + one log_le_sub_one application.

## (D) port order and effort

1. `G1Kernel.lean`: the three constant brackets + `log1pUpper` (one lemma) -- 1 CI file.
2. `G1Floors.lean`: the two-point estimate + the collapse reduction + the per-class floor
   conjunctions -- 1-2 CI files (the per-class evaluations are mechanical norm_num).
3. `G1Endpoints.lean`: heavy-top finite conjunction + tail; minorant + Jensen + uniform
   lemma -- 1-2 CI files.

Everything feeds the same consumers as the Python: the dichotomy budgets and the amortized
hub bound.  After (1)-(3), the ONLY non-Lean rigor left in the entire arc is the exact
finite rational sweeps (442,800-case etc.) -- which are `decide`-shaped but large; recommend
keeping those as Python exact certificates cited by the paper, or porting via `native_decide`
-- which the program has so far (correctly) banned; a middle path is a Lean-checked sampling
of the sweep plus the Python artifact, stated honestly.

conjecture1_proved = False; this document changes nothing about status, only maps the path.
