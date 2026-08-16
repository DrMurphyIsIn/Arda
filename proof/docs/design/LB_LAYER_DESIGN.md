# The (L)/(B) normalization layer — design (2026-08-15, gate opened post-capstone)

Ground truth surveyed; `legs.py` certificates re-validated GREEN this session.

## The decisive structural finding (inherited from the P2 stratification addendum)

(L) and (B) are NOT rewrite surgeries in the live architecture — they are
CLASSIFICATION facts: rate-maximality forces cherry legs and cherry-arm branches.
Anything outside the certified family (legs of length ≠ 2, non-cherry-arm branches,
under-armed hubs) lives in the rate < rho_B stratum, which the stratum-(i) rate
bound kills wholesale (`pi(T) <= (4/3) rhoB^n` with strict rate deficit).  So the
Lean content of this layer is the RATE-CLASSIFICATION theorem, not tree surgery —
a dramatic scope reduction, and the fixed-n bookkeeping problem never arises.

## The Lean deliverable: `R47Legs.lean` (one certificate file)

Port `legs.py`'s cherries-optimal theorem — all exact-rational, Polya-style,
matching the P4 pipeline exactly:

1. `phiL : ℕ → ℚ` — the leg matching factor (phi 1 = 1, phi 2 = 3/2,
   phi (l+2) = phi (l+1) + phi l / 4) with positivity;
2. `phiL_le_beta_pow` — the envelope `phiL l ≤ (483/400)^l` for `l ≥ 3`
   (two base cases by norm_num + the induction step from `beta^2 ≥ beta + 1/4`);
3. `ell_one_rate` — `F_1(1+c)^11 < (621/64)^(1+c)`: the c ≤ 3 exact checks +
   the `(1+2c)/(1+c) < 2` tail with `2^11 < (621/64)^(1+c)` for `c ≥ 4`;
4. `tail_rate` — THE one bignum: `483^253 * 3^11 * 64^23 < 400^253 * 2^11 * 621^23`
   (clear denominators of `beta^253 (3/2)^11 < (621/64)^23`; norm_num kernel bignum,
   same class as the s-tail exponent-317 crux that is already green);
5. `finite_sweep` — the c*l ≤ 21 grid (3 ≤ l ≤ 21, finitely many (l, c)):
   `F_l(1+c)^11 < (621/64)^(1+c*l)` — GENERATED norm_num table (extend
   gen_r47cert_cells.py with a legs emitter; the Python file enumerates the exact
   pairs);
6. the assembled statement `legs_rate : ∀ l ≠ 2, every l-legged star family's
   growth rate < rho_B` in the gadget formulation legs.py proves — stated against
   `rhoB` from the green ExactCruxes constants.

## Honest scope (verbatim into the file header)

Gadget-level (growth-rate) statement — ONE of the necessary conditions.  Its
integration into the full reduction happens at the R7' assembly through the
stratum classification + the rate port; the classification seam ("rate-maximal
families have cherry arms", connecting gadget rates to family membership) is
named at assembly time.  conjecture1_proved=False.

## Method

Exactly the campaign method: the Python certificates are already exact; emit the
finite sweep programmatically; validate any restated inequality in Fractions
before Lean; one CI-gated file; trace-diagnose on red.
