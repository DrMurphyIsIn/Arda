# Strictness-iff for the achievable homogeneous master inequality

Companion to `homog_master_achievable` (PR #38): the STRICT bound
`GS k mu < T` for every achievable `(k, mu)` EXCEPT the arm tip `(1, 1)`,
and the equality characterisation `GS k mu = T <-> (k = 1 and mu = 1)`.

## Lean artifacts (kernel-clean, axioms = [propext, Classical.choice, Quot.sound])

- `lean/HomogStrict.lean` — strict Bernstein interval certs `0 < P(mu)`
  (`certA_small_mu_strict`, `certB_mid_strict`, `certC1_k1_strict`,
  `certC2_k2_strict`, `certC3_kge3_strict`), one per region A/B/C1/C2/C3.
- `lean/HomogStrictAssembled.lean` — strict bridges, strict region lemmas
  `GS_regionA_lt/B_lt/C_lt`, the arm-line strictness `armGS_lt_T` (k >= 2),
  the main `GS_lt_T_of_not_arm`, and the iff `GS_eq_T_iff_arm`.

## Mechanism

Each region cert `P` is `(T - GS)`-shaped and decomposes in the Bernstein
basis `P = sum_i c_i (mu-lo)^i (hi-mu)^(d-i)` with EVERY `c_i > 0`
(see `bernstein_coeffs.py`). Strictness on the whole closed interval:
- `mu < hi`: the leading term `c_0 (hi-mu)^d > 0`;
- `mu = hi`: the trailing term `c_d (mu-lo)^d > 0` (since `lo < hi`).
The nonneg `t_i` haves and the `ring` identity are verbatim from the
non-strict certs; only the conclusion is strengthened, so the certs stay
kernel-clean.

The structural `base`/`Bcap` bounds stay non-strict and compose with the
strict bridge via `lt_of_le_of_lt`. On the arm line `mu = 1`, `k >= 2` gives
`armGS k <= armGS 2 < T` where `armGS 2 = (16/9)^11 (64/621)^2 < (5/3)^11 (64/621) = T`.

## Margin scan (`margin_scan.py`)

Over the achievable region `0 < mu <= 1/2`, the relative margin `(T - GS)/T`
is bounded away from zero everywhere (min ~ 0.128 at k=1, mu=1/2); the master
inequality is saturated ONLY at the arm tip `(k, mu) = (1, 1)` (outside this
open region). Each cert polynomial `P` is strictly positive on its entire
closed sub-interval (min value >= 7.06), confirming the strict certs exist.

`conjecture1_proved = False`. This closes the STRICTNESS half of the
HOMOGENEOUS face over achievable `mu`; the heterogeneous -> homogeneous
reduction remains open.
