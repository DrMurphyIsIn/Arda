# P2b design hand-off: the certified merge layer (2026-08-14)

For the R47 campaign's P2b (Step relation + measure).  Everything below is proved in exact
arithmetic + symbolic Polya certificates in four self-verifying modules on this branch
(`kelmans_mixed_load.py`, `kelmans_vertex_budget.py`, `kelmans_env_rules.py`,
`kelmans_unified_merge.py` -- run_all() green in each).  The punchline: **build the Step relation's
hub-merge constructor as the UNIFIED TOPPED-UP MERGE below, and the stuck-state problem, the
vertex-budget comparison, and mid-rewrite rebalancing all disappear.**

## The one merge rule

**TOPPED-UP MERGE** (replaces (H) and the hub-directed part of (K)): for a hubward adjacent hub
pair `a` (load `cA`, degree `da`) >= `b` (load `cb`, degree `db`), where `b` carries at least
`k = 5 - cb` load-5 arms: downgrade `k` of `b`'s arms to load 4, raise `b`'s load to 5, move all
of `b`'s other neighbours to `a`, leave `b` as a **load-5 leaf of `a`** (a canonical arm).
Anti-hubward pairs: reverse the roles.

* Donor load 5 (`k = 0`): the plain Kelmans merge.
* Donor load 0..4: the borrows are FUSED into the move (the borrow alone is NOT monotone --
  tends to ~0.9913 for giant hubs -- and the unassisted de-loaded merge strictly DECREASES pi;
  only the fusion is uniformly monotone).
* **No debris**: the residue is `k` load-4 arms + one new load-5 arm -- all inside the balanced
  {4,5}-arm family.  (An earlier borrow-1 design left a load-1 leaf; superseded.)

## What is certified (theorem-grade, all N)

`kelmans_unified_merge.certify_unified_table`: for every `(cA, cb)` in {0..5} x {0..5} -- 36
cells -- the move is pi-non-decreasing (strict on the two-hub family) in EVERY environment whose
OTHER neighbours of `a` and `b` satisfy `3*deg + 4*load >= 16` (activity cap `z <= 3/16`).
Proof shape per cell: the exact bilinear identity

    pi(T'') - pi(T) = Penv * FQ * FSr * D(sigma_Q, sigma_r)

(environment enters via two scalars; identity verified exactly on 250 random loaded trees), box
corners of `D` after the shifts `db = (6-cb)+v, da = db+u` (topped-up) / `db = 2+v` with the
one-arm floor `sigma_S >= 3/23` (direct), all-nonnegative numerators over positive denominators.

Cap ladder: 36/36 at 3/23, 3/19, 1/6, 3/17, **3/16**; first failure (1,5) at 1/5.  Cap 3/16
covers: arms of load >= 4, hub neighbours with >= 5 arms (any load), loaded hubs of degree >= 4.

## What this changes in the campaign design

1. **No stuck states.**  Every adjacent hub pair admits a monotone merge (donor loaded -> k=0;
   under-loaded -> topped-up).  The tex's rem:import strictness story and the
   "A_mono_K-BOUNDARY (n<=240)" named hypothesis are REPLACED by these certificates on the
   canonical family.
2. **No mid-rewrite rebalancing requirement.**  The residue (load-4 arms) stays inside the cap,
   so consecutive merges compose without normalization in between.
3. **The measure**: each merge reduces hub count by exactly 1 (mu's first coordinate in the
   campaign's lex measure); termination for the merge layer is immediate.
4. **HubState encoding**: states = (hub tree, per-hub load 0..5, per-hub multiset of arm loads
   {4,5}).  The merge = one arithmetic constructor; no debris variants needed.
5. **A_mono_H / A_mono_K discharge (P4/P5)**: the certificates are LemmaA-style rational
   polynomial inequalities in 2 shifted variables per cell -- 36 cells x 4 corners, each a
   candidate for `nlinarith`/`polyrith` with the coefficient lists as hints.  The exact identity
   itself (bilinear D) mirrors the psi_close bilinear form the tex already cites.

## Honest boundary (what the merge layer does NOT cover)

* **Small structures**: donors with fewer than `5-cb` arms; environment neighbours with
  `3*deg + 4*load < 16` (arms of load <= 3, load-0 hubs with <= 4 arms, bare/low-load leaves).
  These are the (L)/(B) normalization layer's objects: normalize legs/arms FIRST (R2: legs ->
  cherries -> arms), then merge.  The needed ordering: (L)/(B) before topped-up merges touch a
  region.  What (L)/(B) need at fixed n is the branch-replacement bookkeeping -- the campaign's
  named item (b), still open, next natural target.
* **Strictness toward the sink** is inherited from the strict two-hub certificates (positive
  constant terms) on the exact family; the environment versions are non-strict (>=) -- enough for
  A-monotonicity, with uniqueness via the strict two-hub core (as in rem:import).
* The independent cross-check: even if a de-loaded donor were left unmerged, the SAME-n
  single-hub balanced template strictly dominates any stuck multi-hub configuration
  (`kelmans_vertex_budget` Theorem 1, 2-hub proven + 3/4-hub swept) -- the belt to the
  braces above.

## Suggested Lean porting order (when P4 arrives)

1. `D_unified` as a rational function + the exact identity for the two-hub family (pure ring).
2. The 36x4 corner inequalities at cap 3/16 (nlinarith with coefficient hints; the certificates
   provide exact all-nonneg witnesses, so each goal is a sum of explicitly nonneg monomials --
   `positivity` may close many directly).
3. The box/marginal-bound lemma (sigma bounds; mirrors psi_close piece (2)).
4. The environment identity (Penv factorization) -- the only structural induction.

conjecture1_proved = False throughout; nothing here claims the full Conjecture 1.
