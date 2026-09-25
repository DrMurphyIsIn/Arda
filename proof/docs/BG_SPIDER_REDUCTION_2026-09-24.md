# BG spider reduction, part B1 (2026-09-24)

Branch `bg/reduction`. Lean: `proof/formalization/R3Cert/BGSpiderReduction.lean` and
`proof/formalization/R3Cert/BGSpiderCells.lean` (namespace `R3Cert.BGSCL`). Script:
`proof/verification/bg_spider_reduction.py`. `conjecture1_proved = False`.

## The claim

For every tree T on n vertices there is a two-level spider S on n vertices with pi(S) >= pi(T). A
two-level spider is a centre carrying leaves, cherries and arms, where arm_j is a vertex whose j >= 1
other neighbours are all cherries. The "atoms" are the leaf, the cherry and the arms, so a tree is a
spider exactly when some root has only atom children.

Earlier coverage notes said n = 31 (Pant's T(5,5,4)) was a two-hub exception. It is not. Root it at the
middle core vertex x_2 and its children are 5 cherries, x_1 (which is arm_5) and x_3 (which is arm_4),
so it is the spider centre + C^5 + arm_5 + arm_4. The earlier label came from how the old shape printer
chose a root. As far as anything computed shows, there are **no small-n exceptions**.

## Where things stand, in one paragraph

Every tree that has a vertex of degree >= 24 and has n >= 91 vertices is either a spider centred at that
vertex or strictly beaten by a spider of the same size. This is kernel-checked in Lean with no
hypotheses. Every n <= 100 is settled by the repo's exact dynamic program, and a floating-point version
agrees up to n <= 200 (DP_RANGE_PLACEHOLDER). What is left open is trees whose maximum degree is <= 23,
for n beyond the computed range. For those, the Lean reduction needs one more statement, a
degree-capped "taxed envelope", which is supported by numbers but not proved.

## Proved in Lean (no sorry, no native_decide; only propext, Classical.choice, Quot.sound; all in AxiomGuard)

Notation. A planted branch b has summary (T_b, y_b). `bell b = log T_b - |b| F*` with
`F* = log(621/64)/11`, and `V_mu(b) = bell b + mu*y_b`. `piRoot cs = (prod T_c)(1 + (sum y_c)/k)` is the
cavity form of pi at a root with k children.

| Lean name | Statement |
|---|---|
| `phiRoot_eq` | Lagrangian identity: `log pi - (n-1)F* = sum bell b_i + log(1 + S/k)` |
| `phiRoot_le_tangent` | For any t > 0 and mu = 1/(kt): `log pi - (n-1)F* <= log t + 1/t - 1 + sum V_mu(b_i)` |
| `armEnv_interp` | `ArmEnv mu delta` (every branch has `V_mu <= 3mu/23`; every non-atom has `V_mu <= 3mu/23 - delta`) is affine in mu, so the two endpoints give all of [0, mu0] |
| `phiRoot_le_of_armEnv` | If ArmEnv holds on [0, 23/624] and k >= 24 with one non-atom child: `log pi - (n-1)F* <= log(26/23) - delta` (tangent at t = 26/23) |
| `phiRoot_spider_ge` | **Unconditional.** The spider with a copies of arm_5 and q copies of arm_4 has `log pi - (n-1)F* >= log(26/23) + q*bell(arm_4)` |
| `bell_arm4_ge` | `bell(arm_4) >= -1/960` (true value -0.0010264) |
| `armEnv_of_cells` | ArmEnv on [0, 23/624] follows from three per-vertex cell families, using `isSubaction_ρwit`, `bell_add_ρwit_le` and `bg_ceiling` |
| `atom_bV_le` | Every atom satisfies `V_mu <= 3mu/23` for mu in [0, 23/624] (rational log bounds) |
| `atomCell0_of_core`, `atomCellMu_of_core`, `surchargeCell_of_core` | The cells hold outright for K >= 23 atom children and for degree >= 8, which leaves finite cores |
| `surchargeCore_proved` | Degrees 4..7 with arbitrary children. Tangent at the all-cherry point, a convex correction for 1/(d+S), and a per-child bound by ρwit class (`surcharge_child_le`). The resulting arm_K is closed by `atom_bV_le`. Uniform in K |
| `atomCell0Core_proved`, `atomCellMuCore_proved` | Non-atom vertices with <= 22 atom children. 22 per-K tangent certificates (`cell_K1`..`cell_K22`) with degree-6 Taylor log enclosures. Tightest: K = 6 (five cherries plus arm_4), margin 7.3e-4 |
| **`spider_dominates_highDegree_uncond`** | **For every root list with k >= 24 children, at least one of them a non-atom, and n-1 >= 90, there is a spider with q = 5(n-1) mod 11 copies of arm_4 and ((n-1)-9q)/11 copies of arm_5, of the same size and with strictly larger piRoot** |
| `phiRoot_le_taxed`, `spider_dominates_lowDegree_of_taxed` | Low-degree reduction: under `TaxedEnv D lam mu W`, the root bound loses `lam*(n-1)` and the spider wins once `log t + 1/t - 1 + kW - lam*N < log(26/23) - 1/96` |

Why the high-degree argument works: the numbers. At price mu <= 23/624 (that is, root degree k >= 24)
the arm_5 atom is the envelope: `V_mu(arm_5) = 3mu/23`. Every non-atom branch sits below it by at least
0.014520; the minimum is at node[cherry x5, arm_4], size 20. The best spider sits below log(26/23) by at
most 10*0.0010264 = 0.0103, because the residue of n-1 mod 11 can always be absorbed by <= 10 copies of
arm_4, whose y (3/19) exceeds 3/23. Since 0.0145 > 1/75 > 0.0104, the gap beats the integrality slack.

Scope of the Lean statements. They are about the cavity objective `piRoot`, which is the lead's formula.
In the Python engines this was checked against `pi_literal` (per(L)/prod deg). A Lean bridge from
`piRoot` to `R47Tree.Aobj` is **not** in these files.

## Checked by computation (not in Lean)

- **Every n <= 100:** max over ALL trees equals max over spiders, exactly (the repo's FrontierDP in
  `hwh_coverage_large_n.py`), and every maximizer is a spider.
- **Every n <= 200** (float numpy DP, `maxcheck 200`): max over all trees minus exact spider max is at
  most 1.4e-14. DP_RANGE_DETAIL_PLACEHOLDER
- **Envelope** (`envelope 80 19`): exact Pareto-frontier DP over planted branches of size <= 80. It agrees
  with brute-force enumeration for sizes <= 19 (A000081 counts). On mu in [0, 1/2], the supremum of V_mu
  over all branches equals the supremum over atoms. The non-atom gap is 0.01452 at mu = 0 and 0.01516 at
  mu = 0.037.
- **Cells** (`cells`, `gen-cells`): the float scans match, and every rational certificate constant used
  in Lean is re-checked exactly with fractions.
- **Size-free bound per root degree k** (`slack`): the bound with one non-atom child minus log(26/23) is
  below -0.0104 for every k >= 22. The Lean result uses k >= 24 with the arm-only envelope.

## Not proved: the remaining obligation (low degree)

**Case B.** Trees whose maximum degree is <= 23, with n above the computed range.

Why the size-free method cannot close it: the optimal spider's centre degree is only about n/10 (for
example 14 at n = 100). The size-free bound Psi(k) at small k is far above the spider value: X(k) =
Psi(k) - log(26/23) is 0.17 at k = 2 and 0.088 at k = 10. So for moderate n, size has to enter the
argument.

**Crisp reduction (proved in Lean):** `spider_dominates_lowDegree_of_taxed`. Root at a vertex of maximum
degree k <= D. Then every child branch has all vertices with <= k-1 children. Given

> `TaxedEnv D lam mu W`: for every branch b with `maxCh b + 1 <= D`, `bell b + lam*|b| + mu*y_b <= W`,

at `mu = 1/(kt)`, the tree loses `lam*(n-1)` against the size-free bound, and the spider wins as soon as
`n - 1 > (log t + 1/t - 1 + kW - log(26/23) + 1/96)/lam`.

Evidence for TaxedEnv (degree-capped frontier DP, sizes <= 700): TAXED_PLACEHOLDER

What a proof of TaxedEnv would need: a degree-capped, size-taxed version of the ceiling. That means a
subaction rho with `e_v + lam + rho(v) <= sum rho(c)` at every vertex of degree <= D. The tight vertices
of `ρwit` (leaf, cherry middle, arm_5 root) must pass the tax up to the hubs. The degree cap is what
forces a hub (slack about 0.084 per level for D = 23) every <= 11(D-1)+1 vertices. This is the same kind
of cell family as the ceiling and is not attempted here.

## Reproduce

```
cd proof/formalization && lake build R3Cert.BGSpiderCells && lake env lean AxiomGuard.lean
cd proof/verification
python3 bg_spider_reduction.py gen-cells      # exact re-check of the Lean certificate constants
python3 bg_spider_reduction.py cells
python3 bg_spider_reduction.py envelope 80 19
python3 bg_spider_reduction.py slack 200
python3 bg_spider_reduction.py maxcheck 200   # about 1 minute; 500 takes about an hour
```
