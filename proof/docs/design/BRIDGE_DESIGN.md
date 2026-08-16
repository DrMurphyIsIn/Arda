# Branch -> RTree -> SimpleGraph bridge: design + validated derivation

Status: **WIP**. This note records the reverse-engineered, numerically-validated relationship
between the three type-universes in R3Cert, so the bridge theorems are formalized from a *correct*
statement rather than a guessed one. (A naive first guess was empirically refuted -- see below.)

## The three representations

| Universe | File | Object | What it computes |
|---|---|---|---|
| `SimpleGraph V` | `Matching.lean` | `(lapl G).permanent`, `G.degree` | the **real** `pi(T) = per(L(T))/prod deg` |
| `RTree` | `CavityTree.lean` | `Zopen/Ztot`, weights `w` | raw weighted **matching partition functions**; `Zopen/Ztot = 1/(1 + sum w*(Zopen_c/Ztot_c))` |
| `Branch` | `Reach.lean` | `cav`, `eroot`, `logPhi` | the **DEC-reduced, rho_B-normalized** rooted amplitude |

The capstone (`Structure.node_le_omega`, `phi_le_one_of_potential`) lives entirely on `Branch`.
Nothing machine-checked currently connects `Branch.logPhi` to `RTree` or to `per(L(T))`.

## The exact DEC recursion (source of truth: `phibound.py`, quoted in `branch_multiplicativity.py`)

Rooting the amplitude at a vertex `r` with `c` cherries and child-subtrees `C_i`, degree
`d = #children + 1 + c` (the `+1` is the phantom parent edge):

```
Phi0(C) = a(d,c) * prod_i Phi(C_i)                              (root-UNMATCHED part; a PRODUCT)
Phi(C)  = Phi0(C) / rho0(C)
rho0(C) = 1 / ( 1 + z(d,c) * sum_i z(d_i,c_i) * rho0(C_i) ),      z(d,c) = 3/(3d+c)
a(d,c)  = (3/2)^c * (1 + c/(3d)) / rhoB^(1+2c)
```

Note: **cherries do NOT appear in `rho0`'s child-sum** -- they are folded into `z(d,c)=3/(3d+c)`
(the `+c`) and into `a(d,c)` (the `(3/2)^c` and `1+c/(3d)`).

## VALIDATED: the Branch-internal cavity identity  `cav = z(d,c) * rho0`

`Reach.cav (node c ch) = 3/(3 + 3*nch + 4c + 3S)`, `S = cavSum ch`. Writing `rho0 = 1/(1 + z(d,c)*S)`:

```
z(d,c)*rho0 = [3/(3d+c)] / (1 + [3/(3d+c)]*S) = 3/((3d+c) + 3S)
            = 3/(3(nch+1+c)+c + 3S) = 3/(3 + 3nch + 4c + 3S) = cav.     QED (pure algebra)
```

Numerically confirmed with **exact `Fraction` arithmetic on 400 random branches: 400/400.**
Also: `eroot = log a(d,c) + log(1 + z*S) = log a(d,c) - log rho0`, so
`logPhi(node c ch) = sum logPhi(child) + eroot` is exactly `log(Phi0/rho0)` -- consistent with the DEC `Phi`.

This is the **first bridge lemma**, formalized in `R3Cert/Bridge.lean` (`cav_eq_zc_mul_rho0`).
It exposes the DEC cavity recursion `rho0 = 1/(1 + z*S)` underlying `Branch.cav` -- the anchor any
`Branch -> RTree` matching-cavity map must reproduce.

## REFUTED: the naive `rho0 = raw 1/(deg*deg) cavity` bridge

First guess: realize a `Branch` as the literal cherry-expanded rooted tree (cherry = 2-edge path
`node - mid(deg2) - leaf(deg1)`), edge weights `w = 1/(deg_parent*deg_child)`, and claim
`rho0(b) = Zopen/Ztot` of that RTree.

**Empirically FALSE (92/400; only the c=0 cases pass).** Counter-example `b=(c=1, [])`:
- `Branch.rho0 = 1/(1 + z(2,1)*0) = 1` (cherries absent from `rho0`'s sum).
- raw cavity `= 1/(1 + (1/(2*2))*(2/3)) = 6/7`.

So `Branch.rho0` is **not** the raw `1/(deg*deg)` cavity. The real content of the `Branch -> RTree`
bridge is the **cherry-folding identity**: a raw node with `c` explicit cherries has the same
*rooted amplitude* as the DEC node with `z(d,c)=3/(3d+c)` and `a(d,c)` dressing. That folding
(summing the `c` cherry matching-terms into `z` and `a`) is the missing, still-unproved lemma.

## The amplitude seam to `per(L(T))` carries a SECOND limit

Comparing the finite real ratio `pi(T)=per(L)/prod deg` to DEC `Phi(root)` on small trees:
`log_rhoB(pi/Phi)` is **not** an integer or clean function of `n` (measured n+0.29 .. n+1.39).
Reason: DEC `Phi` is defined as a **rooted, rho_B-normalized LIMIT ratio** -- the amplitude of a
gadget attached to a `p -> infinity` cherry-hub, `Phi(G) = lim_p amp(hub+arms+G)/amp(hub+arms)`
(`branch_multiplicativity.py`), not the pi of any finite tree. So the `Branch -> SimpleGraph`
amplitude bridge factors through the hub limit and is materially harder than the cavity bridge.

## Roadmap (in dependency order)

1. **[DONE, Bridge.lean]** `cav = z(d,c)*rho0`  -- Branch-internal cavity structure. Pure algebra.
2. **[OPEN]** cherry-folding: raw-cavity(node with c explicit cherries) expressed via `z(d,c)` +
   the dressed leaves; gives `rho0(b) = ` (a raw matching-cavity of the *dressed* tree). `RTree`-level.
3. **[OPEN]** `RTree.Ztot`(realized dressed tree) `= SimpleGraph` weighted matching sum for the
   graph realizing that RTree (a realization functor `RTree -> Sigma V, SimpleGraph V` + acyclicity).
4. **[CORE DONE, BridgeStep4.lean CI-green]** amplitude normalization / hub limit. `hub_rho0_limit`:
   `rho0(node cH (replicate p arm ++ branches)) -> 1/(1+cav arm)` as `p->inf`, INDEPENDENT of branches --
   the decoupling mechanism (real Mathlib `Tendsto`). Remaining OPEN (hardest): tie `logPhi(B) <= 0`
   back to `per(L(T))`. Needs the `branch_multiplicativity` p->infinity limit formalized.

Steps 2-4 each need the CI loop (local Lean build unsafe on this machine -- documented M3 SoC
watchdog crash; would risk the live trading daemons). Verify via the GitLab `lean-verify` job.

---

## Progress update (Steps 1-2 DONE, CI-green)

- **Step 1 DONE** (`R3Cert/Bridge.lean`): `cav_eq_zc_mul_rho0` -- `cav = z(d,c)*rho0`, `rho0 = 1/(1 + z(d,c)*S)`.
- **Step 2 DONE** (`R3Cert/BridgeStep2.lean`): the cherry-folding. `realize : Branch -> RTree` (DEC-dressed,
  edge weight `z(d,c)*z(d_child,c_child)`, cherries folded into `z`) + positivity + **`q_realize_eq_rho0`:
  `Zopen(realize b)/Ztot(realize b) = rho0 b`** (via `CavityTree.tree_cavity_recursion`).  So `Branch.cav`
  IS a DEC-weighted matching cavity.  Corollary `cav_eq_zc_mul_q_realize`.

## Step 3 (RTree.Ztot = weighted matching sum) -- DONE (BridgeStep3.lean, CI-green)

**COMPLETE.** `Ztot_eq_msum : Ztot t = msum (realize t)` -- RTree.Ztot equals an explicit weighted matching
sum. Built self-contained (avoided Mathlib SimpleGraph): `msum` (include/exclude matching sum, validated
200/200 = brute-force + = Ztot), `realize` (address-vertex edge list, root edges first), `msum_append`
(disjoint multiplicativity) + `msum_pull` (pull a disjoint block from the middle -- the key tool, since
rRoot/rSub share child-root vertices), suffix/disjointness/filter lemmas, and the mutual
`Ztot_eq`/`msum_rSub`/`main_cond` induction (root-edge conditioning: Popen+Matched=Ztot).

### (superseded) original design note

**Target (numerically VALIDATED, exact Fraction, 200/200 trees up to 16 edges):** realize the dressed
`RTree` as a finite weighted graph -- vertices = tree nodes (DFS order), edges = each parent->child pair
carrying the RTree edge weight `w` -- and then

    Ztot (t)  =  sum over MATCHINGS M of the realized tree-graph  of  prod_{e in M} w_e,

where a matching is a set of pairwise vertex-disjoint edges (empty matching contributes `1`).  This is the
standard identity "matching partition function = weighted matching-sum"; `CavityTree.Zopen/Ztot` are
*constructed* as the root-unmatched / all-matchings partition functions, so the identity is the bridge to a
Mathlib `SimpleGraph`.

**KEY OBSTACLE (why it is not a quick reuse):** `Matching.permanent_eq_matching_sum` is LAPLACIAN-specific --
its matching sum weights vertices by `deg` (from `per(L)`), i.e. edge weight `1/(deg_i deg_j)`.  The DRESSED
RTree carries `z(d,c)*z(d',c')` edge weights, NOT `1/(deg deg)`.  So Step 3 needs a **general** weighted
matching-sum `matchingSum : (G : SimpleGraph V) -> (Sym2 V -> R) -> R := sum over matchings prod w`, which is
NOT in `Matching.lean`.  The degree/Laplacian connection (dressed `z` <-> real `1/(deg deg)`) is exactly the
**Step 4** amplitude/`rho_B` hub-limit content, deliberately deferred.

**Formalization roadmap for Step 3 (each an OPEN CI chunk):**
1. `realizeG : RTree -> Sigma (V : Type), SimpleGraph V x (Sym2 V -> R)` -- a DFS realization onto `Fin n`
   (n = node count), tree edges parent<->child, weight from the RTree.  Prove the graph is `IsAcyclic` (tree).
2. `matchingSum G w := sum_{M in G.matchings} prod_{e in M} w e` -- general weighted matching-sum over the
   (Fintype) set of matchings of a finite graph.  (New; Mathlib has `Subgraph.IsMatching` but not this sum.)
3. `Ztot_eq_matchingSum : Ztot t = matchingSum (realizeG t).graph (realizeG t).w` -- by induction on `t`,
   splitting matchings on whether a root edge is used (the `Popen + Matched` decomposition IS this split).

This is a self-contained finite-graph-theory development (~a few hundred lines); it does not touch the open
mathematics of `Phi<=1`, only the type-universe glue.  Step 4 (the `p->infinity` cherry-hub amplitude limit
tying `logPhi(B)<=0` back to `per(L(T))/prod deg`) remains the hardest and is untouched.

## Step 3b/3c/3d (msum semantics + the involutions <-> matchings bijection)

- **Step 3b DONE** (`BridgeStep3b.lean`, CI-green): `subm` (matching enumeration by the same
  include/exclude recursion), `msum_eq_sum_subm`, `mem_subm` (matchings = pairwise vertex-disjoint
  sublists).
- **Step 3c DONE** (`BridgeStep3c.lean`): `subm_nodup` + `msum_eq_finset_sum` (`msum` as a `Finset`
  sum).  First CI run hit a `List.count` `BEq`-instance mismatch in the final rewrite; fixed by
  replacing the count argument with `List.sum_toFinset` (Nodup list => Finset sum = mapped-list sum).
- **Step 3d** (`BridgeStep3d.lean`): the involutions <-> matchings bijection.  `IsEdgeEnum G E`
  (each edge listed once, one orientation, weight `1/(deg u * deg v)`); forward map
  `sigma |-> E.filter (sigma e.1 = e.2.1)`, backward `toPerm M` (product of swaps), the two round
  trips (`toPerm_filter`, `filter_toPerm` via `sublist_eq_of_nodup`), the weight identity
  `prod_v (1 if fixed else 1/deg v) = wprod M` (`prod_weights`, touched-set decomposition), and
  `Finset.sum_nbij'` assembling **`pi_eq_msum : per L(G) / prod deg = msum E`** on top of H2a.
  The SimpleGraph amplitude now speaks the same `msum` language as the `Branch`/`RTree` side.

## Step 4b (branch multiplicativity in the hub limit) -- `BridgeStep4b.lean`

**KEY SIMPLIFICATION over `branch_multiplicativity.py`'s roadmap:** the "missing uniform O(1/p^2)
constant" is NOT needed in Lean.  Phi is DEFINED by the hub limit, so multiplicativity is a pure
limit statement -- `Tendsto` algebra on the EXACT finite-`p` identity

    logPhi (hub_p ++ Gs) - logPhi (hub_p) = logPhiSum Gs + [eroot-difference],

with the `eroot` seam -> 0 (`tendsto_ac_shift`: the `a(d,c)` dressing -> `(3/2)^c/rhoB^(1+2c)`;
`tendsto_zc_term`: the hub cavity load -> `cav arm`, the `hub_rho0_limit` mechanism).  Main:
**`logPhi_hub_diff_tendsto`** -- `Phi(G) = prod_i Phi(G_i)` machine-checked in the limit, for
every hub cherry-count, arm shape and gadget list.

## Step 4c (REMAINING, the hard seam): raw-amplitude identification

Target: `exp (logPhi b) = lim_p pi(T(hub_p + b)) / pi(T(hub_p))` -- identify the DEC/Branch
amplitude with the hub-limit of RAW finite-tree `per L / prod deg` ratios.  Pieces:
1. literal-tree construction `Branch -> address edge list` with cherries EXPANDED (2-paths) and
   RAW weights `1/(deg u * deg v)`; instantiate `IsEdgeEnum` for it (the `litEdges` step) so
   Step 3d turns `pi` into an `msum`;
2. raw-`msum` cavity peeling at the hub root (Step 3's `main_cond` machinery, raw weights);
3. the cherry-folding AT AMPLITUDE LEVEL: raw node with `c` explicit cherries vs the DEC-dressed
   node -- the `a(d,c)` factors and the `rhoB` normalization must reconcile the raw and dressed
   telescopings (this is where the measured non-clean `log_rhoB(pi/Phi)` offsets live; the
   offsets are `p`-dependent but CANCEL in the hub ratio);
4. the raw hub decoupling limit (analog of `hub_rho0_limit` at `1/(deg deg)` weights).
This is a genuine multi-session development; (1)+(2) are mechanical, (3) is the mathematical
content, (4) mirrors green code.
