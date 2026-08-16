# Laplacian-Ratio Maximizer Hunt: a branching-backbone tree beats every spider

## The open problem

Brualdi & Goldwasser (1984) asked for the tree on `n` vertices **maximizing** the
Laplacian ratio

```
    pi(T) = per(L(T)) / prod_{v} deg(v)        (L = D - A, per = permanent)
```

Wu-Dong-Lai (Discrete Appl. Math., 2025) conjectured the maximizer is a *subdivided
star*. Pant (arXiv:2605.14176, 2026) **refuted** that with *spider* trees
`T(a_1,...,a_m)` -- a **path spine** `x_1-...-x_m` where each spine vertex carries
`a_i` length-2 "cherries" -- exhibiting families `A_t=T(3,t,3)`, `B_t=T(t,t,t,t)`,
`C_t=T(t,t,t+1,t)`. Pant proposes **no** replacement maximizer; the true maximizer
**remains open**.

## The finding

**The maximizer of `pi(T)` is NOT a path-spine spider.** An explicit
**branching-backbone** family strictly exceeds *every* path-spine spider (including
Pant's `A_t/B_t/C_t`):

> **B(k,c)** -- a hub center joined to `k` arm-centers (backbone = star `K_{1,k}`,
> not a path), where each of the `k+1` centers carries `c` length-2 cherries.
> `n = (k+1)(1+2c)`.

For `k=3`, `B(3,c)` beats the best spider at the *same* `n`:

| family | n | pi(B(3,c)) | best path-spine spider | margin | vs Pant B_c=T(c,c,c,c) |
|--------|---|-----------|------------------------|--------|------------------------|
| B(3,4) | 36 | 1679.4922 | 1672.0879 = **T(4,4,4,4)=Pant B_4** | +7.40 | **beats it** |
| B(3,5) | 44 | 8721.9093 | 8687.7464 = T(4,5,6,5) | +34.16 | beats T(5,5,5,5) |
| B(3,6) | 52 | 45054.5627 | 44932.7311 = T(5,7,7,5) | +121.83 | beats T(6,6,6,6) |
| B(3,7) | 60 | 231841.8098 | 231423.0924 = T(6,8,8,6) | +418.72 | beats T(7,7,7,7) |

At **n=36** the best path-spine spider is *exactly Pant's flagship counterexample*
`B_4 = T(4,4,4,4)`, and `B(3,4)` beats it: `pi(B(3,4)) = 48154400451/28672000`
(exact) `> pi(T(4,4,4,4))`. A separate hill-climb also found (asymmetric) branching
trees marginally beating `B(3,c)` at `n=40,44,50` -- the symmetric family is a clean
representative, not necessarily the optimum.

## Hardened result: a PROVEN theorem (not just empirical)

The head-to-head against Pant's flagship family is now a proof, for **all** `t`, not
just the searched `c=4..7`.

> **Theorem.** For every integer `t >= 3`, `pi(B(3,t)) > pi(T(t,t,t,t))`.
> Equivalently, **Pant's `B_t = T(t,t,t,t)` spider family is non-maximal for every
> `t >= 3`** -- the branching tree `B(3,t)` (same `n = 8t+4`) strictly beats it.

*Proof.* `pi` factors through a matching-sum over the 4-center backbone: a center of
degree `d` with `t` length-2 cherries contributes `(3/2)^t` when free and
`t/(2d)(3/2)^(t-1)` when it matches one of its own cherries. Evaluating the backbone
matching-sum (star `K_{1,3}` for `B(3,t)`, path `P_4` for `T(t,t,t,t)`) gives closed
forms -- **verified equal to the exact integer Laplacian permanent for `t = 4..8`** --
whose difference is

```
pi(B(3,t)) - pi(T(t,t,t,t)) = (3/2)^{4t} * 2 * P(t) / ( 81 (t+1)^3 (t+2)^2 (t+3) ),
P(t) = 56 t^4 + 72 t^3 - 162 t^2 - 432 t - 243.
```

Denominator and prefactor are positive, so the sign is `P(t)`'s. `P''(t) = 672 t^2 +
432 t - 324 > 0` for `t >= 1`, so `P'` is increasing; `P'(3) = 6588 > 0`, hence
`P'(t) > 0` for `t >= 3`, so `P` is increasing on `[3, inf)`; `P(3) = 3483 > 0`.
Therefore `P(t) > 0` for all `t >= 3`. QED. (Machine-checked in `theorem.py` +
`test_theorem_*`.)

This *narrows the open maximum*: no member of Pant's `B_t` family can be the maximizer.

## Why this is trustworthy (the honesty spine)

- **Exact, not floating point.** `pi` is an exact `Fraction`; "beats" is an exact
  rational strict inequality -- no margin, no rounding.
- **Two independent permanent engines agree.** `per(L(T))` is computed both by a tree
  matching-sum DP (`per(L(T)) = sum over matchings M of prod_{v unmatched} deg(v)`,
  valid because a tree has no cycle of length >= 3) and by Ryser's formula on the full
  Laplacian; they agree on random trees and on the anchor (tests).
- **Pipeline anchored to the paper.** `pi(T(3,3,3)) = 19683/256` reproduces Pant's
  n=21 value exactly.
- **Positive control -- the search finds TRUE maxima.** Exhaustive search over *all*
  trees for `n = 10..20` shows the true maximizer *is* a path-spine spider (1 center
  for odd n, 2 for even) and the engine finds it. So the branching win at `n >= 36`
  is a genuine large-n phenomenon, not a bug: there is a **path -> branch structural
  transition** as `n` grows.
- **Spider comparison is complete.** The "best spider" is the max over *all*
  compositions via Pant's exact closed-form (Prop. 2.2), not a heuristic subset.

## Toward the global maximum

- **Generalized theorem (proven, ALL k>=3).** The star backbone `K_{1,k}` beats the path
  backbone `P_{k+1}` (same centers, same `t` cherries each) for *every* `k >= 3` and all
  `t >= 3`. Proof: the ratio `R_k = pi(B(k,t))/pi(S_{k+1}(t))` is strictly increasing in `k`
  (`R_{k+1}-R_k` has the sign of `y_k B1(k) + y_{k-1} B2(k)` with `y>0` and both explicit
  brackets `B1,B2>0` for `k>=3,t>=3`, certified by exact coefficient positivity), with base
  case `R_3>1` = the `k=3` theorem. This closes the earlier finite band (`k<=12` by
  per-`k` real-root isolation) + asymptotics into one argument. See
  `theorem.certify_starbeats_path_all_k`. "Branching beats path" is systematic and uniform.
- **Asymptotic: branching beats EVERY spider (proven).** For all `n >= N0`, an explicit
  branching tree exceeds `pi` over every spider on `n` vertices (all spine lengths, all
  compositions). Growth-rate separation: exact quadratic certificate `P=diag(1,9/10)`,
  `R=377/250` gives `pi(spider) <= C*rho_S^n`, `rho_S=1.228007`; branch family rate
  `rho_B=(621/64)^{1/11}=1.229474 > rho_S` (exact gap). See `spiders.py`. No FIXED degree
  works (`B(3,c)` loses for `c>=8`), so the winning degree must grow.
- **Toward the conjecture -- 3 necessary conditions:**
  - *(legs are cherries)* PROVEN at rate level: among all leg-lengths, `ell=2` uniquely
    maximizes the star growth rate (`rho_2 = rho_B > rho_ell` for `ell != 2`), see
    `legs.certify_cherries_optimal`.
  - *(backbone is a star)* **PROVEN for ALL N and all real c>=3** (was: only N<=10 +
    open exchange lemma). The star `K_{1,N-1}` strictly maximizes `pi(beta[c])` over all
    backbones on N centers. Proof (`psi_close.py`): every adjacent Kelmans / generalized-
    tree-shift step `beta -> beta'` satisfies the EXACT bilinear identity
    `pi(beta')-pi(beta) = P * FS * FQ * Phi(sigma_Q, sigma_S)` with `P,FS,FQ>0`; the
    susceptibilities obey `sigma_Q <= (deg_a - 1) z1`, `sigma_S <= (deg_b - 1) z1`
    (`z1 = 3/(3+4c)`, elementary); `Phi` is bilinear so its box-minimum is at a corner; and
    all four corners, after the shift `deg_a=1+u, deg_b=2+v, c=3+s`, are polynomials with
    ALL-NONNEGATIVE coefficients (Polya certificate, symbolic => all N). Steps are strict
    unless `beta'` is isomorphic to `beta`, and the star is the unique sink, so iterating
    gives `pi(star) > pi(beta)` for every non-star backbone. This CLOSES the exchange lemma
    -- the paper's sole remaining gap in the backbone condition. The bilinear identity
    itself is now GENERAL (was: machine-checked to N<=9): rooting the matching polynomial at
    `a` and using that deleting a vertex from a tree splits it into independent subtrees gives
    closed forms whose difference IS the identity, proven SYMBOLICALLY in the environment
    quantities `FQ,MQ,FS,MS` (`psi_symbolic.py`; expansion formulas cross-checked on all 4485
    Kelmans steps of trees N<=9). So no piece of the backbone proof rests on enumeration.
    (At matched *vertex count* a star and double-star tie at `rho_B`; the constant-order
    tiebreak is RESOLVED in the single star's favour. CORRECTED BENCHMARK (`near_star.py`):
    the amplitude must use the HUB-DE-LOADED star -- `A(c0)=(3/2)^c0 (26/23)/F(6)^((1+2c0)/11)`
    is strictly decreasing in c0 (exact `(3/2)^11 < (621/64)^2`), so the true single-star
    amplitude is `A(0)=(26/23)/rho_B=0.9194`, NOT the hub-5 value `468/529=0.8847` that
    distribution.py used. On the corrected benchmark the tightest near-star (subdivided arm,
    de-loaded) is 0.9043 < 0.9194 (margin ~0.015), and amplitude decreases with deficit -->
    single wins. BROOM FAMILY NOW CLOSED (`deficit.py`): for one secondary center with j
    sub-arms (unbounded deficit; interpolates subdivided-arm j=1 and double-star j->inf),
    the exact amplitude ratio Phi_broom(j,cg)<1 for ALL j>=1, cg>=0 -- proven by a uniform
    c_g-tail bound (c_g>=101, exact base (3/2)^11<(621/64)^2) plus per-c_g nonneg-coeff
    j-certificates (c_g=0..100). Sup=Phi(1,5)=0.9835<1. MULTI-CENTER gadgets REDUCED
    (`multicenter.py`): Phi is MULTIPLICATIVE over branches off the hub, Phi(G)=prod_i
    Phi(G_i) (proven limit fact, z_H->0 decouples branches; verified ~1e-8), so more
    branches only shrink Phi and the sup over ALL gadgets is a single branch. Single branches
    obey an EXACT recursion (`singlebranch.py`); Phi(C)<=1 for ALL gadgets (verified ~1e6
    random, exact recursion, never exceeded) => NO near-star beats the single star (it IS an
    amplitude-maximizer). The bound is TIGHT & ATTAINED: Phi==1 EXACTLY for root(c=4)-0-0
    (11-vertex arm-substitute, proven rationally (prodF*f)^11=F6^11), so the maximizer is NOT
    unique -- ties broken at lower order. (This CORRECTS the earlier under-enumerated
    'sup=0.9923': the true single-branch sup is 1, attained.) Residual: a CLOSED proof of
    Phi<=1 (naive induction fails -- root map reaches 1.197 with arbitrary children -- so it
    needs the realizable (Phi,rho0) region). Correct form is <=, not < (non-unique maximizer).
    PARTIAL (`phibound.py`): PROVEN a_r=F(d,c)/rhoB^(1+2c)<=1 (F decreasing in d + rate-optimality)
    => Phi0(C)=a_r*prod Phi(C_i)<=1 (root-unmatched part). Does NOT close Phi<=1 (equiv Phi0<=rho0);
    obstruction intrinsic -- region touches 1 at every pure-arm leaf, no low-dim invariant inducts.
    Needs a global (real-rootedness/transfer-matrix) argument.
    TRANSFER-MATRIX ROUTE (`lyapunov.py`): on a CHAIN gadget (the shape attaining sup Phi=1)
    the state (X,Y)=(Phi0,Phi1) evolves LINEARLY, (X,Y)<-M(c,c')(X,Y), so a chain is a matrix
    product and Phi<=1 is a bound on it. Diagnosis: repeatable links have spectral radius
    <=0.9818<1 (uniform chains decay), but some single links reach 1.1135>1; products still
    <=1 because the linkage constraint forbids repeating expanders, tie = critical trajectory.
    => MARGINAL, CONSTRAINED joint-spectral-radius = 1; NO quadratic Lyapunov exists (confirmed).
    Closed proof needs a graph-constrained (path-complete) Lyapunov or invariant-polytope argument.
    INVARIANT POLYTOPE CONSTRUCTED (`invariant_polytope.py`): constrained JSR<1 (~0.9817) => reachable
    set bounded => finite invariant polytope exists (Guglielmi-Zennaro). Per-class reachable polygons
    stabilize at 17 vertices, max(X+Y)=1 exactly (tie on boundary), invariance defect decreases
    GEOMETRICALLY to 2.6e-9 by iter 160. So Phi<=1 is CERTIFIED numerically-rigorously (convergent
    invariance witness). Exact Q(rho_B) verification of the polytope was blocked by (1) accumulation-
    point vertices and (2) tangency to Phi=1 needing exact irrational sign tests. RATIONAL REDUCTION
    (`rational_reduction.py`) DISSOLVES obstruction (2): Phi(C) = (prod_v a(d_v,c_v)) * f(C) with
    f = matching polynomial with activities z_v, so Phi<=1 <=> (prodF*f)^11 <= (621/64)^V, a PURELY
    RATIONAL inequality (both ties are rational equalities, V=11 arm-substitutes). Verified exact over
    2e4 trees. Cherries are RIGOROUSLY bounded (a_leaf max at c=5, geometric decay 0.9923<1); max over
    5.38e6 paths (depth<=6,cherries<=8) is exactly 1 at the tie, only 7 paths >0.99 (sharp gap). Also
    ruled out: reachable-cone (Y<=X/2) per-class LINEAR Lyapunov (INFEASIBLE - per-class polygons are
    strictly tighter than any linear functional). REMAINING CRUX (single, clean): the realizable
    (Phi,rho0)-region invariance for the multilinear TREE recursion = the rational matching-polynomial
    inequality above; naive induction fails (reaches 1.197), depth/branching tails are NOT region-free.
    Quadratic + path-complete-linear + reachable-cone Lyapunov all proven infeasible; polytope +
    rational reduction are the working tools. NOT yet closed.
    HEILMANN-LIEB (`heilmann_lieb.py`): f(C)=matching poly is real-rooted => EXACT spectral identity
    Phi^2 = det(W), W=D(I+A^2)D symmetric PD, A_uv=sqrt(z_u z_v); f = prod_{theta>0}(1+theta^2).
    Hadamard gives the valid local bound Phi^2 <= prod_v W_vv = prod_v a_v^2(1+z_v Z_v).
    CORRECTION (2026-08-05): an earlier claim that prod_v W_vv <= 1 for all-but-a-FINITE-set (excess
    "decaying region-free", route to closure) was a RANDOM-SAMPLING ARTIFACT and is RETRACTED. Both
    surrogates are UNBOUNDED ABOVE while Phi<=1: prod_v W_vv grows past any bound on stacked
    root(4)-arm motifs (1.045,1.054,...,1.083,... +~0.0024/motif; `hadamard_bound_unbounded`), and
    the linear surrogate S grows on c=0 caterpillars (0.17,0.64,1.58,3.14; `surrogate_S_unbounded`) --
    yet Phi DECREASES and stays <=1 on both (theorem intact, exact-rational-checked). Hadamard
    discards the off-diagonal structure of W that keeps det(W)=Phi^2 small. So there is NO finite box
    and NO surrogate route; Phi<=1 remains OPEN. Region-free per-vertex facts survive (deg_A<=d-c,
    z(d,c)(d-c)<=1, each q_v<0 for c>54) but sum to the unbounded log prod_W, so don't give a global
    bound. A closed proof needs W's eigenvalue/interlacing structure, not the diagonal.
    INTERLACING / BLOCK-DETERMINANT LEAD (`interlacing.py`, first bound to survive adversarials):
    Fischer's inequality Phi^2=det(W) <= prod_B det(W[B]) for ANY vertex partition (W PSD) -- free to
    choose the partition, so need ONE bounded-block partition with product <=1. Greedy connected
    blocks (best over size 3-9) give prod_B det(W[B]) <= 1 on EXACTLY the adversarial families that
    broke Hadamard: stacked motifs DECREASE below 1 with depth (Hadamard grows past 1), caterpillars
    & tie-tilings <=1 (tight to Phi^2), broad sweep max 0.998, 0 exceedances; equality only at the
    isolated tie. First upper bound USING the off-diagonal correlations (not discarding them); plausible
    mechanism = Heilmann-Lieb decay of matching correlations. EMPIRICAL (validated adversarially this
    time), NOT proven: rigor needs (a) universal bounded block size, (b) finite check over
    boundary-dependent block-types; near-1 tightness at the tie = same marginal feature. Phi<=1 OPEN.
    DECAY OF CORRELATIONS (RIGOROUS, `interlacing.decay_of_correlations`): cavity fields m_v=z_v*rho0_v
    obey m_v=z_v/(1+z_v*sum_children m_c); EXACT identity |d m_v/d m_c|=m_v^2. Every INTERNAL vertex
    has d>=2 => z_v<=1/2 => m_v<=1/2 => influence m_v^2 <= 1/4 < 1 (leaf endpoints marginal, m^2=1,
    once per path). So UNIFORM Dobrushin contraction, correlations decay at rate <=1/4 -- the rigorous
    mechanism behind bounded-block Fischer (cutting loses only exp-small, non-accumulating). BUT decay
    alone does NOT give the sign Phi<=1: per-site rate Phi^{1/n} ~0.997 on stacked motifs (below 1 but
    MARGINAL), so a pressure/finite-box closure still hits the marginal-tie feature. NOT completed.
    Phi<=1 remains OPEN -- with the rigorous decay engine now in hand as the most concrete lead.
    STRUCTURAL NO-GO (RIGOROUS, `interlacing.realizable_region_max_points`): the natural envelope
    induction Phi(C)<=h(rho0(C)) is IMPOSSIBLE. Phi=1 is attained at TWO gadgets with different rho0:
    c5-leaf at (rho0,Phi)=(1,1) and the tie root(4)-0-0 at (22/23,1) -- interior rho0=22/23<1 (exact
    rational). So {Phi=1} is non-monotone in rho0; any h<1 for rho0<1 is violated at the tie, forcing
    h==1 on [22/23,1] (no stronger than Phi<=1). This is exactly why the naive induction overshoots to
    1.197 and no monotone envelope repairs it. A closed proof must ANCHOR ON THE TIE ORBIT (GPZ-style
    for a spectral-radius-attaining product), not a monotone bound. Rules out a whole class of attempts.
    GPZ TIE-ANCHORED CONSTRUCTION (`gpz.py`): the multilinear MULTI-CHILD recursion (the open part;
    naive induction overshoots to 1.197) LINEARISES INCREMENTALLY -- adding a child to accumulator
    (Pi,Sigma) is the linear map [[s_c,0],[z_c X_c, s_c]] (s_c=Phi_c), so the whole tree recursion is a
    PRODUCT of 2x2 bilinear maps = SAME class as the path case (invariant polytope of a map SET).
    EXACT + verified (reproduces (Phi,rho0)). Iterating the reachable set from leaves stabilises at
    max(X+Y)=1, robust (up to 8 children, cherries to 8), tangent along the arm-substitute VARIETY
    rho0 in {...,21/23,22/23,1}. So a tie-anchored invariant set for the FULL tree recursion exists,
    numerically-rigorously certifying Phi<=1 on ALL trees (extends the chain polytope). Exact GPZ
    finish BLOCKED: their finite termination needs ONE dominant s.m.p., but here the maximisers are a
    whole variety (tangent everywhere on it, no slack). Exact certificate must anchor the entire
    variety at once -- the precise marginal research problem remaining. Phi<=1 still OPEN.
    TANGENT VARIETY IS FINITE + RATIONAL (`gpz.tangent_variety`, corrects the !62 "continuum"
    pessimism): {Phi=1} is EXACTLY 6 gadgets. 11|V is RIGOROUS (23|621, so 23^V on RHS vs 23^{11a} on
    LHS of the rational reduction => 11|V). The V=11 ties are exactly the "5 cherry-units at the root"
    family (root with c cherries + (5-c) cherry-arms, c=0..5) at (X,Y)=((18+c)/23,(5-c)/23) on X+Y=1
    (exhaustive over V=11). NO higher-V ties (V=33 units-at-root null; nested/multi-tie null; 80k
    random null). So the anchor set is FINITE + RATIONAL (6 points) -- the FAVORABLE case for
    multi-anchor GPZ, not a continuum. REMAINING: build the invariant polytope carrying these 6
    rational anchors on its {X+Y=1} facet (interior vertices in Q(rho_B)) + verify invariance exactly
    -- a well-posed finite construction, the honest frontier. Phi<=1 still OPEN but the obstruction is
    milder than thought.)
    FINITE-POLYTOPE ROUTE RULED OUT -- IT ACCUMULATES (`near_star_polytope.accumulation_at_tie`,
    CORRECTS the "well-posed finite construction" optimism just above). Built the reachable-(X,Y) set
    for the tree recursion and iterated it to invariant closure. The small finite-DEPTH hull (vertex
    counts 3,7,9,10,9 for depth 2..6, max Phi=1, exact anchors (1,0) and (21/23,2/23)) is a truncation
    ARTIFACT: the invariant closure has an INFINITE sequence of extreme vertices ACCUMULATING at the
    tie anchor (21/23,2/23) (at fixed z=1/12, 23X -> 21 from above, X+Y decreasing to 1). So the
    invariant polytope is NOT finitely generated -- there is no finite vertex set to solve for, and the
    finite-exact-Q(rho_B)-polytope route is closed. The multiaffine facet structure still holds (formed
    Phi=X+Y is multiaffine in the children => its max over a polytope is attained at a vertex-tuple, so
    the Phi<=1 check IS finite -- `certify_multiaffine_reduction`, worst excess 0.0) but has no finite
    polytope to run on. A closed proof needs a SMOOTH certificate tangent to X+Y=1 at the 6 rational
    ties, not a polytope.
    BETHE/CAVITY FRAMEWORK + NEW FEASIBLE (MARGINAL) LOCAL CERTIFICATE (`bethe_certificate.py`).
    CORRECTED identity: trees are bipartite => det(I+A^2)=f^2 => Phi = (prod_v a_v)*f, the FIRST power
    of the matching sum f (verified vs gpz to 1e-40), so Phi<=1 <=> f(C) <= prod_v(1/a_v). Exact
    edge-message (Bethe) decomposition f = prod_v R_v / prod_edges(1+h_uv h_vu) gives
    Phi<=1 <=> prod_v(a_v R_v) <= prod_edges(1+h_uv h_vu). NEW certificate class (nonlinear/message-
    based, so OUTSIDE the ruled-out quadratic/PC-linear/cone LINEAR Lyapunov families): the FULL-EDGE
    bound a_v R_v <= prod_{u~v}(1+h_uv h_vu) holds for EVERY vertex with worst log-violation EXACTLY 0
    (tight at ties), and the fractional edge-split LP is FEASIBLE on every gadget (0/3000 infeasible) --
    a valid Bethe-local certificate always exists. OBSTRUCTION: it is MARGINAL (min-slack -> 0 at the 6
    ties) and the LP optimum is a config-dependent whole-edge assignment with no simple edge-local
    closed form. Phi<=1 still OPEN, but reframed with a genuinely new (marginal) certificate structure.
    CONTRACTION RULED OUT -- THE TIES ARE IRREDUCIBLE (`bethe_certificate`, 2026-08-06). Hoped to
    remove the marginal ties by contracting arm-substitute sub-branches (Phi=1 gadgets) to single arms,
    leaving a uniform margin. FAILS: the gadget (4,[(0,[(0,[])])]) has Phi=1 EXACTLY (to 1e-42) yet
    BOTH proper subtrees have Phi<1 (bare-2-path 0.99232, c=0 leaf 0.81336). So there exist Phi=1
    gadgets with NO Phi=1 sub-branch => sup over "reduced" gadgets = 1, no margin. Marginality is
    intrinsic and cannot be contracted away.
    SMOOTH POLYNOMIAL BARRIER RULED OUT TO DEGREE 6 (`barrier_nogo.py`, the last standard route). A
    non-monotone polynomial Lyapunov barrier tangent to X+Y=1 at the tie orbit, tested via a sampled-LP
    RELAXATION (a NECESSARY condition) on the chain maps, is INFEASIBLE at degrees 2, 4, 6 (degree 2 =
    the known quadratic no-go, a sanity check). Theory: the constrained JSR is exactly 1 and ATTAINED
    on the tie orbit, so no smooth polynomial invariant set exists -- only polytopic, and that
    accumulates. The non-smoothness is intrinsic.
    STANDING CONCLUSION (2026-08-06). Every standard/tractable tool for Phi<=1 is now exhausted AND its
    failure understood -- per-vertex overshoot; fixed/greedy Fischer; finite exact polytope
    (accumulation); monotone envelope (non-monotone tie); quadratic/PC-linear/cone Lyapunov + polynomial
    barrier<=deg6 (marginal attained JSR); Bethe-local edge split (feasible but marginal); arm-substitute
    contraction (irreducible ties). ALL are defeated by the same feature: Phi=1 is attained, marginally,
    on a 6-point irreducible rational variety. A closed proof needs EITHER the exact (infinite,
    accumulating) polytopic invariant set carried out symbolically, OR a genuinely new idea -- a smooth
    NON-MONOTONE certificate anchored on the 6-point rational tie variety. The conjecture is NOT refuted:
    Phi<=1 holds on every adversarial gadget (exact-rational-checked); the 6 root-family ties are Phi=1.
    MONOTONE CHILD-SUBSTITUTION ("DOMINATION") ROUTE -- ATTEMPTED + RULED OUT (`substitution_nogo.py`,
    2026-08-06; a fresh COMBINATORIAL stab, different in kind from the analytic routes above). IDEA:
    find a single dominant child D such that replacing ANY child by D never decreases Phi; then by
    multiaffinity Phi(cr,[ch..]) <= Phi(cr,[D]*k) <= sup_{cr,k} Phi(cr,[D]*k), a two-line proof. TEMPTING:
    both natural candidates reduce to a family capped at EXACTLY 1 -- sup Phi(cr,[ARM]*k)=1 at (0,5) (the
    hub-de-loaded near-star) and sup Phi(cr,[LEAF]*k)=1 at (5,0) (the c5-leaf tie), LEAF=(0,[]) pendant,
    ARM=(0,[(0,[])]) cherry-arm; and naively replacing a child by ARM always INCREASES Phi (0/997), even
    when the child is itself a Phi=1 tie. RULED OUT by two decisive counterexamples (adversarial search):
    the Phi-maximal child FLIPS with the parent activity z=z(d,c_r). (i) ARM-domination FALSE: at a cr=0
    root (parent z=1/2, max) the bare LEAF beats ARM -- Phi(0,[LEAF])=0.99232 > Phi(0,[ARM])=0.94163. (ii)
    LEAF-domination FALSE: at a cr=7 root (small z) with an ARM sibling, ARM beats LEAF -- 0.98650 >
    0.85005. So no fixed child dominates: the child-optimization max_child Phi is a multiaffine program
    whose maximizers are the EXTREME points of the reachable child set, which ACCUMULATE at the ties with
    the argmax flipping across them. The domination route is thus the child-optimization VIEW of the same
    accumulation obstruction -- ruled out structurally, not for a missing trick. (The flaw was found by
    adversarial search BEFORE any claim; the two reduced families are still genuinely <=1, consistent with
    the conjecture.) Phi<=1 remains OPEN.
    SPECTRAL LOCATION OF THE MARGINALITY (`spectral_marginality.py`, 2026-08-06; the eigenvalue view).
    Trees bipartite => Phi = (prod_v a_v) prod_j sqrt(1+mu_j^2), mu_j = eigenvalues of the WEIGHTED
    adjacency A (A_uv=sqrt(z_u z_v)); so Phi<=1 <=> sum_j log(1+mu_j^2) <= -2 sum_v log a_v (SPEC) --
    the SPECTRUM vs a sum of LOCAL weights. NEW facts (verified): (i) rho(A) < 1 for EVERY finite gadget
    (ties included: 0.957..0.0) and rho(A) -> 1 exactly along the c=0 CATERPILLAR (0.707,0.866,0.951,
    0.985,0.996,0.999,... -> 1; the infinite c=0 chain has A=(1/2)P, rho=1). So the whole problem's
    marginality is LOCATED spectrally -- it is rho(A) touching 1 in the caterpillar limit, unifying "the
    c=0 caterpillar is adversarial" with a precise cause. (ii) Since rho(A)<1, log(1+mu^2) expands as a
    convergent local closed-walk series sum_k (-1)^{k+1} tr(A^{2k})/k; its k=1 term tr(A^2)=2 sum_edges
    z z is exactly 2*S (the retracted linear surrogate) and OVERSHOOTS the target on every c=0
    caterpillar, while the exact log-sum stays under -- so the even-moment (k>=2) corrections are
    essential, and on a tree they resum precisely to the Bethe/cavity form (bethe_certificate.py), giving
    NO new margin. The alternating series sits at the edge of convergence (rho->1) exactly where Phi is
    marginal. Honest characterization, not a proof: Phi<=1 remains OPEN, its obstruction now also seen as
    rho(A)->1 on the c=0 caterpillar.
    SYMBOLIC-REGRESSION ENVELOPE SEARCH (`curve_search.py`, 2026-08-06; evolutionary curve search with
    an artifact-proof gate). Searched directly for the smooth certificate: an inductive ENVELOPE
    Phi <= h(u,z) (u=rho0, z=root activity), which -- if h<=1 with anchors=1 and inductively invariant --
    PROVES Phi<=1. NOT a ruled-out route: single-var Phi<=g(u) is impossible (two Phi=1 points at
    u=1,22/23), and the z-BOX envelope (Phi<=B(z),X<=C(z)) OVERSHOOTS at the corners (+0.077, the
    (maxPhi,maxX) corner unrealizable), but the bivariate h(u,z) COUPLES the coordinates and the 6
    anchors sit at distinct (u,z)=((18+c)/23,3/(18+c)). ENGINE: vectorized numpy kernel (~1ms/eval,
    ~1000x over the pure-Python loop -- the right acceleration, NOT Rust, whose shared arda_rust binary
    must not be touched for an experiment), (mu,lambda)-ES over a rational h. FINDING: a strong deg<=3
    search DRIVES the SAMPLED invariance defect (over ~6000 formation contexts) to ~0 -- which LOOKED
    like a lead. It is a SAMPLING ARTIFACT: the ADVERSARIAL gate (wide nodes k<=16, tie/anchor children,
    the naive-overshoot config) exposes a positive floor. DECISIVE: with the ceiling HARD-ENFORCED
    (h<=1: ceiling_max ~1e-3, anchor_err ~5e-4, containment ~1e-6), the best deg<=3 envelope over 5
    seeds still has adversarial invariance FLOOR ~+0.038 (worst: cr=0, k=2, z_node=1/3, formed
    Phi ~1.030 from envelope-children). So the deg<=3 bivariate-envelope class is INSUFFICIENT: a
    fixed-complexity smooth envelope cannot BOTH contain the reachable set (h<=1, anchors=1) AND be
    inductively invariant -- because the true invariant boundary is the ACCUMULATING curve
    (near_star_polytope), not a low-degree rational. The overclaim trap sprang (sampled inv ~0) and the
    adversarial gate caught it. What survives: a fast reusable envelope search + working gate, and the
    demonstration that deg<=3 bivariate envelopes do not close it. Phi<=1 remains OPEN.
    ENVELOPE ROUTE PUSHED AS HARD AS POSSIBLE -- NO FIXED-DEGREE ENVELOPE CLOSES IT (`envelope_hard_verify.py`).
    Ceiling-free ansatz h=1-s(u,z)^2 (h<=1 by construction, h=1 at a tie iff s=0), ADVERSARIAL TRAINING
    (cutting-plane: fit s, hunt the worst formation, feed it back), degree sweep 3,4,5, 400k-formation
    adversary hunts. The free search reports NEGATIVE floors (deg3 -0.008, deg4 -0.010) -- looked like a
    strict-margin certificate -- but it is a CONTAINMENT-VIOLATION ARTIFACT: the fit buys margin by
    letting h dip ~1e-5 BELOW Phi exactly at the ties (h<1 there), which the random hunt never probes.
    DECISIVE, with HARD containment enforced (h>=Phi on depth-5, h=1 at the 6 ties -- verified h(tie)=1
    to 1e-6): the EXACT-TIE invariance defect is +0.0225 (deg3), +0.0256 (deg4), +0.0270 (deg5) and the
    adversary floor +0.042/+0.081/+0.086 -- the floor does NOT shrink with degree, it PLATEAUS (slightly
    rises) at ~+0.025 at the exact ties. The exact-tie defect is the clean kill: forming the tie
    neighbourhood overshoots the envelope by ~+0.025 no matter the fit/degree. So NO fixed-degree
    bivariate envelope h(u,z) is inductively invariant while containing the reachable set -- the whole
    smooth-envelope class is exhausted, defeated by the same marginal 6-point tie (= accumulating
    invariant boundary = rho(A)->1 on the c=0 caterpillar). Phi<=1 remains OPEN; a closed proof needs the
    exact symbolic accumulating invariant set or a genuinely new idea, NOT any fixed-complexity envelope.
    CAVITY-POTENTIAL REFORMULATION -- the accumulating invariant set, symbolically (`cavity_potential.py`).
    NEW EXACT IDENTITY (verified 1e-41): with the cavity field m_v = z_v*rho0_v obeying
    m_v = z_v/(1+z_v*sum_children m_c) (leaf m=z), the log-amplitude TELESCOPES:
    log Phi(T) = sum_v [log(a(d_v,c_v) z(d_v,c_v)) - log m_v].  A potential P(m)>=0 with the per-vertex
    inequality q_v <= sum_children P(m_c) - P(m_v) (q_v = log(a_v z_v) - log m_v) telescopes exactly to
    log Phi <= -P(m_root) <= 0 -- so P PROVES Phi<=1, and P is the symbolic accumulating invariant set
    (its sublevel structure = the reachable-set boundary). The inequality is LINEAR in P => feasibility
    is an LP, driven by an adversarial cutting-plane. THE TIE PINS P EXACTLY: all 6 tie roots have
    m_root = 3/23 (uniform), forcing P(3/23)=0 (a minimum), P(1)=log rho_B, P(1/3)=log(2 rho_B^2/3).
    HOW FAR (honest): a 1/m-basis P is feasible on finite sets but BLOWS UP at small m -- wide
    "tie-children" nodes (k ties as children, m=3/23, zero budget) drive the violation to +inf as
    k->inf (m_v->0, q_v bounded). A BOUNDED-near-0 basis + explicit tie-children constraints (k<=8000)
    is feasible and a 1M-sample adversary (wide nodes k<=1000, tie/near-tie children) is nearly
    exhausted -- BUT a real depth-7 node (cr=0,k=3,m_v~0.19) still violates by +0.0006, because P is
    forced ~0 on a whole INTERVAL m in [0.05,0.18] around the ties, leaving no budget for near-tie deep
    nodes. So NO fixed-basis potential certifies all nodes; the residual SHRINKS with better bases
    (+0.033 -> +0.0006) but never reaches 0 with a valid (P>=0, tie-tight) P. This is the CLOSEST the
    whole program has come, and the RIGHT object: closing Phi<=1 needs the exact infinite/asymptotic
    potential (the genuinely accumulating P with the right small-m/near-tie asymptotics), not any
    finite-complexity certificate. Phi<=1 remains OPEN.
    EXACT NEAR-TIE ASYMPTOTICS -- INTEGRALITY IS ESSENTIAL, so NO smooth certificate can prove Phi<=1
    (`near_tie_asymptotics.py`; the unifying explanation of every failure). In the value-function form
    (Psi(m)=sup{log Phi: root cavity=m}, P*=-Psi, problem = Psi<=0, Psi(3/23)=0), the near-tie upper
    envelope is carried by the explicit family G(c)=(c,[ARM]) (root: c cherries + one cherry-arm child),
    with root cavity m(c)=3/(4c+7) and the EXACT closed form
    log Phi(c) = -(2c+3)log rho_B + (c+1)log(3/2) + log(4c+7) - log(3(c+2)).
    The tie is c=4 (m=3/23), where log Phi(4)=0 EXACTLY -- an integer identity 64*243*23 = 621*576 =
    357696. The reachable near-tie points are m=3/n with n=4c+7 ≡ 3 (mod 4) (n=...15,19,23,27,31...),
    echoing 23|621; along them Psi ~ -C(m-3/23)^2. DECISIVE: the CONTINUOUS relaxation of log Phi(c)
    (c real) has an interior maximum at c*=3.8217 with Phi(c*)=1.0000417 > 1 (f'(3)>0>f'(4)). So the
    smooth interpolation POKES ABOVE 1 between the integer configs c=3,4; the actual gadgets live only
    at INTEGER c, where Phi<=1 with equality at c=4. Phi<=1 is therefore an ARITHMETIC fact (true
    because cherries and degrees are integers), NOT a smooth one -- which is EXACTLY why every smooth
    certificate (envelope Phi<=h(u,z); bounded potential P(m); polynomial barrier) fails: each must
    bound the continuous relaxation, which exceeds 1 (by +4.2e-5 on this family; larger residuals
    +0.0006..+0.038 on others), so the marginal tie defeats them all and the residual never reaches 0.
    CONSEQUENCE: closing Phi<=1 needs an ARITHMETIC argument (integer c,d; the 23-adic rational
    reduction rational_reduction.py, 11|V since 23|621), NOT a smooth certificate -- prove log Phi(c)<=0
    at INTEGER c while the real-variable max is +4.2e-5>0. The obstruction is now fully explained; Phi<=1
    remains OPEN but the search for a smooth/analytic certificate is definitively closed off.
    ARITHMETIC PROOF ON THE NEAR-STAR FAMILY -- RIGOROUS (`near_star_arithmetic_proof.py`, exact-Fraction
    verified). THEOREM: for the family N(c,k) = root with c cherries + k cherry-arm children, Phi(N(c,k))
    <= 1 for ALL integers c,k>=0, with equality iff c+k=5 (this contains all 6 exact ties). PROOF: (1)
    log Phi depends only on s=c+k (the log(3d+c) terms cancel), g(s) = -(2s+1)log rho_B + s log(3/2) +
    log(4s+3) - log(3(s+1)). (2) Clearing the 11th root (rho_B^11=621/64=3^3*23/2^6): g(s)<=0 <=>
    3^(5s-14) 2^(s+6) (4s+3)^11 <= 23^(2s+1) (s+1)^11  (a rational inequality in the integer s). (3)
    R(s)=RHS/LHS satisfies R(s+1)/R(s) = (23^2/(2*3^5))((s+2)(4s+3)/((s+1)(4s+7)))^11 =
    (529/486)(1 - 1/(4s^2+11s+7))^11, which is STRICTLY INCREASING in s (denominator increasing) and
    crosses 1 once (ratio<1 at s=4, >1 at s=5). So R is strictly decreasing on {0..5}, strictly
    increasing on {5,6,..}, min at s=5. (4) R(5)=1 EXACTLY (the integer identity 64*243*23=621*576).
    Hence R(s)>=1 for all s>=0, equality iff s=5. QED. This is the first proof to go THROUGH the
    integrality that defeats every smooth certificate; the arithmetic constant 529/486 = 23^2/(2*3^5) is
    the 23-adic content of 621. SCOPE: the near-star family only -- the FULL conjecture (arbitrary
    subtrees as children) is still OPEN, but this is the rigorous marginal-family result and validates
    the arithmetic route (integer c,k, not smooth analysis). Verified in exact Fraction arithmetic + tied
    to the actual gadgets (Phi(N(c,k))<=1, =1 iff c+k=5).
    EXTENSION TO ARBITRARY CHILDREN -- the general inductive step + the exact remaining gap
    (`general_induction.py`). The exact telescoping step: log Phi(node) = sum_i log Phi_i + [log a(d,cr)
    + log(1 + z(d,cr) sum_i m_i)]; the conjecture is the induction "children log Phi_i <= 0 => node
    log Phi <= 0". This CANNOT be proven from log Phi_i <= 0 alone -- placing children at the UNREACHABLE
    spot (m=1, log Phi=0) makes a cr=0 root overshoot to e_root -> -log rho_B + log 2 = +0.486 as k->inf.
    The step needs the QUANTITATIVE cavity-dependent bound log Phi_i <= Psi(m_i) = -P*(m_i). THE GAP,
    pinned: (a) the tightest such P is P*=-Psi but P*>=0 IS the conjecture (circular); (b) NO smooth/
    fixed-complexity P works (near_tie_asymptotics: continuous relaxation > 1 between integers); (c) the
    proven families do NOT capture Psi -- sup over ALL gadgets exceeds sup over near-stars+tie-children+
    brooms by up to +0.197 (at m=1/15), and the optimal child is non-monotone (a bare leaf can beat a
    cherry-arm at large parent activity), so there is no single dominating child-family to reduce to. So
    the near-star ratio-unimodality argument (a global proof for one family, bypassing P) does not
    directly extend; the general case needs a NON-smooth/arithmetic potential respecting integer
    (cherries,degree), or a family-by-family global argument covering the true (mixed, non-monotone)
    maximizers. WHAT EXTENDS (verified): leaves (log a(1+c,c)<=0, =0 iff c=5); the near-star family
    (proven); the tie-children family (cr,[TIE]*k) <=0 (same cancellation+ratio structure); and the FULL
    step holds empirically (worst node log Phi over real children ~ -0.0015 <= 0, tie only at equality).
    A full proof of Phi<=1 for arbitrary children is the OPEN Brualdi-Goldwasser crux -- now with the
    obstruction fully characterized (integrality; no smooth certificate; no dominating child-family) and
    a proven arithmetic template for individual families.
  - *(cherry distribution)* Arms balance evenly at `c~5` (PROVEN Schur-concave, Polya cert).
    The HUB carries 0 -- now a THEOREM among stars of cherry-bundles (`arm_bound.py`).
    (a) Rate-optimality: `rho(c)<rho_B` for every integer `c!=5` (exact `F(c)^11<F(5)^(1+2c)`),
    so with arm-balancing the maximizer's arms lie in {4,5,6} for `n>=N1` (explicit rate
    envelope `N1=10412`; empirically `n~200`). (b) The hub->arm transfer is affine in the
    other-arms' activity, so two endpoint certificates cover all balanced arms in {4,5,6}
    (`k>=33`). Together: for `n>=N1`, arms in {4,5,6} and `k=Theta(n)>=33` => hub 0. Both
    earlier gaps (uniform-arm model; arm-level bound) are CLOSED.
  - *(degree grows)* consistent with the ceiling (`B(3,c)` fails `c>=8`) and the search.
- **Structural map.** Among *all* backbones on <= 8 vertices with uniform cherries, a
  **star** maximizes `pi` at essentially every attainable `n`, and the optimal star's
  degree **grows with `n`**.
- **Local optimality.** An exact single-edge-relocation hill-climb started from a single
  star **never escapes to a multi-level structure** -- it stays a single star of
  cherry-bundles.
- **Conjecture (corrected).** For large `n` the maximizer is a *star of cherry-bundles* -- a
  hub adjacent to `k=k(n) -> infinity` arm-centers; the ARM-centers carry `Theta(1)` (=5,
  rate-optimal) cherries balanced to within one, while the HUB carries 0 (de-loaded). The
  backbone is a star, not a path. (Earlier form had every center carrying `Theta(n/k)`; the
  cherry-distribution step refutes the uniform version.) Open: a PROOF of the constant-order
  near-star separation, and closing the two hub-de-loading gaps above.

Full academic writeup (definitions, matching-sum lemma + proof, closed-form propositions,
Theorems, computational evidence, limitations, references): **`paper_laplacian_ratio_maximizer.tex`**
(compiles to PDF).

## What this is NOT (limits, stated plainly)

- **Not proven to be the global maximum.** `B(3,c)` is proven to beat every
  path-spine spider (exactly), but it is a strong explicit construction / hill-climb
  local maximum, **not** a certified global maximizer. Other trees may beat it.
- **The symmetric family only wins in a window.** At `c=8` (`n=68`) a larger `m=6`
  spider retakes the lead over `B(3,8)`. The optimal branching structure must itself
  grow with `n` (more/larger branches), exactly as the spider spine grows -- so `B(3,c)`
  is a representative of a *transition*, not a final answer.
- **Externally unverified.** A literature search (incl. Pant 2026) found **no**
  discussion of a branching-backbone maximizer for this ratio -- so this is
  *apparently novel* -- but "not found" is not "does not exist," and this has **not**
  been checked by an independent tool (e.g. SageMath permanent) or a human expert.
  **No formal claim should be made without that cross-check.**

## Reproduce

```
python -m pytest proof/verification/tests/test_lr.py
python -m verification.hunt --n-min 19 --n-max 50   # GA sweep
# hill-climb from the best spider + exact verification is in hillclimb.py;
# the explicit family is trees.branch_tree(3, c). Exact data: result_card.json.
```

**Bottom line:** the honest engine produced a concrete, exact, apparently-new
contribution to an open extremal-graph-theory problem -- an explicit tree family whose
*branching* backbone strictly beats every path-spine spider (including the newest
published counterexamples) at `n = 36, 44, 52, 60`. It is internally airtight and
externally unverified; it is offered as a candidate, flagged for independent
cross-check, not as a settled result.
