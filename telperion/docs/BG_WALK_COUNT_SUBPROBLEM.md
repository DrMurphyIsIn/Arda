# Walk-count sub-problem — the combinatorial core of the capacity upper bound (route b)

> **Port note (2026-08-30).** The kernel-gated deliverable of this arc — the flag-discharge `m_2`-cut
> certificate — lives at `examples/bg_flag_discharge/` (emitter `src/telperion/flag_discharge.py` +
> `generate.py` → `lean/BGFlagDischarge.lean`), kernel-checked by the `bg-flag-discharge-compiles` job of
> `telperion-lean-e2e` (`lake build`). The W-sections below are the faithful **research record of the
> original branch development**; where they mention a monolithic `rh_lean` library / `build.py` FROZEN dict
> / `RH.BGFlagDischarge`, that was the branch's assembly, now superseded by this per-example project on
> `main`. The mathematics and the frozen rational dual are unchanged. `conjecture1_proved = False`.

**Status:** deliberate research effort, the reduced sub-problem of `BG_CAPACITY_ATTACK_SPEC.md` route (b).
It replaces the transcendental free-energy by a **finite, polynomial, local** object (spectral moments =
weighted closed-walk densities), where route (b) earns its keep over the failed local certificate (a).
`conjecture1_proved = False`.

## The reduction

`F(T) = (1/n)log(per(L)/∏deg) = ½∫log(1+u)dμ_{N²}(u)`, `u=λ²∈[0,1]`, `μ_{N²}` = spectral measure of
`N²`, `N=D^{-1/2}AD^{-1/2}`. Bound `½log(1+u) ≤ Σ_{k=1}^K c_k u^k` by a fixed polynomial envelope (valid
on `[0,1]`; SOS-certifiable, kernel-checkable). Then

    F(T) ≤ Σ_{k=1}^K c_k m_k(T),   m_k(T) := (1/n) Tr N^{2k} = normalized weighted closed-walk density.

`m_k(T)` is **local & polynomial**: `Tr N^{2k} = Σ_{closed walks of length 2k} ∏_{steps a→b} 1/√(deg_a deg_b)`;
on a tree every closed walk retraces edges, so `m_k` is determined by the `k`-neighborhoods. **Goal:** bound
`Σ_k c_k m_k(T) ≤ log ρ* + (1/n)log poly(n)` for all trees — a moment optimization, not a transcendental one.

## Key structural findings (2026-08-29)

**1. Different trees maximize different `m_k`** (exhaustive n=12): `m_1` by a hub tree (degseq [4,3,2,2]),
`m_2` by [3,2,2,2], `m_3`,`m_4` by the **path** [2,2,2,…]. The path has the highest *high* moments
(`m_2`=0.378, `m_3`=0.316 vs caterpillar 0.308, 0.198) but a *lower* free-energy (rate 1.210 < 1.2276).

**2. The extremal caterpillar maximizes NONE of the `m_k` individually** — so "bound each `m_k`" is the
wrong sub-problem (it gives the path/hub extremes, not `ρ*`).

**3. The free-energy is the balanced ALTERNATING combination.** The envelope coeffs alternate sign
(`c ≈ [+0.500, −0.242, +0.124, −0.035]`), so `Σc_k m_k = c_1 m_1 − |c_2| m_2 + |c_3| m_3 − …`. The path's
large `m_2` is *penalized* by `−|c_2|`; the caterpillar balances the alternation and maximizes the
combination. This is the finite-side shadow of the free-energy concavity.

## The precise sub-problem (moment-body / SDP)

Let `𝓜_K` = the convex body of achievable moment vectors `(m_1,…,m_K)` of **tree** spectral measures
`μ_{N²}` (a probability measure on `[0,1]`). Prove

    max_{m ∈ 𝓜_K}  Σ_k c_k m_k  =  log ρ*  (+ finite-n correction),   attained at the ~7-arm caterpillar.

Two nested relaxations, in increasing strength:
- **(S1) Hankel/moment relaxation:** `m` = moments of *some* probability measure on `[0,1]` (Hankel PSD).
  Cheapest; test first — if `max Σc_k m_k` over Hankel-PSD `m` (with the tree bound on `m_1`) already
  equals `log ρ*`, the bound is a clean SDP/SOS certificate (kernel-gateable). Likely too loose alone.
- **(S2) Tree walk-count constraints:** the additional inequalities that tree closed-walk densities
  satisfy (beyond Hankel PSD) — e.g. `m_1 = (2/n)Σ_e 1/(deg_i deg_j)` and higher local identities. These
  are the "tree-specific" cuts that tighten (S1) to the true `𝓜_K`.

## Milestones

- **W1.** Fix the degree-`K` envelope `Σc_k u^k ≥ ½log(1+u)` on `[0,1]` as an exact SOS certificate
  (univariate, kernel-checkable). K=4 already gives ~4-digit tightness at the caterpillar.
- **W2.** Bound `max_T m_1(T) = max_T (2/n)Σ_e 1/(deg_i deg_j)` in closed form (the entry moment; pure
  degree-sequence optimization under the tree handshake `Σdeg = 2n−2`).
- **W3.** Solve/relax (S1): the Hankel-PSD moment SDP with the functional `Σc_k m_k`; measure the gap to
  `log ρ*`. If closed → SDP proof; if not → identify which tree cut (S2) is missing.
- **W4.** Prove the needed (S2) tree walk-count inequalities (local, per-neighborhood), and assemble the
  bound. **W5.** Add the finite-`n` `poly(n)` correction (the small-n moment excess) for the exact
  statement.

## Why this is the right level

The moments are **local and polynomial**, so bounding them is combinatorial (walk counts / degree
sequences), not transcendental — sidestepping (a)'s collective wall (which lived in the per-vertex
`log a_v`) and Koiran's SOS no-go (which blocks certifying the *permanent*, not moment inequalities).
The alternating-sign structure is exactly the "discharging built into the dual" that (a) lacked. The
open risk is whether (S1)+(S2) close *tightly* to `ρ*^n·poly(n)` — real research, but now a finite
moment/SDP problem rather than an infinite-dimensional one.

## Reproduce / verify hooks

`m_k(T) = (1/n)Σ λ_i^{2k}`, `λ` = eigenvalues of `N=D^{-1/2}AD^{-1/2}`; envelope via `linprog`/SOS on
`½log(1+u)−Σc_k u^k ≥ 0` on `[0,1]`; caterpillar builder + `girardeau.hard_core_boson_partition` and
`rooted_phi._all_tree_edges(n)` (see `BG_TRUE_MAX_PROBE.md`, `BG_CAPACITY_ATTACK_SPEC.md`).
Runnable: `PYTHONPATH=telperion/src python3 telperion/docs/bg_walk_counts_reproduce.py` (W5 findings below).

## W5 (2026-08-29): the target is a bulk free-energy DENSITY, not a finite `max_T` — and the certificate is an edge-discharging potential

Attacking the W4d′ proof surfaced a scoping error that reshapes the statement (exact-rational, reproducible).

**(i) `max_T F(T)` is at the single edge, and `per/∏deg ≤ ρ*^n` is FALSE.** With `F(T)=(1/n)log(per(L)/∏deg)
= ½∫log(1+u)dμ_N`, exhaustive enumeration gives `max_{|T|=n} F(T)` **strictly decreasing FROM ABOVE** to
`log ρ* = 0.205098`: n=2 `½log2 = 0.34657` (single edge), n=3 `0.23105`, … n=13 `0.20927`, with even/odd
oscillation. So **every finite tree has `F > log ρ*`**; the sup over all finite trees is the single edge
(`(per/∏deg)^{1/n} = √2 > ρ*`), and `per/∏deg ≤ ρ*^n` is violated (ratio `1.327` at n=2). `ρ*` is a
**thermodynamic-limit growth rate** (the free-energy-density sup over tree-realizable spectral measures
`μ_N`), approached from above — NOT a finite maximum. The finite bound is `per/∏deg ≤ C·ρ*^n`, `C≥1.327`.

**(ii) Consequence for W4d′.** "The caterpillar maximizes `G(T)=Σc_k m_k` over trees" holds only
**asymptotically / among bulk-dominated families** — small trees exceed it exactly as they exceed `F`. The
correct target is the **bulk (infinite periodic caterpillar) free-energy density**, with a *subextensive
surface term* for finite trees. Confirmation: the naive discharging LP over *all* local profiles returns the
weak bound `B = ½log2` (correct but not `log ρ*`), because it must cover the single-edge profile
(a degree-1 vertex adjacent to a degree-1 vertex — which occurs *only* in `K₂`).

**(iii) The finite-`n` maximizers are explicit — the cherry-parity oscillation.** `argmax_{|T|=n} F` is the
length-2-arm caterpillar: a single degree-`k` hub with `k` cherry-legs for odd `n` (n=13 → deg-seq
`(6,2,2,2,2,2,2,1,…)`, i.e. deg-6 hub + 6 length-2 arms; n=11 → deg-5 hub; n=9 → deg-4), and **two** hubs for
even `n` (n=10 `(3,3,2,…)`, n=12 `(4,3,…)`, n=14 `(4,4,…)`). These converge to the periodic multi-hub
caterpillar (matches the cherry-parity memory).

**(iv) The certificate object — an antisymmetric edge-discharging potential.** Verified exact per-vertex
LOCAL formulas (0 mismatches vs `Tr(N^{2k})/n`, all 47 trees n≤8):
`m_1 = (1/n)Σ_v S_v/d_v`, `m_2 = (1/n)Σ_v[2 S_v²/d_v² − Q_v/d_v²]`, `S_v=Σ_{a~v}1/d_a`, `Q_v=Σ_{a~v}1/d_a²`.
Both — and every `m_k` — are **averages of a local 1-neighbourhood degree functional**, so `G(T)=(1/n)Σ_v g(v)`
with `g(v)=Σ_k c_k L_k(v)`. The upper-bound certificate is therefore an **antisymmetric potential
`w(x,y)=−w(y,x)`** on degree-pairs with a per-vertex inequality that telescopes on any tree
(`Σ_v Σ_{a~v} w(d_v,d_a)=0`):

    prove   g(v) − Σ_{a~v} w(d_v, d_a) ≤ log ρ*   for BULK profiles,   tight at the three caterpillar
    vertex types (spine deg `a+2`, arm-middle deg 2, leaf deg 1),   with boundary excess O(surface)=o(n).

This is structurally the **folded cavity-potential / discharging certificate** that closed the Laplacian
`Φ≤1` crux — the honest, well-posed route-(b) target. The `2c₂S_v²/d_v²` cross-term (pairwise in the
neighbour degrees) is the residual "collective" piece the potential must absorb. `conjecture1_proved = False`.

**Revised milestones.** W1–W3 unchanged. **W4** → prove the per-vertex *bulk* discharging bound (find `w`;
the finite-degree feasibility LP is the entry probe). **W5** → the surface term `per/∏deg ≤ C·ρ*^n` and the
`lim` statement (superseding the old "poly(n) correction", now understood as the from-above convergence).

## W6 (2026-08-29): 1-neighbourhood K=2 discharging does NOT close — it plateaus at the small-path free energy

Ran the discharging LP (`min B` over antisymmetric `w(x,y)` s.t. `g(v)−Σ_a w(d_v,d_a) ≤ B` for every
bulk-realizable local profile, excluding all-leaf/star-center neighbourhoods). **Result: `min B = 0.23099`,
a hard floor `+0.0259` above `log ρ* = 0.20510`.** It is pinned *exactly* — by hand — by a single profile
pair (independent of the degree cap):

- leaf `(D=1, {2})`:            `g = 0.21164`, constraint `g − w(1,2) ≤ B`;
- path-interior `(D=2, {1,2})`: `g = 0.25034`, constraint `g + w(1,2) ≤ B`.
  Adding: `B ≥ ½(0.21164 + 0.25034) = 0.23099` — matching the LP to 5 digits.

So the **linear (discharging) relaxation alone has an integrality-gap-like plateau at ≈ the small-path
free energy** (`F(P₃)=0.23105`, `F(P₄)=0.22907`). The independent-profile relaxation cannot tell "these two
profiles coexist only in a low-density path" from "they tile a high-density tree", so it over-counts. The
missing constraint is exactly **measure-realizability = the Hankel-PSD moment body** (ingredient 2): the
tree spectral measure `μ_N` cannot simultaneously put the mass on `(1,{2})` and `(2,{1,2})` that the
relaxation assumes. This concretely **validates the plan's emphasis on the moment-SDP Hankel constraints
over pure discharging** — the linear cuts (ingredient 3) need the Hankel PSD (ingredient 2) to close.

**Next probe:** (a) K=4 discharging (add `m_3,m_4` local terms — 2-/3-hop neighbourhoods, a tighter
envelope) to see how far the plateau drops; (b) couple the discharging LP to the Hankel-PSD moment
constraints (the moment-SDP proper) — the combination is the actual route-(b) certificate.
`conjecture1_proved = False`.

## W7 (2026-08-29): three probes — Hankel + the `m₂` cut closes it; the cut is measure-realizability, not elementary convexity

Ran all three follow-ups. They converge: **the sole load-bearing lever is the tree cut `m₂ ≥ φ(m₁)`, and
it is a measure-realizability fact — exactly the Hankel/flag-algebra structure, not local discharging.**

**(a) Moment-SDP proper** (`max Σc_k m_k` over measures on `[0,1]`; Hankel moment + localizing matrices;
cvxpy/SCS). Staged:
- Hankel-PSD only → `½log2 = 0.34657` (gap **+0.141**): the single-atom `δ₁` (= the single edge, a genuine
  measure) is admissible at *every* Lasserre order, so pure measure constraints never remove it.
- `+ m₁ cut` → no change (`max_T m₁ = 1` is realized by `δ₁`).
- `+ m₂ ≥ φ(m₁)` (convex caterpillar-boundary envelope, 9 supporting tangents) → **gap +0.0010** (K=4 & K=6),
  with the argmax **pinned at `m₁≈0.523` = the caterpillar**. Residual `+0.001` = envelope + tangent
  linearization order (matches prior W4 `+0.0008`). **So Hankel + the `m₂` cut closes; the cut is the
  load-bearing constraint.**

**(b) K=4 discharging.** Per-vertex `g_K(v)=Σc_k(N^{2k})_{vv}`. The tighter K=4 envelope makes the **1-hop
antisymmetric potential TIGHT at the caterpillar**: `w=(w₁₂,w₂,ₕᵤᵦ)=(−0.0057,+0.0082)` sends *all three*
vertex types (leaf/arm-mid/hub) to exactly `log ρ*` (max residual `3·10⁻⁵`; K=2 was not tight, residual
`8·10⁻³`). **But the global plateau barely moves** — the P₄ binding-pair floor is `0.22913` (K=4) vs
`0.23099` (K=2), still `+0.024` above `log ρ*`. Higher order makes the extremizer locally certifiable but
does **not** remove the path-profile floor: the residual gap is measure-realizability, not locality/order.

**(c) The `m₂ ≥ φ(m₁)` cut is NOT elementary convexity.** From the exact local formula
`m₂ = 2·avg(x_v²) − avg(Q_v/d_v²)` (`x_v=S_v/d_v`, `Q_v=Σ1/d_a²`), Cauchy–Schwarz+Jensen give only
`m₂ ≥ 2m₁² − m₁` — valid (0 violations / 2287 trees) but **useless at the band** (`0.021` vs true `0.308`).
Reason: at the caterpillar the `x_v` have **negligible variance** (`avg(x²)−m₁² = 0.0015`), so
`m₂ ≈ 2m₁² − avg(Q_v/d_v²)`, and the cut is really an **upper bound on `avg(Q_v/d_v²)` at fixed `m₁`** —
which the elementary `avg(Q/d²) ≤ avg(x/d)` overshoots (`0.366` vs actual `0.233`). The sharp cut needs the
**joint degree-neighbourhood distribution**, i.e. a local **flag-algebra / moment SDP on the degree
distribution** (dual-certifiable with the same Telperion Hankel/SOS machinery, ingredient 2), not a
standalone inequality.

**Consolidated state of route (b).** The certificate architecture is **Hankel-PSD (measure realizability)
+ the `m₂ ≥ φ(m₁)` cut**; this closes to `+0.001` (envelope order). The single genuinely-open theorem is
the cut itself — the caterpillar minimizes `m₂` (equiv. maximizes `avg(Q_v/d_v²)`) among trees at fixed
`m₁` in the extremum band — and all three probes show its proof is a **degree-distribution moment/flag SDP
with a dual (SOS) certificate**, NOT rearrangement (caterpillar interior, W5) and NOT elementary convexity
(too weak, W7c). Reproductions: `bg_moment_sdp.py`, `bg_k4_discharge.py`, `bg_c_convexity.py`.
`conjecture1_proved = False`.

## W8 (2026-08-29): the mass-transport flag-LP CLOSES the m₂ cut — explicit, verified dual certificate

The W7 diagnosis (the discharging gap is *measure-realizability*) is now made precise and largely resolved.
Both moments are **linear** in the vertex-type distribution `π(t)`, `t=(d;{e_1..e_d})`:
`m₁=Σπ(t)x(t)`, `m₂=Σπ(t)(2x(t)²−q(t))`, `x(t)=(Σ1/e_i)/d`, `q(t)=(Σ1/e_i²)/d²`. So the cut is a **linear
program** (no SDP needed at this order): `min m₂ s.t. m₁ = M` over `π ≥ 0` with the realizability
constraints a real tree must satisfy:
- normalization `Σπ = 1`;
- tree handshake `Σπ(t)·d(t) = 2` (bulk mean degree);
- **mass transport / unimodularity**: for every degree pair `d<e`,
  `Σ_t π(t)[cnt_e(t)·1{deg=d} − cnt_d(t)·1{deg=e}] = 0` (the `(d,e)`-edge count is equal from each side).

**Result — it closes.** The independent-profile discharging floored at `0.231` (W6); adding mass transport
lifts `min m₂` onto the caterpillar boundary across the whole band: at the caterpillar's own `m₁`,
`min m₂` equals the caterpillar `m₂` to `~10⁻⁴` (DMAX=7 `+1.4e−4`, DMAX=8 `+1.1e−4`, **DMAX=9 `+0.9e−4`**,
shrinking), and `min m₂(M)` tracks `φ(M)` for `M∈[0.50,0.54]`.

**The LP dual IS the certificate (verified).** The equality-constraint multipliers give a per-type
inequality — valid over **all 3431 types** with worst slack `−5.6e−17` (machine zero):

    m₂-contribution(t) = 2x(t)²−q(t)  ≥  β₀ + β₁·d(t) + β₂·x(t) + Σ_{a~v} w(d, e_a),

with `w(d,e) = −w(e,d)` the **antisymmetric discharging potential read off from the mass-transport duals**
(e.g. `w(1,2)=0.00066`, `w(2,7)=0.00527`, `w(2,3)=0.06539`). Summed over a tree the `w`-terms telescope to
0, giving `m₂ ≥ β₀ + 2β₁ + β₂·m₁` — a certified linear lower bound tight at the caterpillar. This is
exactly the folded discharging potential, now **valid** because the mass-transport duals supply the
coupling the independent relaxation lacked.

**Honest caveat — the 1-hop LP is a relaxation, not exactly tight.** Mass transport + mean-degree-2 are
*necessary* for trees, not sufficient, so `min m₂` is a valid *lower* bound on the true tree-min and its
gap grows mildly as the degree cap admits more types (DMAX=10 → `+3.0e−3`, up from `0.9e−4`). So the pure
1-hop flag-LP certifies `m₂ ≥ φ(m₁) − O(10⁻³)`. Closing the residual to *exact* tightness needs
**higher-order flag constraints — Hankel-PSD on the degree-type moments (the flag-SDP)** — the same
`HankelJensenCertificate` machinery as the spectral side.

**Route-(b) architecture, now concrete.** The full certificate is two coupled Hankel/SOS-dual objects:
(1) the **spectral** moment-SDP on `m_k` (§W7a) — Hankel-PSD + the `m₂` cut → `G ≤ log ρ* + O(10⁻³)`; and
(2) the **degree-distribution** flag-SDP (this section) — mass-transport LP + degree-moment Hankel →
certifies the `m₂ ≥ φ(m₁)` cut with the explicit antisymmetric-potential dual, tight at the caterpillar.
Both are kernel-gateable with Telperion's `hankel_jensen.py` + `cone.py`. The sole remaining work is the
Hankel tightening of (2) and rationalizing the duals into a kernel-checked emitter. Reproductions:
`bg_flag_lp.py` (LP + verified dual), `bg_flag_robust.py` (degree-cap robustness). `conjecture1_proved = False`.

## W9 (2026-08-29): the flag-LP CONVERGES to the true cut; the exact extremizer is a *generalized* caterpillar (refines W8)

Degree-cap convergence at fixed `m₁ = 0.520` sharpens the W8 caveat into a clean picture. `min m₂` decreases
monotonically with **shrinking** increments and converges from below:

    DMAX = 8, 9, 10, 11  →  min m₂ = 0.31246, 0.30784, 0.30485, 0.30251   (Δ = −4.6, −3.0, −2.3 ·10⁻³)

- **It is a valid, convergent lower bound**, not a blow-up: the LP over degree-`≤DMAX` type-distributions is
  a relaxation of the degree-`≤DMAX` tree min, and the sequence converges to the true `φ(0.520)`.
- **The true `φ(0.520) ≈ 0.302–0.305` is BELOW the uniform caterpillar `0.30841`.** A direct search over
  tree families finds **mixed-arm / multi-hub caterpillars beat the uniform a=7 caterpillar** at `m₁=0.520`
  (e.g. `a1=8/a2=7` blocks → `m₂≈0.305`), confirmed valid (`LP ≤ real tree` on matched `m₁`). So the exact
  extremal boundary is traced by **generalized (period>1, mixed-arm) caterpillars** — precisely the
  cherry-parity / multi-hub oscillation seen in the finite-`n` maximizers (W5(iii)).
- **W8's "tight to 10⁻⁴ at DMAX=9" was the converging sequence crossing the uniform-cat level** (`0.30784`
  vs `0.30841`) — a coincidence of that cap, not exact tightness against the uniform family.

**What this means for the proof.** The correct target is a **hierarchy limit**, exactly as W5 established
(`log ρ*` is a thermodynamic-limit growth rate, not a finite max). Route (b) is a **convergent family of
finite, kernel-gateable certificates** — indexed by SOS-envelope order `K` and flag/degree cap `DMAX` —
each proving `density ≤ log ρ* + ε(K, DMAX)` with `ε → 0`. The spectral moment-SDP (§W7a) supplies the
`m_k`-side bound; the flag-LP + its verified antisymmetric-potential dual (§W8) supplies the `m₂`-cut,
converging to the true generalized-caterpillar boundary (§W9). This is a complete proof **structure** for
the limit statement `sup_tree-density = log ρ*`, modulo (i) a standard hierarchy-convergence theorem and
(ii) Hankel/2-ball acceleration to make a *low* level tight enough for a compact emitter. The uniform
caterpillar is a near-optimal *reference*, not the exact extremizer. Reproductions: `bg_converge.py`
(degree-cap convergence), `bg_lp_vs_real.py` (LP ≤ real-tree, generalized-caterpillar search).
`conjecture1_proved = False`.

## W10 (2026-08-29): the flag-discharge cut, emitted as a kernel-gated Telperion certificate

The W8 dual is now a first-class Telperion emitter — `telperion/src/telperion/flag_discharge.py`,
`FlagDischargeCertificate`. `from_flag_lp(dmax, m1_target)` solves the mass-transport flag-LP, reads the
unimodularity duals as the antisymmetric potential `w(d,e)=−w(e,d)`, rationalizes them (denominator 720),
and sets `b0` to the **exact rational infimum** of the per-type residual, so the per-vertex inequality
`2x²−q ≥ b0 + b1·d + b2·x + Σ_a w(d,d_a)` holds by construction. `check()` re-verifies it **exactly** over
all 3431 degree-≤7 types (worst slack `0`, tight at the extremal caterpillar profile) plus antisymmetry.

The certified cut (dmax=7): `m₂(T) ≥ −1937/3600 + (13/360)(2−2/n) + (1081/720)·m₁(T)` for every tree with
max degree ≤ 7 — the `−2b₁/n` term is the W5 surface correction, the `Σw=0` telescoping + `Σd=2n−2`
handshake the assembly. At the a=5 caterpillar this gives `m₂ ≥ 0.32026` vs actual `0.32164` (gap `+0.0014`
= rationalization order). `lean_module()` emits a frozen module `examples/bg_flag_discharge/frozen/
BGFlagDischarge.lean` of `norm_num`-checked rational atoms (leaf/arm/hub/tight profiles), wired into the
`rh_lean` FROZEN library (`RH.BGFlagDischarge`, `build.py --check: OK`) so the kernel gate re-checks every
atom. Tests: `tests/test_bg_flag_discharge.py` (6, green) — exact check, antisymmetry, independent per-type
re-derivation, valid-lower-bound-at-caterpillar, atom shape, frozen==generated. Generator:
`examples/bg_flag_discharge/generate.py`. This is one finite level of the W9 convergent hierarchy, now
kernel-gateable end-to-end. `conjecture1_proved = False`.

## W11 (2026-08-29): the flag-SDP acceleration landscape — two natural lifts are dead, the correct object identified

Pushing on tightening the 1-ball flag relaxation (which loosens with the degree cap, W9) maps the hierarchy
cleanly — two obvious accelerations are provably wrong, which pins where the real work is.

**Linear pair / 2-ball lift is VACUOUS.** Add a joint edge variable `E(a,b) ≥ 0` (density of edges between
vertex-types a,b) with the marginals `Σ_{b: deg=k} E(a,b) = π(a)·cnt_a(k)` and symmetry `E(a,b)=E(b,a)`.
This adds **nothing** beyond 1-hop mass transport (`min m₂` unchanged to `10⁻⁵` at DMAX=4,5): given mass
transport the joint is always fillable (a feasible transportation problem), so the linear level-2 collapses
to level-1. The residual gap is therefore **not** closable by any linear flag constraints.

**Naive edge-matrix PSD lift is INVALID.** The genuine level is the SDP (reflection positivity), but the
*raw* edge-type matrix `E` is the wrong object: constraining `E ⪰ 0` **overshoots** — at DMAX=4/5 it returns
`min m₂ ≈ 0.400`, *above* a real tree (`best-real 0.368`), so it excludes real trees and is not a valid
lower bound. Direct check: the a=2 caterpillar's `E` has eigenvalues `{−68.7, −4.6, −0.009, 4.3, 24.6, 94.5}`
(min `−68.7`) — strongly indefinite, because `E` is a bipartite-like hub↔arm↔leaf adjacency (`±`-symmetric
spectrum), never PSD for real trees.

**The correct object.** Reflection positivity for graph limits (Lovász) is PSD on the moment matrix of
**rooted partial-subtree homomorphism densities** `M[F,F'] = t(F∪F' at the root, T)` — NOT the raw 2-point
adjacency. That matrix *is* PSD for every tree and is the valid flag-SDP tightening; building it (rooted-star
features + a reliable SDP solver — SCS/Clarabel suffice numerically, exact needs care) is the genuine
remaining construction. Until then the sound finite certificate is the degree-capped 1-ball emitter (W10),
valid for max-degree ≤ dmax, one convergent-hierarchy level (W9). Reproductions: `bg_level2.py` (linear lift
vacuous), `bg_psd_lift.py` (naive PSD overshoots), plus the `E`-indefiniteness check. `conjecture1_proved = False`.

## W12 (2026-08-29): the finite flag-SDP provably cannot close it — the gap is measure-extremality (why route b is a hierarchy)

Building the reflection-positive moment matrix carefully reveals a **dichotomy** that closes the question of
whether any finite flag-SDP level exactly closes the cut. It does not, and for a structural reason.

**The k=1 (single-root) moment matrix is VACUOUS.** Reflection positivity (Lovász) makes
`M[j,k] = E_v[cnt_v(j)·cnt_v(k)]` PSD — but it is a *covariance of 1-ball features* `φ_j(v)=cnt_v(j)`, hence
auto-PSD for **any** type distribution `π`. Adding `M ⪰ 0` to the flag-LP changes `min m₂` by `0` (DMAX=5).
So the only *valid* PSD moment matrix over neighbourhood-types adds nothing.

**The dichotomy.** Across every finite construction:
- **single-vertex features** (k=1 moment matrix, linear moments) → the constraint is a covariance /
  transportation feasibility, **auto-satisfied → vacuous** (W11 linear lift, W12 k=1);
- **edge / two-vertex features** (raw `E`, cavity-pair matrices) → the matrix is a bipartite-like
  adjacency, **indefinite for real trees → invalid** (W11).

No finite matrix over local types is simultaneously valid (PSD on all trees) and biting. The reason is
structural: mass transport + local moments enforce exactly **belief-propagation / cavity consistency**, and
for the degree measure the BP fixed-point set is strictly larger than the set of genuine tree limits. The
flag gap **is** the gap between *locally consistent* (BP-fixed-point) measures and *extremal tree-limit*
measures — a **measure-extremality / Gibbs-uniqueness** phenomenon, invisible to any finite convex
(LP/SDP) relaxation. This is exactly why route (b) is a *convergent hierarchy* (W9) with no finite exact
level, and why `log ρ*` is a *thermodynamic limit* (W5): the same fact seen three ways.

**The constructive exact path (reconnecting to route a).** Trees are **loopless**, so the cavity/BP method
is **exact** for each tree's matching free-energy density `F(T) = ½∫log(1+u)dμ_N` — no RSB, no relaxation
gap. The exact optimum is therefore a **variational problem over BP fixed points**: maximize the exact
cavity free-energy functional over degree-consistent local measures, attained by the caterpillar's fixed
point at `log ρ*`. That is precisely the folded **cavity-potential** object that closed the Laplacian
`Φ≤1` crux — the honest exact route is the cavity/interpolation argument, not a finite moment-SDP. Route (b)
delivered what a moment hierarchy can: a convergent bound and a kernel-gated finite certificate (W10);
its exact closure is the cavity variational proof. Reproduction: `bg_k1_moment.py` (k=1 vacuity).
`conjecture1_proved = False`.

## W13 (2026-08-29): the exact cavity (Bethe) free energy — foundation built + ρ* localized; the naive local potential hits the same wall

Built the exact cavity/Bethe machinery — the route-(a) foundation, now correct for the *matching* object.

**Exact cavity free energy (verified).** Messages `x_{u→v}=Σ_{c~u,c≠v} w_{uc}/(1+x_{c→u})`, `w=1/(d_u d_c)`;
`log Z = Σ_v log(1+Σ_a w_{va} q_{a→v}) − Σ_e log(1+w_e q_{u→v} q_{v→u})`, `q=1/(1+x)`. This reproduces
`log(per(L)/∏deg)` **exactly** — max error `9·10⁻¹⁶` over all 47 trees `n≤8` (it is exact on trees,
Heilmann–Lieb). Reproduction: `bg_cavity.py`.

**ρ* localized as a cavity variational optimum.** The infinite length-2-arm caterpillar has an explicit
fixed point (`x_{leaf→AM}=0`, `x_{AM→H}=½`, hub messages solving a quadratic). Its per-cell density `F(a)`
is maximized at `a* = 7.016` with `F(a*) = log ρ* = 0.205098` (to `2·10⁻⁸`), and the integer `a=7` hits it.
So `ρ* = max_a [infinite-caterpillar cavity density]` — a clean exact characterization. Reproduction:
`bg_cavity_caterpillar.py`.

**But the naive local cavity potential hits the SAME wall (W12 confirmed in cavity space).** The per-vertex
free energy `pv(v)=log A_v−½Σ_a log B_{va}` plus a message-discharge `Σ_a[P(x_{a→v})−P(x_{v→a})]` (telescoping)
and a handshake degree term `β·d` — minimized over configs `(d; {(d_a,x_a)})` — **plateaus at `0.331`**
(`gap +0.126`, DMAX=4), not `log ρ*`. Same cause as the moment side: the per-config relaxation admits
**non-realizable** local message configs (and the single-edge boundary `½log2`). The exact-cavity variables
do **not** dodge the realizability wall; enforcing message realizability would converge but (W12) not finitely
close. Reproduction: `bg_cavity_potential.py`.

**The right global tool.** Heilmann–Lieb: monomer-dimer has **no phase transition** → the cavity recursion is
a **contraction** with a *unique* fixed point. So the flag/cavity gap is realizability (which local marginals
are genuine tree limits), *not* Gibbs multiplicity. The exact bound should therefore come from a **global
monotone / contraction argument** on the unique cavity map (Guerra-style interpolation between `T` and the
caterpillar, or a Lyapunov functional of the contraction) — not a local per-vertex potential, which provably
plateaus. That is the sharp next target; the cavity foundation (exact `F`, explicit caterpillar fixed point,
`ρ*=max_a F(a)`) is now in place to support it. `conjecture1_proved = False`.

## W2 first result (2026-08-29): the entry moment `m_1` is bounded

`m_1(T) = (2/n)Σ_e 1/(deg_i deg_j)` (exact rational). Exhaustive per n:
- **path** `P_n` gives `m_1 = (n+1)/(2n) → ½` (edges: (n−3) interior `¼` + 2 end `½`).
- for `n ≤ 9` the path is the maximizer; for `n ≥ 10` a "double-broom" (two deg-3 hubs + extra leaves,
  degseq `[3,3,2,…,1,1,1,1]`) narrowly beats it (n=10: `5/9` vs path `11/20`).
- `max_T m_1` is **monotone decreasing** in n (5/8, 3/5, 7/12, …, 61/112 at n=14) and bounded, →~½.

So `m_1 ≤ 5/8` (all n; sharp at n=4) and `m_1 ≤ (small const)` asymptotically — the entry moment is
controlled by a pure degree-sequence optimization under the handshake `Σdeg = 2n−2`. **W2 is essentially
closed** (a clean rational bound); the work moves to W3 (the joint moment SDP with the alternating
functional), where the caterpillar's balance — not any single-moment extremum — must be shown optimal.

## W3 result (2026-08-29): Hankel-PSD + `m_1` OVERSHOOTS — the missing cut is an even-moment LOWER bound

Two relaxations tested against `log ρ* = 0.20510`:
- **Per-moment bounds** (`m_k ≤ β_k = max_T m_k`, K=6, grid-LP): max `F = 0.22977`, **gap +0.0247**.
  Loose — the β_k are not jointly achievable (different trees max different `m_k`).
- **Hankel-PSD moment SDP** (measure on [0,1], K=4 envelope) + `m_1 ≤ β_1` (cvxpy/SCS):
  `β_1=0.625` → gap +0.038; `β_1=0.52` (caterpillar) → **+0.0043**; closes only at `β_1 ≤ 0.505`,
  which *excludes* the caterpillar (`m_1=0.520`).

**Diagnosis (the S2 cut located).** With `c_2 < 0` in the envelope, the SDP inflates `F` by pushing
`m_2` down to the **Hankel floor `m_2 ≥ m_1²`** (`=0.270` at `m_1=0.52`) — below the caterpillar's
`m_2 = 0.308`. No tree with `m_1=0.52` reaches `m_2 < 0.308`. So the binding missing constraint is a
**tree-specific LOWER bound on `m_2` given `m_1`**, strictly above the Hankel floor. This is the concrete
S2 cut to prove (W4): `m_2(T) ≥ φ(m_1(T))` for a tree function `φ` with `φ(m_1) > m_1²`, tight at the
caterpillar. Higher even moments likely need analogous cuts. The per-vertex/degree-local nature of the
walk moments is what makes these cuts provable (unlike the transcendental per-vertex `log a_v`).

## W4 progress (2026-08-29): the S2 cut is a LOCAL even-moment lower bound (concrete + provable)

The tree `(m_1, m_2)` locus (empirical): the lower boundary is traced by the **caterpillar family** as
`a` grows. At `m_1 ≈ 0.52`, `m_2` decreases with `a` (a=7→0.308, a=10→0.296, a=13→0.287) but stays
**strictly above the Hankel floor `m_1² = 0.270`**; length-3 arms (0.394) and paths (0.378) sit far
higher. So trees provably do not reach the Hankel `m_2` floor that the W3 SDP-overshoot exploited.

**The cut is a local degree inequality.** `m_2 = (1/n)Tr N^4` has an explicit closed form: for each
vertex `v`, `(N^4)_{vv} = (1/deg_v²)(Σ_{a~v} 1/deg_a)² + Σ_{a~v}(1/(deg_v deg_a²))·Σ_{c~a,c≠v} 1/deg_c`
(closed 4-walks = "cherry-returns" `v→a→v→b→v` + "neighbor-of-neighbor" `v→a→c→a→v`). So `m_2` is a
**local, polynomial degree functional** — the S2 cut `m_2(T) ≥ φ(m_1(T))` is a per-neighborhood
inequality, exactly the provable object route (b) promised (vs the transcendental per-vertex `log a_v`).

**W4 remaining:** (i) derive the tight `φ` from the local formulas (the caterpillar boundary in closed
form); (ii) re-solve the SDP with `m_2 ≥ φ(m_1)` added — confirm it closes to `log ρ*` at the
caterpillar (and identify whether `m_3`,`m_4` cuts are also needed). **W5:** the finite-`n` `poly(n)`.

**Status of route (b):** the upper bound is now a **finite, local, moment-SDP + walk-count-cut problem**
— W1 (SOS envelope, ~done), W2 (`m_1` bound, done), W3 (relaxation gap measured + cut located, done),
W4 (cut is local/provable, in progress). No transcendental obstruction remains; the open work is the
explicit even-moment cuts and the SDP closure. `conjecture1_proved = False`.

## W4 DECISIVE (2026-08-29): the local `m_2` cut nearly closes the SDP — route (b) validated

Two confirmations that route (b) is a **viable** proof route (bypassing the collective wall):

1. **The `m_2` local degree formula is EXACT** — verified `m_2 = (1/n)Σ_v[(1/deg_v²)(Σ_{a~v}1/deg_a)² +
   Σ_{a~v}(1/(deg_v deg_a²))Σ_{c~a,c≠v}1/deg_c] = (1/n)Tr N^4` for all trees n=4–9. The cut is a concrete,
   provable, per-neighborhood degree inequality.
2. **Adding the tree `m_2` lower bound collapses the SDP gap** (K=4 envelope, `m_1 ≤ 0.52`):
   | cut | max F | gap to log ρ* |
   |---|---|---|
   | none | 0.20936 | +0.00426 |
   | `m_2 ≥ 0.287` (tree min at this m_1) | 0.20785 | +0.00275 |
   | `m_2 ≥ 0.308` (caterpillar) | 0.20588 | **+0.00078** |

The residual `+0.0008` is attributable to the K=4 envelope order and a missing `m_4` lower-bound cut;
a higher-K envelope + `m_2`,`m_4` cuts should close it fully. **This is the key viability result:** the
moment-SDP + a *provable local walk-count cut* drives the bound to `log ρ*`, so route (b) genuinely
evades the collective wall (which lived in the transcendental per-vertex `log a_v`) — the difficulty is
now a *finite, local, combinatorial* even-moment-cut problem.

**Remaining to a full proof:** (W4c) derive the tight `m_2 ≥ φ(m_1)` and `m_4` cuts in closed form from
the local degree formulas (the caterpillar traces the boundary); (W4d) re-solve with a higher-K SOS
envelope + both cuts, confirm exact closure; (W5) the finite-`n` `poly(n)` correction. Every remaining
piece is finite-dimensional and combinatorial — no transcendental obstruction. `conjecture1_proved = False`.

## W4c (2026-08-29): the S2 cut `φ(m_1)` in closed form

The tree `(m_1,m_2)` lower boundary is the caterpillar family, now derived in closed form from the local
degree formulas of the infinite periodic a-arm caterpillar (spine deg `d=a+2`, `a` mids deg 2, `a` leaves
deg 1; period `1+2a`), verified against empirical to <2e-3:

    m_1(a) = (2/(1+2a)) [ 1/(a+2)² + a/(2(a+2)) + a/2 ]
    m_2(a) = [ N4_spine + a·N4_mid + a·N4_leaf ] / (1+2a),   with
      N4_leaf  = 1/4 + 1/(4(a+2))
      N4_mid   = (1/4)(1+1/(a+2))² + (1/(2(a+2)²))(2/(a+2) + (a−1)/2)
      N4_spine = (1/(a+2)²)(2/(a+2)+a/2)² + (2/(a+2)³)(1/(a+2)+a/2) + a/(4(a+2))

The curve runs from `(m_1,m_2) = (0.520, 0.372)` at a=1 to `(½, ¼)` as a→∞ (variance `m_2−m_1² → 0`).
**The S2 cut is `m_2(T) ≥ φ(m_1(T))`**, `φ` = this boundary (parametric in `a`; monotone, invertible).

**W4c remaining → W4d:** (i) PROVE `m_2(T) ≥ φ(m_1(T))` for all trees — a per-neighborhood inequality on
the (now explicit) local degree formulas `m_1 = (2/n)Σ_e 1/(deg_i deg_j)`, `m_2 = (1/n)Σ_v[…]`; the
caterpillar boundary being tight means it's an equality-constrained optimization (Lagrange/rearrangement
over degree sequences). (ii) the analogous `m_4` cut for the residual `+0.0008`. (iii) re-solve the SDP
with `m_2 ≥ φ(m_1)` (+`m_4`) and a higher-K SOS envelope → confirm exact closure to `log ρ*`. Then W5
(`poly(n)`). All finite/combinatorial. `conjecture1_proved = False`.

## W4d (2026-08-29): the `m_2` cut ALONE suffices — the theorem is a single inequality

SDP closure test (K=4 validated envelope): `m_1≤.52` gap +0.00426; `+ m_2≥.308` (caterpillar) gap
**+0.00078**; `+ m_2≥.308, m_4≥.140` gap **+0.00078** (unchanged). So the `m_4` cut is *not* needed —
the residual +0.0008 is **K=4 envelope order** (`Σc_k u^k > ½log(1+u)` slack), reducible with a higher-K
SOS envelope, not a missing moment constraint.

**Consequence — route (b) upper bound reduces to ONE theorem:**

    (W4d-thm)   m_2(T) ≥ φ(m_1(T))  for every tree T,

with `φ` the closed-form caterpillar boundary (W4c). Given this single per-neighborhood degree
inequality (+ a higher-K SOS envelope for the residual + W5 poly(n)), the moment-SDP closes to `log ρ*`.
No other moment cut, no transcendental step. The inequality is on the *explicit local formulas*
`m_1=(2/n)Σ_e 1/(deg_i deg_j)`, `m_2=(1/n)Σ_v[(S_v/deg_v)² + Σ_{a~v}(1/(deg_v deg_a²))(S_a−1/deg_v)]`
(`S_v=Σ_{a~v}1/deg_a`) — a finite degree-sequence optimization with the caterpillar tight, provable by
local move / rearrangement or Lagrange conditions. **This is the sole remaining theorem of route (b).**
`conjecture1_proved = False`.

## W4d CORRECTION (2026-08-29): the cut is NOT a universal inequality

**Retraction:** the preceding "route (b) reduces to ONE inequality `m_2(T) ≥ φ(m_1(T))` for every tree"
is **overstated**. Exhaustive check n≤14: `m_2 ≥ φ(m_1)` FAILS for low-`m_1` trees (58 violations, min
slack −0.11 at `m_1≈0.14`). The `(m_1, min-m_2)` global lower boundary is traced by **stars** at low
`m_1` (where `m_2 = m_1`, still well above `m_1²`) and by the **caterpillar family only near `m_1≈0.52`**
— the extremum band. Two independent implementations (this effort + a second-opinion session) converged
on exactly this scoping.

**Correct remaining theorem.** The SDP only sees the region near `m_1≈0.52` (where `F` is maximal;
low-`m_1` trees have low `F` and don't bind). So the sole remaining theorem is:

    (W4d′)  the caterpillar maximizes the LOCAL POLYNOMIAL functional  G(T) := Σ_k c_k m_k(T)  over trees
            (asymptotically / with poly(n)), equivalently: the tree moment body's `Σc_k m_k`-max is the
            caterpillar's — a claim scoped to the extremum `m_1` band, NOT a universal `m_2 ≥ φ(m_1)`.

This is still the genuine route-(b) reduction — `G` is **local and polynomial** (walk moments), so it's a
combinatorial optimization provable by local move / rearrangement, versus the transcendental free-energy.
But it is the *full* extremal optimization, not a single clean cut. **Independently de-risked:** the
decisive W4 structure (exact `m_1` formula; trees strictly above the Hankel `m_1²` floor by ≥+0.08; the
SDP-overshoot measure genuinely unreachable by trees; caterpillar `m_2` values) was reproduced from
scratch by a second implementation. `conjecture1_proved = False`.

## W4d′ numerically validated (2026-08-29)

The corrected theorem — caterpillar maximizes `G(T)=Σc_k m_k` over trees — checks out: `G` over large
families gives **cat a=7 = 0.205140 (MAX)**, cat a=6/a=8 = 0.20511 (near), cat a=5/a=10 = 0.20497, path
0.18882, star 0.00231, double-broom 0.06558; and `log ρ* = 0.205098` (cat a=7's `+0.00004` excess is
K=4 envelope order). So the local polynomial functional `G` is maximized by the caterpillar at exactly
`log ρ*` — the well-posed, scoped W4d′ target. `conjecture1_proved = False`.

## W14 (2026-08-29): RH-toolkit review for BG leads -- Heilmann-Lieb = Lee-Yang = the W13 contraction, with real-stability certificate vocabulary

Reviewed the RH-side Telperion skillset (`turan`, `jensen`, `hankel_jensen`, `interlacing`, `toeplitz`,
`weil_positivity`, `trig_nonneg`) for leads into the BG cavity/density bound.  It is a **real-rootedness /
PSD-positivity** vocabulary, and it plugs into BG through one deep fact.

**The connecting fact (verified).** `per(L)/∏deg = ∏_{λ>0}(1+λ²) = |char_N(i)| = ∏_{all λ}√(1+λ²)`, where
`char_N` = characteristic polynomial of `N=D^{-1/2}AD^{-1/2}`, which is **real-rooted** (N symmetric;
equivalently the weighted matching polynomial, real-rooted by **Heilmann-Lieb 1972**).  Checked exactly on
path/star/caterpillar (match to 1e-9).  So `F(T)=(1/n)log|char_N(i)|` is a real-rooted-polynomial evaluation
on the imaginary axis, and Heilmann-Lieb is precisely a **Lee-Yang / "zeros-on-a-line" theorem** -- an
*already-proven* RH-analog for the matching polynomial.

**Three leads.**
1. **(deep, frontier) Heilmann-Lieb -> Stieltjes cavity -> the W13 global contraction, made rigorous.** The
   cavity ratio `μ(T−v)/μ(T)` is a **Stieltjes continued fraction** (Godsil interlacing + Heilmann-Lieb);
   the cavity map `x ↦ Σ w/(1+x)` is a Stieltjes/Herglotz contraction with a *unique* fixed point (the W13
   "no phase transition => contraction", now with a name).  Crucially, this is the **realizability
   constraint the W13 local potential lacked**: messages are not free in [0,1], they are Stieltjes
   continued-fraction values.  The RH `interlacing.py` (Wronskian real-stability, SOS-of-Wronskian) is the
   certificate vocabulary for exactly this.  Resuming BG = build the Stieltjes/interlacing bound on the
   cavity free energy (the honest exact route; local potentials provably plateau, W6-W13).
2. **(buildable) kernel-gate the moment-SDP via `HankelJensenCertificate`/`WorstCorner`.** The RH
   `hankel_minors` + `WorstCornerCertificate` machinery certifies Hankel-PSD over rational brackets IN-KERNEL
   (Hermite's criterion) -- exactly the moment-realizability of W7a.  Reuse to kernel-gate the BG moment
   bound; with the W10 flag-discharge cut cert this gives a fully kernel-gated route-(b) finite level.
3. **(angle) Weil-positivity template.** Weil's form (PSD quadratic form <=> RH) suggests casting the BG
   extremality as PSD of the cavity free energy's **second variation** at the caterpillar fixed point,
   certified via `WorstCorner` -- "caterpillar is the max" as a positivity certificate.

**Extra structural constraint spotted.** Real-rootedness gives the matching numbers `c_k` (`= e_k(λ²)`)
**nonnegative + Newton log-concave** (verified) -- a constraint on the tree moment body BEYOND the generic
power-sum Hankel-PSD used in W7/W12.  Worth adding to the moment relaxation (does not exclude the single
edge -- a real tree -- but may tighten the non-tree relaxation).  Reproduction: `bg_rh_toolkit_lead.py`.
`conjecture1_proved = False`.

## W15 (2026-08-29): Lead 1 -- the cavity is a STRONG contraction (geometric convergence); Stieltjes-realizable messages tighten the bound ~44%

Pursued Lead 1 (Heilmann-Lieb Stieltjes cavity as the W13 "global contraction" + the message-realizability
the local potential lacked).  Two concrete results.

**(A) The cavity map is a strong contraction; the free energy converges geometrically.** A leaf-message
perturbation decays with per-hop ratio **~0.008-0.045** up the caterpillar; the Bethe free energy reaches its
fixed point in **~2-3 sweeps** (error 4e-6 -> 2e-10 -> machine zero).  So `F(T)` is determined by the
depth-2/3 local structure (deeper terms `< 10^-4`) -- the Heilmann-Lieb "no phase transition => contraction"
made quantitative.  This is a **geometrically-convergent** hierarchy, unlike the slow moment/flag hierarchy
(W9).  Reproduction: `bg_cavity_contraction.py`.

**(B) Stieltjes-realizable messages tighten the cavity bound ~44%.** W13's cavity potential over FREE messages
(handshake + bulk-config restricted) gives, at DMAX=5, a density bound `0.2286` (gap `+0.0235`).  Restricting
the incoming messages to their **realizable Stieltjes set** (each message is a continued-fraction value
`x = Σ 1/(d·d_c·(1+x_c))` from realizable child messages, converged via the contraction) tightens it to
`0.2182` (gap `+0.0131`) -- a **44% gap reduction**.  So the realizability constraint the local potential
lacked (W13) genuinely helps, exactly as the RH/Stieltjes lead predicted.  Reproduction:
`bg_stieltjes_potential.py`.

**Honest status.** Lead 1 tightens but does not *alone* close (still `+0.013` at DMAX=5, coarse): the
per-config relaxation still lacks the **joint mass-transport consistency** (W8) between a message and its
reverse.  Per W12 no finite local relaxation closes exactly -- but the strong contraction (A) means the
**convergence is geometric/fast**, so the natural certificate is a finite cavity level (realizable messages +
mass transport + fine resolution) with a *certified geometric error bound* `F ≤ log ρ* + C·ρ^d`, `ρ ~ 0.03`.
The synthesis = Lead 1 (Stieltjes messages, exact cavity, geometric error) + W8 (mass transport) + Lead 2
(kernel-gate the finite level via the RH `WorstCorner`/real-stability machinery).  `conjecture1_proved = False`.

## W16 (2026-08-29): Lead 2 -- the RH Hankel/WorstCorner PSD machinery transfers to BG (kernel-gating foundation)

Demonstrated the Lead-2 transfer: the RH `hankel_minors` + `WorstCornerCertificate` machinery (Hermite's
criterion -- a symmetric matrix is PSD iff its leading principal minors, polynomials in the entries, are
positive over rational brackets) certifies BG moment-body facts **in exact rationals**.  The caterpillar's
exact spectral moments `(m_1,…,m_4)` give a Hankel moment matrix `[[1,m_1,m_2],[m_1,m_2,m_3],[m_2,m_3,m_4]]`
with leading minors `D_1=1`, `D_2=610291/8820000>0`, `D_3=116095997089/185220000000000>0` -- exactly the
rational minor-positivity the RH `WorstCornerCertificate` gates.  So the RH real-stability/PSD toolkit
certifies BG moment-realizability in-kernel, and the buildable kernel-gated route-(b) certificate is:
**W10 `FlagDischargeCertificate` (the `m_2` cut atoms) + RH Hankel-minor cert (moment-body PSD) + W15's
certified geometric error `F ≤ log ρ* + C·ρ^d`** (the fast cavity convergence), assembled at one finite
level.  Note: the primal moment-PSD is trivially true for a real tree; the kernel-gating *value* is the
moment-SDP **dual** bound, which combines these PSD/linear certificates -- the concrete formalization the
RH toolkit now makes reachable.  `conjecture1_proved = False`.

### Leads status (2026-08-29)
- **Lead 1 (Stieltjes cavity, W15):** cavity is a strong contraction (geometric convergence); realizable
  messages tighten the bound ~44%.  Real proof-progress; full closure = Stieltjes messages + mass transport
  (W8) at fine resolution, converging geometrically.
- **Lead 2 (kernel-gating, W16):** RH Hankel/WorstCorner machinery certifies BG rational PSD facts in-kernel;
  the route-(b) certificate assembles W10 + Hankel-cert + geometric error at a finite level.
- **Lead 3 (Weil-positivity template):** untried; casts caterpillar extremality as second-variation PSD.

## W17 (2026-08-29): synthesis target confirmed -- exact cavity F over a rich generalized-caterpillar family peaks at the caterpillar = log ρ*

The Lead1+W8 synthesis (exact cavity free energy over reversible degree-message distributions) must certify:
**no degree structure beats the ~7-arm length-2 caterpillar.**  Confirmed over a rich explicit family --
arm-counts 1-19, arm-lengths 1-3, hub-periods 1-3 (multi-hub spacing) -- the exact cavity `F` is maximized at
**(arms=7, arm_len=2, hub_period=1)** = the length-2 7-arm caterpillar, `F=0.205160` (excess `+6·10^-5` =
finite-spine boundary).  The top six are all `arm_len=2, hub_period=1, arms∈{5..10}`; no mixed-arm-length or
multi-hub-period structure comes near.  Reproduction: `bg_synthesis.py`.

**Synthesis status.**  The proof target is confirmed over a rich family, and the three ingredients are
validated: (W15) realizable messages tighten the relaxation ~44% toward `log ρ*`; (W8/W9) the mass-transport
moment relaxation converges to the caterpillar; (W15) the cavity contraction gives geometric convergence.
The remaining build is the **combined relaxation** -- exact cavity `F` over the reversible (mass-transport)
degree-message distribution with Stieltjes-realizable messages -- run to convergence, which by the contraction
converges **geometrically** to `log ρ*` with a certifiable error `F ≤ log ρ* + C·ρ^d` (`ρ~0.03`).  This is the
nonlinear (Bethe-functional) optimization that closes route (b); the family confirmation (W17) + ingredient
validation (W15/W16) show it is the right object with the caterpillar as its unique max.  `conjecture1_proved
= False`.

## W18 (2026-08-29): the combined relaxation is the tightest local bound, but per-config bounds `sup_T F` (finite) not the density -- the definitive wall

Built the combined relaxation: exact cavity free energy + Stieltjes-realizable messages + **full mass-transport
discharge `P(d,x)`** on half-edge states (sender degree + message), telescoping on trees.  Two findings.

**(A) Full mass-transport `P(d,x)` beats message-only `P(x)` sharply.** At DMAX=5 the bound drops
`0.218 → 0.209224` (gap `+0.0131 → +0.0041`, a 69% reduction).  Progression of the local bound:
free `P(x)` (W13) `0.331` → realizable `P(x)` (W15) `0.218` → realizable `P(d,x)` (W18) `0.209`.  Each RH-lead
ingredient (realizable messages, then full state-discharge) tightens substantially.

**(B) But the bound INCREASES with the degree cap -- it bounds `sup_T F`, not `log ρ*`.** Degree-cap sweep:
DMAX=4 `0.2047` (`−4e-4`, restricted to deg≤4 trees < caterpillar), DMAX=5 `0.2092`, DMAX=6 `0.2124`, DMAX=7
`0.2146` -- monotone **increasing**.  The per-config bound = `sup` over degree-≤DMAX bulk trees of `F`, and
since **every finite tree has `F > log ρ*`** (W5, approached from above), that sup exceeds `log ρ*` and grows
as higher-degree trees are admitted.  `log ρ*` is the **n→∞ thermodynamic density**, fundamentally NOT a
per-config/per-vertex quantity -- so no local relaxation (moment W6-W12, cavity W13, or this combined one)
reaches it.  This is the definitive form of the W5/W12 wall.  Reproduction: `bg_combined_relaxation.py`.

**Where this leaves route (b).**  The density `log ρ*` is obtained *directly* on infinite trees (W13, exact
cavity, `F(caterpillar)=log ρ*` to 2e-8) and is maximized by the caterpillar over a rich family (W17).  The
per-config relaxations bound the finite `sup_T F`; the RH-lead ingredients (realizable messages, full
mass-transport) tighten that local bound dramatically but cannot cross to the density.  A finite CERTIFICATE
of the density is obstructed by measure-extremality (W12); the honest exact route remains the **infinite-tree
variational argument** (max over unimodular tree measures of the exact cavity density = `log ρ*`), for which
the strong contraction (W15) gives the analytic control but not a finite convex certificate.
`conjecture1_proved = False`.

## W19 (2026-08-29): Lead 3 -- the exact cavity density is CONCAVE; caterpillar = unique max (the variational proof structure)

Since the local-relaxation line bounds `sup_T F` not the density (W18), the exact route is the **infinite-tree
variational argument**: max over unimodular tree measures of the exact cavity density = `log ρ*`.  Its crux is
**concavity** (a concave functional with a unique stationary point has that point as its global max).  Tested
it on the exact cavity density.

**(1) `F(a)` is strictly concave in arm-count.**  Discrete second difference `F(a+1)−2F(a)+F(a−1) < 0` for
every `a=4..10`, with the maximum at `a≈7` (matching the `a*=7.016` of W13).  So along the arm-count
direction the density is strictly concave with a unique interior max.

**(2) No mixed structure beats the caterpillar.**  Spatial mixes (fraction `p` of hubs with `a=9`, rest `a=5`,
both flanking `a*=7`) all give `F_mix ≤ F(a*=7)` -- the uniform ~7-arm caterpillar dominates every
interpolation.  Consistent with concavity + a unique maximizer.

**The proof structure (Lead 3 = Weil-positivity template).**  (i) The caterpillar is a **stationary point**
of the exact cavity density (`F'(a*)=0`, `a*=7.016`).  (ii) The **second variation is negative** (arm-count
`F''<0`; no mix exceeds it).  (iii) If the full Hessian is negative-definite over all unimodular structural
perturbations, the caterpillar is a strict local max; with global concavity it is the **global** max = `log
ρ*`.  The negative-definite second variation is exactly a **PSD quadratic-form** fact -- the natural home for
the RH `WeilPositivityCertificate` / `WorstCorner` machinery (Lead 3), certifying `−Hessian ⪰ 0` over rational
brackets.  Remaining rigorous work: prove full-Hessian concavity over all unimodular directions (numerically
supported here; the analytic step), then kernel-gate the second-variation PSD.  Reproduction:
`bg_concavity.py`.  `conjecture1_proved = False`.

## W20 (2026-08-29): the caterpillar is a STRICT LOCAL MAX in every structural direction -- local-max half of the variational proof, via the contraction

The exact-route (W19) reduces to concavity; its *local* half is that the caterpillar is a strict local max.
Tested six independent single-site structural perturbations of the uniform a=7 length-2 caterpillar -- **all
strictly decrease `F`**:

| perturbation | `dF` |
|---|---|
| +1 arm at one hub        | `−1.0e−6` |
| −1 arm at one hub        | `−7.9e−7` |
| one arm length 2→3       | `−7.1e−5` |
| one arm length 2→1 (leaf)| `−2.4e−4` |
| spine branch (3-way hub) | `−1.2e−4` |
| arm-end cherry (deg-2)   | `−7.1e−5` |

So the caterpillar is a strict local max in arm-count, arm-length, spine-branching, and arm-end degree --
every structural direction tested.  **The analytic reason:** in the cavity method a strict local max of the
Bethe density corresponds to **BP fixed-point stability = the Bethe-Hessian being negative-definite**, and
that stability is exactly the **strong contraction** established in W15 (rate ~0.03).  So the local-max half
is essentially *reduced to the already-established contraction* -- not another numerical coincidence.

**Variational proof, assembled (Lead 3):** (i) caterpillar is the unique stationary point at `a*=7.016`
(W17); (ii) it is a strict local max in every direction (W20), analytically because the cavity map contracts
(W15); (iii) the density is concave along the tested families (W19).  The **one remaining rigorous piece** is
*global* concavity / no-other-local-max over all unimodular tree measures -- the genuine hard-analysis step,
numerically supported by the W17 rich-family scan (caterpillar dominates) but not proven.  With it, the
caterpillar is the global max of the exact cavity density = `log ρ*`, i.e. the BG density bound; the
negative-definite Hessian is then kernel-gateable via the RH `WeilPositivityCertificate`/`WorstCorner`
machinery.  Reproduction: `bg_localmax.py`.  `conjecture1_proved = False`.

### Route (b), fully mapped (W5-W20)
- **Density characterized:** `log ρ*` = infinite-caterpillar cavity density (exact, W13), maxed by the
  caterpillar over a rich family (W17); a thermodynamic limit approached from above (W5).
- **Local-relaxation line (walled):** moment/cavity/combined per-config bounds bound the *finite* `sup_T F`,
  not the density (W6-W18); RH-lead ingredients tightened it `0.331→0.209` but cannot cross to the density.
- **Variational route (the exact path):** reduced to concavity (W19); local max established in all directions
  via the contraction (W20); **sole remaining piece = global concavity over unimodular measures.**
- **Kernel-gated deliverable:** W10 `FlagDischargeCertificate` (finite-level m_2 cut).
- **RH toolkit:** Heilmann-Lieb = Lee-Yang real-rootedness (W14); Hankel/WorstCorner + Weil-positivity are the
  certificate machinery for the moment-body PSD (W16) and the second-variation PSD (W19/W20).
