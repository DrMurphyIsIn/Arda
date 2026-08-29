# Walk-count sub-problem — the combinatorial core of the capacity upper bound (route b)

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
