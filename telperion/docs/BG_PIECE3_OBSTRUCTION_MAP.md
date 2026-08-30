# BG route-(b) piece 3 — obstruction map + the Guerra interpolation program

**Status:** `conjecture1_proved = False`. This documents the *universal* piece-3 step (the caterpillar is the
global maximizer of the matching free-energy density over all trees), why every local/combinatorial method
fails to certify it, and the one remaining viable route — **Guerra interpolation**.

## 0. The object

`F(T) = (1/n) log(per(L)/∏deg) = (1/2) ∫ log(1+u) dμ_N(u)`, `u = λ²`, `N = D^{-1/2} A D^{-1/2}`,
`μ_N` the empirical spectral measure of `N`. Equivalently `F(T) = (1/2n) log det(I + N²)`.
Route (b): `log ρ* = lim_n max_{|T|=n} F(T) = 0.205098…`, maximizer the length-2-arm ~7-arm caterpillar.

Reduction of the BG-classical crux (global concavity of the Bethe density) into three pieces:
- **Piece 1 — SSM.** Monomer-dimer strong spatial mixing (Bayati–Gamarnik–Katz–Nagaraj–Tetali, STOC 2007):
  a *uniform* cavity contraction, no phase transition (Heilmann–Lieb). **Known theorem.**
- **Piece 2 — `F''(a) < 0` + strict max at a=7.** Kernel-verified: `telperion/examples/bg_caterpillar_concavity`.
- **Piece 3 — global no-distant-competitor.** The subject of this document.

## 1. The verified `m_k` machinery (reusable)

Key rational identity: `N^m_{vv} = (A D^{-1})^m_{vv}` (the `D^{±1/2}` cancel on the diagonal), so closed-walk
weights are rational. The distance-from-`v` profile of a closed `2k`-walk on a tree is a **Dyck path** (length
`2k`, Catalan `C_k` shapes). Enumerating + reassigning the radius-`>k` shapes to their middle vertex gives an
exact per-vertex integrand `lhs_k(v)` with `Σ_v lhs_k(v) = Tr N^{2k}`:

- `lhs_1 = S/d` (radius-1), `S = Σ_{a~v} 1/d_a`.
- `lhs_2 = 2S²/d² − Q/d²` (radius-1), `Q = Σ_{a~v} 1/d_a²`.
- `lhs_3 = C1r + T3/d + 2·S·T2/d² + S³/d³` (**radius-2**), with `S_a = Σ_{c~a} 1/d_c`,
  `T2 = Σ_a (S_a−1/d)/d_a²`, `T3 = Σ_a (S_a−1/d)²/d_a³`, `C1r = (1/d²)Σ_a (1/d_a²)(S_a−1/d)(S−1/d_a)`.

Verified to ~1e-16 against eigenvalue ground truth on structured + 30 random trees, and re-checked exactly by
stdlib rational matrix power in `tests/test_bg_m3_moment_cut.py`.

## 2. What is certified so far (degree 3)

`examples/bg_m3_moment_cut` (PR #161) kernel-gates the **finite** argmax: for the frozen degree-3 upper
envelope `P_3(u) ≥ ½log(1+u)`, the ~7-arm caterpillar strictly maximizes `c₁m₁+c₂m₂+c₃m₃` over a set of
**structurally distinct** competitors (2/3/4-regular trees, L=3-arm caterpillars, arm counts 3, 10). This is
the honest ceiling of the degree-3 level (see §3).

## 3. Why local / moment methods CANNOT certify the universal step

All experiments below verified the caterpillar **is** the true maximizer, then failed only at *certification*.

1. **Degree-3 moments are provably insufficient.** The reversible flag LP (decoration/type densities
   `q,e` with degree/`S`-consistency + reversibility) is loose from dmax≥5. Its spurious optimum has moments
   `(m₁,m₂,m₃)=(0.549,0.432,0.372)` (vs caterpillar `(0.526,0.341,0.240)`) that pass **every** order-3 moment
   constraint — 2×2 Hankel `m₂≥m₁²`, `[0,1]`-localizing `m₁m₃≥m₂²` and `(1−m₁)(m₂−m₃)≥(m₁−m₂)²`. So an
   order-3-valid moment vector of *some* measure beats the caterpillar; no degree-3 structure excludes it.
   Universal certification requires `m₄,m₅,…` — the moment-SDP hierarchy, which even at K=4 only reaches
   +8e-4 (slow).

2. **Discharge (per-vertex inequality + telescoping) is loose.** With an antisymmetric radius-2 potential
   `W(x_v,x_a)` and worst-case neighbour-of-neighbour sums `S_a`, the bound is loose (0.27–0.35 vs 0.20),
   because the worst-case lets every neighbour be adversarial independently. Pinning the joint `S_a` is the
   intractable radius-2 type enumeration. `B₁<0` (the surface term, see §4) helps but does not rescue it.

3. **Grafting → Fekete is refuted.** `F(graft)` < size-weighted average in 19/21 tests (grafting generally
   *lowers* density — the caterpillar is the attractor), but grafting two low-`F` stars *raises* `F`
   (0.077→0.085). No clean sub/super-additivity ⇒ no building-block argument.

### The single root cause: **acyclicity is global**

The Bethe/cavity free energy and the `lhs_k` integrands are **exact only on trees**. Every *local* relaxation
(flag LP / discharge / moment) unavoidably applies these tree-formulas over a feasible set that **includes
loopy and forest measures**: mean degree → 2 admits the *unicyclic* limit and finite-component *forests*
(a forest of P3's + high-degree pieces averages mean-degree 2), on which the formulas are invalid and
inflated. Local statistics cannot distinguish a tree from a cycle or a forest (identical finite
neighbourhoods). This is exactly why Bethe is exact on trees but not loopy graphs — and it defeats the entire
local/combinatorial family for the universal step.

## 4. The one structural handle: the surface term

The discharge inequality summed over a graph gives `mean Φ ≤ B₀ + B₁·(mean degree)`. A **connected tree** has
`Σd = 2n−2` (mean degree `2−2/n`); a **forest with k components** has `Σd = 2n−2k`. So a *single* per-vertex
inequality automatically yields, with `B₁<0`, `F(connected) ≤ logρ* + O(1/n)` while correctly allowing
forests to be higher — the connectedness is encoded by the exact Euler characteristic `#edges = n−1`, which
the density-limit flag LP (mean degree fixed at 2) throws away. This is why an inequality/interpolation
argument — not a measure relaxation — is the right vehicle.

## 5. The Guerra interpolation program (committed next step)

Guerra's method proves free-energy inequalities **without any local relaxation**, by interpolating between
two systems and showing the derivative of the free energy has a definite sign (a sum of squares). It is the
natural fit here because:

- It works on the **exact** free energy `F` (log-det / Bethe), so it sidesteps the acyclicity barrier by
  construction (no loopy measures ever enter).
- The second-order term is a **susceptibility**, which is controlled by the **uniform SSM contraction
  (piece 1)** — so the two existing pieces plug in as the definiteness input.

**Concrete framework.** `F(T) = (1/2n) log det(I + N_T²)`. Interpolate between an arbitrary (large) tree `T`
and the caterpillar `C` via the cavity/message distribution `ρ_t` (`ρ_0 = ρ_T`, `ρ_1 = ρ_C`), or via a matrix
interpolation of the quadratic form. Define `Φ(t) = Bethe-free-energy[ρ_t]` and target `Φ'(t) ≤ 0`, i.e.
`F(T) ≤ F(C)`. The RDE-stationarity of `ρ_C` (caterpillar = cavity fixed point) kills the first-order term;
the second-order term is a message-susceptibility bounded by the SSM contraction rate `< 1`.

**Milestones + progress.**
- **G1 — DONE, verified.** The exact matching free energy in cavity-message coordinates:
  `F(T) = (1/n)[ Σ_v log(A_v/d_v) − Σ_e log(1 + 1/(μ_{u→v}μ_{v→u})) ]`, `A_v = d_v + Σ_{a~v} 1/μ_{a→v}`,
  messages `μ_{u→v} = d_u + Σ_{c~u,c≠v} 1/μ_{c→u}` (leaves `μ = d_leaf`). Derived from the Schur/leaf-elimination
  of `M = D − iA` (which is real: `(−i)² = −1`), edge factor identified from P3 and **verified to ~1e-16**
  against the eigenvalue `F` on paths/stars/caterpillars/binary/30 random trees. This is the exact substrate —
  no moments, no relaxation.
- **G2 — DONE, decisive negative.** The Bethe functional `Φ[μ]` (evaluated at arbitrary messages) is
  **stationary** at the caterpillar BP fixed point (`|Φ'| ~ 1e-13`, the known BP-stationarity) but it is a
  **SADDLE, not a max**: `Φ''` spans `[−2.7e-5, +2.7e-5]` and some perturbations *raise* `Φ`. So the naive
  message-space concavity that a straightforward interpolation would need **does not hold** — as expected
  (the Bethe free energy is famously non-convex in raw message coordinates).
- **G3 — the crux. Two advances (this session):**

  **(i) The monomer-dimer reformulation (verified ~1e-16).** Working out the weighted matching polynomial at
  `i` (`μ_N(i) = i^n Σ_k p_k`, since `i^{-2k}=(-1)^k` cancels the `(-1)^k`) gives the exact identity
  ```
  per(L)/∏deg = Σ_{matchings M} ∏_{e=(u,v)∈M} 1/(d_u d_v) = Σ_M ∏_{v matched by M} 1/d_v,
  F(T) = (1/n) log of it.
  ```
  So `F` is *exactly* a **monomer-dimer log-partition-function** with degree-tied edge weight `1/(d_u d_v)`
  (per-vertex form: each matched vertex contributes `1/d_v`). This is the Heilmann-Lieb (real roots, no phase
  transition) / Guerra-Toninelli setting — cleaner than the moment or raw-cavity forms. Script:
  `guerra/G3_monomer_dimer.py`.

  **(ii) The concavity route is DEAD (coordinate-invariant saddle).** The G2 saddle is not a coordinate
  artifact: the Hessian signature at a critical point transforms as `H → Jᵀ H J` under any smooth
  reparametrization (Sylvester — inertia preserved), so belief/occupation variables (`t_{u→v}=d_u/μ_{u→v}`) are
  a saddle too. The Bethe free energy is genuinely non-variational here. Route (a) must therefore use
  **linearity, not concavity**: `F = ½∫log(1+u)dμ_N` is *linear* in the spectral measure ⟹ its max over the
  convex hull of achievable measures is at an **extreme point** ⟹ **forests are excluded** (non-extreme convex
  combinations of components); the remaining extreme points are ergodic trees. A dual/supporting-hyperplane
  `ψ(u) ≥ ½log(1+u)` tight on `supp μ_caterpillar` with `∫ψ dμ_T ≤ ∫ψ dμ_C` certifies it — and a *non-polynomial*
  `ψ` (resolvent-matched to the caterpillar spectrum) escapes the degree-`K` moment cap (§3.1).

  **Remaining routes (both saddle-independent):** (a) linearity + a non-polynomial dual `ψ` (sum-rule
  certificate on the monomer-dimer spectral measure); (b) **Guerra-Toninelli** edge/activity interpolation
  signed by monomer-dimer correlation inequalities. Both stay within **connected** trees, so the acyclicity
  barrier (§3) never enters.

  **(iii) The resolvent decomposition (route (a), concrete — verified structure).** Integral representation
  `½log(1+u) = ½∫₀¹ u/(1+tu) dt` gives
  ```
  F(T) = ½ ∫₀¹ g_T(t) dt,   g_T(t) := ∫ u/(1+tu) dμ_T = (1/n)Tr[N²(I+tN²)⁻¹] = Σ_{k≥1} (−t)^{k−1} m_k.
  ```
  `g_T(t)` is a **resolvent trace** — a *resummation of all moments*, so it escapes the degree-`K` cap of §3.1
  by construction, and is cavity-computable (local, by SSM). Empirically (`guerra/G3_resolvent_dominance.py`):
  **`g_T(t) ≤ g_C(t)` pointwise in `t ∈ [0,1]` for every tree `T` structurally distinct from the caterpillar**
  (paths, regular trees, L=3/L=4 caterpillars, sparse caterpillars, 40 random trees — all dominated with
  margin). The **only** pointwise-crossers are near-optimal caterpillar-like trees (the uniform L=2 arm-count
  family `a≠7`, which crosses at small/large `t` as `m₁`/tail trade off, plus non-uniform generalized
  caterpillars like "every 3rd hub 9 arms") — all within `F ~ 10⁻³` of `a=7`. This realizes the **local–global
  split**:
  - **Far** (structurally distinct, `F ≤ logρ* − ε`): pointwise resolvent dominance `g_T ≤ g_C ⟹ F(T) ≤ F(C)`.
  - **Near** (the crossers, `F` within `ε`): the strict local max in *all* structural directions — piece 2 +
    the phonon Hessian negative-definite via the SSM contraction (the W15-W20 fusion).

  **Route-(a) milestones (supersede/refine G3-G5):**
  - **A1** — prove `g_T(t) ≤ g_C(t)` for structurally-far trees (a *single* per-`t` resolvent inequality; the
    margin is large, so a loose cavity/moment bound suffices — unlike the knife-edge §3.1 which needed
    tightness). **Foundation done + verified** (`guerra/A1_resolvent_cavity.py`): `g_T(t)` is an exact
    per-vertex cavity sum, `g_T(t) = (1/n)Σ_v ρ_v(t)`, `ρ_v(t) = (1 + (1/√t)·Im G_v(i/√t))/t`, with the
    complex cavity Green's functions `G_{u→v}(z) = 1/(z − Σ_{c≠v} (1/(d_u d_c)) G_{c→u}(z))` at `z = i/√t`
    (verified ~1e-16 vs eigenvalues). The complex cavity is a contraction (SSM), so `ρ_v` is genuinely local.
    Corollary (exact, via the regular-tree fixed point): the caterpillar **strictly dominates every infinite
    `d`-regular tree** at all `t`, with `g` decreasing in `d` and the **path (`d=2`) the tightest far
    competitor** (margin ~0.03). Per-vertex, the caterpillar's arm-mids (`ρ≈0.43`) carry the weight; high-`ρ`
    vertices (star center `ρ≈0.67`) can't dominate a connected tree because they force low-`ρ` leaves. The
    remaining A1 work: a per-vertex/monomer-dimer bound on `ρ_v(t)` that the caterpillar's role-mix maximizes
    over far trees (margin makes a loose bound sufficient).
  - **A2** — the local charts: extend piece 2 to a negative-definite Hessian in *all* structural phonon modes
    (not just arm-count), gapped uniformly by SSM (piece 1) — covers the crossers.
  - **A3** — the covering/compactness: every tree is Far (A1) or Near (A2), regimes overlapping.
  - **A4** — kernel-gate the finite pieces (enclosure model).
  Honest risk: A1 (per-`t` far dominance) and A3 (covering) are the open crux; A2 is the existing piece-2 line.
  But the resolvent `g_T(t)` gives the *global* part a concrete, cap-free handle for the first time.
- **G4** — the finite-`n` surface-term version (§4) to land `F(T) ≤ logρ* + O(1/n)`, tight at the caterpillar.
- **G5** — reduce the analytic inequality to kernel-gateable rational/enclosure atoms (turan/jensen model).

Honest risk: G3 is the crux and may still fail; G2 already ruled out the naive route and pointed to (a)/(b).
This is a genuine proof attempt. `conjecture1_proved = False`. Scripts: `bg_guerra_G1.py`, `bg_guerra_G2.py`.

## Appendix — reproduction scripts (offline, `/tmp` during development)

`bg_m3_derive.py` (integrand derivation + verification), `bg_m3_flagLP2.py` / `bg_m3_flagL2.py` (reversible
flag LP + support diagnosis), `bg_m3_universal.py` (discharge LP), plus the grafting and small-tree checks.
The exact integrand and moment machinery live in `examples/bg_m3_moment_cut/generate.py`.
