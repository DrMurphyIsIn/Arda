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

**Milestones.**
- **G1** — write the exact per-vertex/per-edge Bethe free energy of the tree matching model in message
  coordinates; confirm it reproduces `F` (numeric).
- **G2** — build the interpolation `ρ_t` and compute `Φ(t)` numerically for many `(T, C)` pairs; **test
  `Φ'(t) ≤ 0`** empirically (monotonicity probe) before any proof. A single violation kills the naive
  interpolation and dictates the correction.
- **G3** — identify the interpolation making `Φ'(t)` a manifest sum-of-squares / sign-definite via the
  cavity stationarity + SSM contraction bound.
- **G4** — the finite-`n` surface-term version (`§4`) to land `F(T) ≤ logρ* + O(1/n)`, tight at the
  caterpillar.
- **G5** — reduce the analytic inequality to kernel-gateable rational/enclosure atoms (turan/jensen model).

Honest risk: G3 (finding the right interpolation) is the crux and may fail; the monotonicity probe (G2) is the
cheap decisive test. This is a genuine proof attempt, not an incremental probe. `conjecture1_proved = False`.

## Appendix — reproduction scripts (offline, `/tmp` during development)

`bg_m3_derive.py` (integrand derivation + verification), `bg_m3_flagLP2.py` / `bg_m3_flagL2.py` (reversible
flag LP + support diagnosis), `bg_m3_universal.py` (discharge LP), plus the grafting and small-tree checks.
The exact integrand and moment machinery live in `examples/bg_m3_moment_cut/generate.py`.
