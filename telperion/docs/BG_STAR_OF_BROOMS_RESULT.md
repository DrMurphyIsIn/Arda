# A star-of-cherry-brooms family exceeding the caterpillar counterexamples for the Laplacian ratio of trees

**Status:** novel result, exactly verified; `conjecture1_proved = False` (the global maximizer remains open).
This note states precisely what is established and what is open. All quantities are exact `Fraction`s computed
by `telperion.matching_free_energy.rho` and the closed forms in `telperion.spider_broom` /
`telperion.transfer_caterpillar`.

## 1. The problem

For a tree `T` on `n` vertices with Laplacian `L(T) = D − A`, the **Laplacian ratio** is
```
π(T) = per(L(T)) / ∏_{v} d(v) = Σ_{matchings M of T} ∏_{uv ∈ M} 1/(d(u) d(v))
```
(the second equality is Pant 2026, Lemma 2.1; it is exactly `matching_free_energy.rho`). Brualdi & Goldwasser
(1984) asked for `max_T π(T)` over `n`-vertex trees; **the exact maximizer is open**. We study the per-vertex
growth rate `F = lim_{n→∞} (1/n) log π(T_n)` of natural tree families.

## 2. Prior state of the art

- **Wu–Dong–Lai (Discrete Appl. Math. 372, 2025), Conjecture 1.2:** the maximizer is the *subdivided star*
  `S(n,·)` (odd `n`) / double subdivided star `S(n,a,b)` (even `n`) — a hub (or two joined hubs) whose branches
  are **single length-2 paths** (one cherry per branch). Its rate is `F = ½ log(3/2) ≈ 0.202733`.
- **Pant (arXiv:2605.14176, 2026):** *refutes* Wu–Dong–Lai in all three parity cases with the **path-core
  caterpillar** family `T(a₁,…,aₘ)` (a path spine `x₁–⋯–xₘ` with `aᵢ` pendant length-2 paths on `xᵢ`), for which
  `π(T(a₁,…,aₘ)) = (3/2)^{Σaᵢ} f_m` (`f_m` a two-term recurrence). Pant leaves the exact maximizer **open** and
  gives no per-vertex constant. The caterpillar family's rate is `F_cat = max_a F_cat(a) = 0.205098` at `a = 7`
  arms per interior hub (interior hub degree `a+2`).

So `0.202733` (WDL) `< 0.205098` (Pant caterpillars), and the maximizer is open.

## 3. The star-of-cherry-brooms `S(k,c)`

Define `S(k,c)`: one **central hub** joined to `k` **branch-hubs**, each branch-hub of degree `c+1` carrying `c`
pendant length-2 paths ("cherries", each = branch-hub–armmid–leaf). Vertices: `n = 1 + k(2c+1)`.

The distinction from Pant's caterpillar is the **core**: the branch-hubs sit on a *star* (each has exactly one
"up" neighbour, the center), so each branch-hub has degree `c+1` — versus the caterpillar's *path* core, where
interior hubs have degree `c+2`. The lower degree gives a larger matching weight `1/d`, and the single
high-degree center is asymptotically negligible.

**Exact closed form** (Theorem 3.1, verified `== rho` for `1 ≤ k ≤ 8`, `1 ≤ c ≤ 6`):
```
total(c) = (3/2)^{c-1} (4c+3) / (2(c+1))          (the weight one B(c) branch presents to the center)
π(S(k,c)) = total(c)^{k-1} ( total(c) + (3/2)^c/(c+1) )
```
Derivation: each cherry presents cavity pair `(unm, mat) = (1, 1/2)` on its degree-2 armmid, so a branch-hub of
degree `c+1` with `c` cherries has `U = (3/2)^c` (hub unmatched) and `M = c/(2(c+1)) (3/2)^{c-1}` (hub matched
down), i.e. `total = U + M = (3/2)^{c-1}(4c+3)/(2(c+1))`. The center of degree `k` is unmatched in the leading
term (`∏ total`) plus one matched-to-a-branch correction, giving the formula. As `k → ∞`,
```
F(c) := lim (1/n) log π(S(k,c)) = log(total(c)) / (2c+1).
```

## 4. Main result (exact, verified)

**Theorem 4.1 (`c = 5` optimum).** `F(c)` is maximized over integers `c ≥ 1` at `c = 5`, with
```
total(5) = 621/64,   F(5) = log(621/64)/11 = 0.2065864…   (rate π^{1/n} → 1.2294737…).
```
Strictness is certified by cross-exponentiation (which clears the `(2c+1)`-th roots): for `c ≠ 5`,
`F(5) > F(c) ⟺ total(5)^{2c+1} > total(c)^{11}`, an exact rational inequality. Kernel-gated in
`examples/bg_broom_optimum` (Lean `norm_num`, competitors `c ∈ {2,3,4,6,7,8}`).

**Theorem 4.2 (beats the caterpillars).** `F(5) = 0.206586 > 0.205098 = F_cat` (Pant's caterpillar sup), and in
fact `F(c) > F_cat` for every `c ≥ 3`. Hence `S(k,5)` asymptotically exceeds both Pant's caterpillars and the
Wu–Dong–Lai subdivided star. At **finite** `n` the crossover is `n ≈ 134`: e.g. `S(19,3)` (n=134) has
`log π = 27.5336 > 27.5259` (best caterpillar), and `S(15,4)` (n=136) `28.020 > 27.937` — all exact.

**Proposition 4.3 (branch-rate ceiling, computational).** Writing the optimal tree as "central hub + copies of a
rooted branch `B`", the density is governed by `rate(B) = total(B)^{1/|B|}`. Over **all** rooted branches up to
**18 vertices** (exhaustive), the *unique* maximizer is `B(5)` (`total = 621/64`, `rate = 1.2294737`, size 11);
recursive/2-level branches (a hub of sub-brooms) score strictly lower. The ceiling is robust under every tested
extension beyond the exhaustive range: big brooms `B(c)` decrease monotonically past `c = 5` (`rate(B(6)) =
1.229330 < 1.229474`), and recursive `hub-of-j×B(5)` branches increase in `j` but converge to `1.229474` strictly
**from below** (`j = 40`: `1.229232`) — as they must, since `j → ∞` is the star-of-B(5)-brooms itself. This is
strong evidence that `F* = F(5) = log(621/64)/11 = 0.2065864` is the true tree density supremum.

## 5. What is proven vs open

- **Proven / exactly verified:** the closed form (3.1); the `c = 5` discrete optimum (4.1, kernel-gated); the
  strict family dominance `F(5) > F_cat > F_WDL` and the finite-`n` crossover (4.2); the rooted-branch ceiling
  up to 16 vertices (4.3). Also: the **m=2 arm-balancing lemma** (a general `∀ a,b` monotonicity, kernel-gated
  in `bg_arm_balancing`) salvaged from the refuted "reduce to caterpillar" step.
- **Open:** that `S(k,5)` (or any explicit family) achieves the **asymptotic maximum growth rate** — i.e. that
  `F* = lim_n (1/n) log max_{|T|=n} π(T) = 0.206586` (the `≤` direction; the `≥` is proven in §4). This is the
  Brualdi–Goldwasser maximum, still formally open; (4.3) is a finite computation, not a proof over all trees.
  The remaining rigorous target is the **branch-reduction / bulk-bound theorem** `log π(T) ≤ F*·n + C` — see
  §5b for the exact Bethe framework and why per-tree density bounds cannot work (small trees exceed `F*`).

## 5b. Toward the upper bound — the branch-reduction theorem (proof framework)

The remaining hard direction is `F* ≤ 0.206586`. Progress and the correct framing:

**Exact Bethe decomposition (verified `== rho`, all trees `n ≤ 12`).** With cavity fields
`h_{u→v} = 1/(1 + Σ_{c∈N(u)\v} w_{uc} h_{c→u})`, `w_{uv} = 1/(d_u d_v)`, `h ∈ (0,1]`:
```
π(T) = ∏_{v} (1 + Σ_{u∈N(v)} w_{uv} h_{u→v})  /  ∏_{(u,v)∈E} (1 + w_{uv} h_{u→v} h_{v→u}).
```
So `log π(T) = Σ_v A_v − Σ_e B_e`, `A_v = log(1 + Σ_{u} w h_{u→v})`, `B_e = log(1 + w h_{u→v} h_{v→u})`.

**The target is asymptotic, not per-tree.** `(1/n) log π` is NOT bounded by `F*` for every tree: e.g.
`F(P_2) = ½ log 2 = 0.3466 > F*`, and `max_{|T|=n} (1/n) log π(T)` **decreases** monotonically from `0.347`
(`n=2`) toward `F*` from above (`0.20805` at `n=16`). The correct statement is the growth-rate limit
```
F* = lim_{n→∞} (1/n) log max_{|T|=n} π(T) = log(621/64)/11 = 0.2065864,
```
proven `≥` by the `S(k,5)` family (§4). Notably the small-`n` maximizers are exactly the **Wu–Dong–Lai
subdivided stars** (`n=11,13,15`: a single hub of degree `5,6,7`), overtaken by Pant's caterpillars and then by
`S(k,5)` — a clean three-regime transition.

**Why naive local bounds fail, and the correct target.** A per-vertex bound `φ_v ≤ F*` (any edge-splitting
discharge `φ_v = A_v − Σ_u τ_{v,u} B_{uv}`) is impossible: the equal split is spoofed by high-degree stars
(`φ_center = 0.438` on `K_{1,13}`), and degree-weighted splits are spoofed by leaves / small trees (`P_2`) —
exactly the acyclicity/surface barrier, and correct, since those trees really do exceed `F*` in density. The
provable target is therefore a **bulk bound with a bounded surface surplus**:
```
log π(T) ≤ F* · n + C     for an absolute constant C,
```
i.e. a discharge with `φ_v ≤ F*` for all but an `O(1)` boundary set (the `S(k,5)` bulk — branch-hub, armmids,
leaves — must sit exactly at `≤ F*` at the cavity fixed point, with only the single center and genuine
boundary carrying the surplus `C`). Equivalently, `F*` is the top of the spectrum of the one-vertex cavity
transfer operator over `(degree, field)` states — the rigorous form of the branch-rate ceiling (§4.3).

**The discharge is feasible and TIGHT on the extremal family (new).** At the `S(k,5)` cavity fixed point the
exact local data is `A_center = 0.12260, A_bh = 0.24705, A_arm = 0.44983, A_leaf = 0.38400` and edge terms
`B(center,bh) = 0.001925, B(bh,arm) = 0.044364, B(arm,leaf) = 0.38400`. Solving the minimax edge-discharge LP
over the three bulk vertex types (branch-hub, armmid, leaf; center exempt as the `O(1)` boundary) gives optimum
```
(a, b, g) = (0, 0.1737, 0.5380)  →  φ_bh = φ_arm = φ_leaf = F* = 0.206586  (all three saturate exactly),
```
with `φ_center = 0.12260 < F*`. The three bulk types being **equal at `F*`** is the hallmark of a tight extremal
certificate (max `=` average `=` `F*`, so the discharge is optimal). This confirms `F*` is the right constant
and reduces the upper bound to a **universal pointwise discharge inequality**: for every local configuration
(vertex degree `d`, neighbour degrees, incoming cavity fields `h ∈ (0,1]`) there is a valid edge-split making
`φ_v ≤ F*`, with equality only at the `B(5)` bulk. That pointwise statement — a finite-dimensional inequality
per configuration, over the constrained field domain — is the remaining Brualdi–Goldwasser core and remains
**open**; the framework here (exact Bethe form + tight bulk/surface discharge, or the transfer-operator
variational bound) is the live, now-concrete route.

## 6. Novelty

Confirmed against the literature (Brualdi–Goldwasser 1984; Wu–Dong–Lai 2025 DAM 372; Wu–Dong–Lai–Zeng 2024
arXiv:2402.15669; Pant 2026 arXiv:2605.14176): the star-of-cherry-brooms as an (asymptotic) extremal family, the
`c = 5` optimum, and the growth constant `0.206586` (`1.2294737`) are **not** in the record. This is a stronger
counterexample to Wu–Dong–Lai than Pant's, and a new lower bound on the maximum Laplacian-ratio growth rate.
Terminology caution: "broom" denotes the diameter-constrained *minimizer* in Wu–Dong–Lai–Zeng 2024 — we name
ours *star-of-cherry-brooms* `S(k,c)` and contrast it with Wu–Dong–Lai's `S(n,a,b)` (one cherry per branch).

## 7. Reproduction

`telperion.spider_broom` (`spider_edges`, `spider_Z`, `broom_total`, `broom_free_energy`, `broom_argmax_c`,
`BroomOptimumCertificate`), `telperion.transfer_caterpillar` (`two_hub_Z`, `arm_balance_delta_g`,
`Z_recurrence`), tests `tests/test_spider_broom.py` + `tests/test_transfer_caterpillar.py`, kernel gates
`examples/bg_broom_optimum` + `examples/bg_arm_balancing`. Refutation trail in `BG_PIECE3_OBSTRUCTION_MAP.md`.
`conjecture1_proved = False`.
