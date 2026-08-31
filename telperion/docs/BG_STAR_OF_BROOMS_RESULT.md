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
16 vertices, the *unique* maximizer is `B(5)` (`total = 621/64`, `rate = 1.2294737`); recursive/2-level branches
(a hub of sub-brooms) score strictly lower (depth-4 `F ≈ 0.2053 < 0.2065`), because only one hub can afford high
degree. This is strong evidence that `F* = F(5) = 0.206586` is the true tree density supremum.

## 5. What is proven vs open

- **Proven / exactly verified:** the closed form (3.1); the `c = 5` discrete optimum (4.1, kernel-gated); the
  strict family dominance `F(5) > F_cat > F_WDL` and the finite-`n` crossover (4.2); the rooted-branch ceiling
  up to 16 vertices (4.3). Also: the **m=2 arm-balancing lemma** (a general `∀ a,b` monotonicity, kernel-gated
  in `bg_arm_balancing`) salvaged from the refuted "reduce to caterpillar" step.
- **Open:** that `S(k,5)` (or any explicit family) is the **global** maximizer — i.e. that no tree beats
  `F* = 0.206586`. This is the Brualdi–Goldwasser maximum, still formally open; (4.3) is a finite computation,
  not a proof over all trees. The remaining rigorous target is a **branch-reduction theorem**:
  `sup_T F(T) = sup_B rate(B)` with the sup attained at `B(5)`.

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
