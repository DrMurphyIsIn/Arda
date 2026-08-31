# Brualdi–Goldwasser route (b): first-principles map + literature-reassessed crux

`conjecture1_proved = False`. A complete inventory of every lemma, theorem, and refutation in the proof
effort, then the reassessment after a 3-agent combinatorial-literature dive. **Headline: the productive
toolkit is combinatorial (VDB-weighted matching / Karamata exchange), not the spectral/cavity machinery this
project has been using — and that redirect explains every refutation.**

## 0. The object (first principles)

`F(T) = (1/n) log(per(L)/∏deg)`, `L = D−A`. From `per(D−A)` directly: a permutation contributes only via
fixed points (weight `d_v`) and edge 2-cycles (weight `(−1)(−1)=1`), so on a tree
```
per(L) = Σ_{matchings M} ∏_{v unmatched} d_v   ⟹   Z(T) := per(L)/∏deg = Σ_{matchings M} ∏_{v matched} 1/d_v.
```
This is a **degree-weighted monomer–dimer / VDB-weighted Hosoya index** (edge weight `1/(d_u d_v)`). Maximize
`F = (1/n)log Z` over trees, `n→∞`; maximizer = interior multi-hub length-2-arm caterpillar (~7 arms/hub),
`log ρ* ≈ 0.205098`. **OPEN** (Brualdi–Goldwasser 1984; Pant 2026 arXiv:2605.14176 refuted the subdivided-star
conjecture, confirming an interior length-2-arm caterpillar; no upper bound / no ~7 in the literature).

## 1. Verified exact reformulations (lemmas, all numeric ~1e-16)

| id | statement | use |
|----|-----------|-----|
| L1 | `F = ½∫log(1+u)dμ_N`, `N=D^{-1/2}AD^{-1/2}`, `u=λ²` | spectral |
| L2 | `Z = Σ_M ∏_{v matched} 1/d_v` (monomer–dimer) | **combinatorial (the productive one)** |
| L3 | `F = ½∫₀¹ g_T(t)dt`, `g_T(t)=(1/n)Tr[N²(I+tN²)^{-1}]` | resolvent (cap-free) |
| L4 | `F = (1/n)Σ_v[log(A_v/d_v) − ½Σ_a log(1+1/(μ_{v→a}μ_{a→v}))]` | cavity/Bethe |
| L5 | exact per-vertex `m_k` integrands via Dyck-path enumeration (m₁,m₂ radius-1, m₃ radius-2) | walk-count |
| L6 | `N^m_{vv} = (AD^{-1})^m_{vv}` (rational) | enabling |
| L7 | **transfer recurrence** `π(T(a₁..aₘ)) = (3/2)^{Σaᵢ} f_m`, `f_i=(1+a_i/(3d_i))f_{i-1}+1/(d_{i-1}d_i)f_{i-2}` (Pant) | finite reduction |

## 2. Kernel-verified theorems (on `main`)

- **T1 (piece 2, #158):** `F(a)` (uniform length-2-arm caterpillar, a arms/hub) is concave with strict max at
  a=7 — the arm-count/`k=0` direction.
- **T2 (piece-3 finite rung, #161):** caterpillar strictly beats explicit structurally-distinct competitors at
  moment-degree-3.
- **piece 1:** SSM / uniform cavity contraction (Heilmann–Lieb; BGKNT 2007) — cited theorem.

## 3. Verified-but-unproven

- **V1:** far (structurally-distinct) trees are pointwise resolvent-dominated `g_T(t) ≤ g_C(t) ⟹ F(T)≤F(C)`.
- **V2:** caterpillar = fixed-degree Randić(`m₁`)-max = F-max for **caterpillar-family** degree sequences.
- **V3:** phonon Hessian negative-definite (structural local max), gapped by SSM.

## 4. Proven negatives — every clean simplification refuted (verification-as-instrument)

N1 moment/flag capped at degree 3 · N2 resolvent forest-spoofed at every t · N3 message-discharge overfits
(289k params/896 constraints) · N4 Bethe functional a coordinate-invariant saddle · N5 grafting not
sub/super-additive (Fekete fails) · N6 spectral-measure SSD too strong · N7 no simultaneous weighted-`Z_k`
maximizer (9/74 groups) · **N8 Randić `argmax F = argmax m₁` FALSE (N=14 counterexample)** · N9 GTS/Kelmans
endpoint-only (interior optimum inapplicable). **The barrier:** acyclicity is global; all local per-vertex
means are forest-spoofed (forests have higher density). Connectedness `= #edges=n−1`; path-cover/longest-path
(ACH §4) is the measure-level forest discriminator.

## 5. THE REASSESSMENT (3-agent combinatorial-literature dive)

**The whole effort used spectral/cavity/moment tools; the literature says the productive toolkit is
combinatorial.** Three independent agents converged:

- **The exact analogue is solved.** Cambie–McCoy–Sharma–Wagner–Yap (arXiv:2209.03408) study the **VDB-weighted
  Hosoya index** `Z(G,φ)=Σ_M ∏φ(d_u,d_v)` and PROVE the extremizers: for `φ=c^{ij}` the maximizer is the
  **balanced double-broom (a caterpillar)** — a proven **interior** maximizer of a degree-weighted matching
  sum. Method: **induction + Karamata majorization + leaf-exchange** (combinatorial, connectedness-native).
  Our weight is `φ(i,j)=1/(ij)=(ij)^{-1}` — the **decreasing (c=−1)** regime, *outside* their proven `c>0`
  range. That is the frontier and the load-bearing gap.
- **This EXPLAINS N8.** The reciprocal weight `1/d_v` couples a vertex's weight to its own branching, breaking
  the Andriantiana–Wagner (arXiv:2008.00722) monotonicity condition (I.2/II.2) — exactly why the greedy/M-tree
  dichotomy and the Randić reduction fail. The non-monotonicity is intrinsic, not a fixable accident.
- **Why the optimum is interior at ~7 (mechanism).** Unweighted monomer–dimer entropy is monotone increasing
  in degree (no interior optimum); the `1/d²` edge weight makes the effective fugacity `∝1/d²`, so per-arm
  entropy `≈ log(1+1/(2d)+½)` *falls* as arm count rises `∝ d`. Arms grow linearly, weight decays
  quadratically ⟹ **interior max at finite d≈7**. Heilmann–Lieb real-rootedness ⟹ log-concave per-site free
  energy justifies the concavity (this is T1, now mechanistically explained).
- **My refutations are literature-confirmed:** GTS/Kelmans endpoint-only; real-stability is *intra-graph* only
  (cannot compare two trees — kills the moment/coefficient route); FKG/Ahlswede–Daykin **fail** (matchings are
  log-**sub**modular / negatively associated); occupancy-fraction LP → **disconnected** extremizers
  (forest-blind — this IS my acyclicity barrier, named in the literature).

### The reassessed proof template (literature-grounded, avoids all refuted routes)

Work with `Z` **combinatorially**, not `F` spectrally:

1. **P1 — reduce to the caterpillar family** via a Cambie–Wagner-style **Karamata majorization + leaf-exchange**
   over tree degree sequences. **LOAD-BEARING NEW LEMMA:** re-sign their leaf-exchange inequality for the
   *decreasing/reciprocal* weight `1/(d_u d_v)` (c=−1). Pant's clean `3/2`-per-arm factorization (L7) is
   evidence the needed coefficientwise structure holds.
2. **P2 — finite reduction:** Pant's transfer recurrence (L7) reduces the caterpillar family to a
   finite/1-parameter optimization (the spine `f_i` IS the monomer–dimer transfer operator).
3. **P3 — interior optimum at ~7:** degree-weighted concavity (the linear-arm vs quadratic-weight mechanism;
   Heilmann–Lieb log-concavity) — this is T1, to be extended to *all* structural directions.
4. **P4 — exclude competitors:** GTS **coefficientwise** domination (if the weighted `g`-polynomials stay
   nonnegative) + per-hub **arm-balancing interchange** (arms differ by ≤1) + a Shearer-type **integer floor**
   (no hub exceeds threshold).

### P0-combinatorial — the load-bearing exchange VERIFIED for the reciprocal weight

The key structural lemma of P1/P4 — that the **arm-balancing / leaf-exchange move signs correctly for the
*decreasing* weight `1/(d_u d_v)`** (the `c=−1` case Cambie–Wagner leave open) — is numerically confirmed:
- **Two-hub** `T(a,b)`, `a+b` fixed (L=1 and L=2 arms): balancing arms **monotonically increases** `F`; the
  balanced split (`|a−b|≤1`) is the maximizer in every case (e.g. a+b=14, L=2: (7,7)=0.20659 > (8,6) > … >
  (14,0)=0.19990).
- **Multi-hub** (3,4,5 hubs, total arms fixed): the **equal** distribution across hubs maximizes `F` in every
  case — the uniform caterpillar is the family maximizer, and `F → logρ*` from above as hubs grow.

So the exchange the whole combinatorial route rests on **holds for our weight**, and the uniform ~7-arm
caterpillar is the arm-distribution optimum (consistent with T1). This is strong evidence P1/P4 are viable; the
remaining unproven content is (a) the *general* leaf-exchange lemma over arbitrary degree sequences (not just
arm-count), and (b) competitor exclusion beyond the caterpillar family. Script: `phase0/P0_2_arm_balancing.py`.

**Cautionary precedents (heed):** Wang's "greedy caterpillar maximizes Wiener" was **FALSE** (refuted by a
31-vertex counterexample; true answer an arithmetic/integrality-pinned "valley caterpillar" — mirrors this
project's own 23-adic near-tie no-go). He–Salia–Tompkins–Zhu 2026: **uniqueness can fail even when the value
is pinned** — prove the max value/arm-count separately from uniqueness.

### Phase-A gates (fail-fast; skill S0a `weighted_matching.py` built + tested)

- **S0a built + verified:** `weighted_matching.matching_generating_poly` = the VDB-weighted matching
  generating polynomial `M(T,t)=Σ_k Z_k t^k`; `M(T,1)=rho` cross-checked exhaustively to N=9 + random.
- **GATE-1 PASS (n≤16):** the global `Z`-maximizer over *all* trees is **always** a length-2-arm caterpillar
  `T(a₁..aₘ)`. P1's "reduce to caterpillar family" *target* is sound (contrast the Randić reduction, which
  broke at N=14). Script `phase0/P0_3_gates.py`.
- **GATE-2 FAIL (coefficientwise):** the toward-caterpillar (arm-balancing) move dominates in the *summed*
  `Z=Σ_k Z_k` (P0.2, holds) but **NOT coefficientwise** — the violation is always at the *top* coefficient
  (maximum matching), where the more-concentrated arrangement wins. So the **GTS-coefficientwise** competitor-
  exclusion mechanism (Sh4/S4a in the plan) is **refuted** for the reciprocal weight; **P4 must use the summed
  `Z` directly**, not coefficientwise `Z_k`. (Same reciprocal-weight non-monotonicity that killed N8.) This
  drops the coefficientwise machinery from the plan and sharpens P4 to a summed-`Z` domination argument.

## 6. The reassessed crux (single sentence)

The crux is no longer "sign the alternating-sign spectral `F`" — it is the **combinatorial lemma that the
leaf-exchange / degree-sequence-majorization move signs correctly for the *decreasing* VDB weight
`1/(d_u d_v)`** (the `c=−1` case Cambie–Wagner leave open), which — combined with Pant's transfer recurrence
(finite reduction), the degree-weighted concavity (interior ~7), and GTS/arm-balancing (competitor exclusion)
— assembles into the full theorem. This is a concrete, connectedness-native target in the toolkit that
*actually solves* this problem class, and it sidesteps the acyclicity barrier and every spectral refutation.

## Key references
Pant 2026 arXiv:2605.14176 · Brualdi–Goldwasser 1984 (Discrete Math 48) · Goldwasser 1986 (matching-stratified
bound) · **Cambie–McCoy–Sharma–Wagner–Yap arXiv:2209.03408 (VDB-weighted Hosoya; double-broom; the closest
solved analogue)** · Andriantiana–Razanajatovo–Wagner arXiv:2008.00722 (exchange/M-tree framework) · Cruz–
Gutman–Rada DAM 317 2022 (VDB-Hosoya foundation) · Heuberger–Wagner arXiv:1011.6554 (interior matching-max,
subtle motif) · Csikvári GTS arXiv:1002.2768 + Ding arXiv:2405.09027 · Csikvári LMC arXiv:1406.0766 · ACH
arXiv:1405.6740 · Davies–Jenssen–Perkins–Roberts arXiv:1508.04675 (occupancy → disconnected, forest-blind) ·
Bollobás–Tyomkyn / Belardo–Oliveira–Trevisan arXiv:2405.06091 (integer-arm floor precedents).
