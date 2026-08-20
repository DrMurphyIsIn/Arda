# Brualdi–Goldwasser ≤-half: structural assembly

Target: `Φ¹¹(T) ≤ 1` for all trees `T` (equality only at the 6 ties).  This file assembles the full logical
structure and marks every piece **PROVEN** (all n) / **VERIFIED** (exhaustive in a finite range only) /
**OPEN**.  The honest verdict is at the bottom.  `conjecture1_proved = False`.

## Decomposition

- **Per-root reduction.** `Φ¹¹(T) = max_r Φ¹¹(T,r) ≤ 1  ⟺  Φ¹¹(T,r) ≤ 1 for every root r`
  (`collective_cancellation`). — **VERIFIED n≤10.** [likely provable; a restatement]
- Every tree splits into **single-hub** (one vertex of degree ≥3) and **multi-hub** (≥2). BG = R1 ∪ R2.

## The base: near-star spine — PROVEN (all n, Lean CI-green)

- Tie `Φ¹¹(N(0,5))=1`  ⟺  `64·243·23 = 621·576` (`rigidity`, `FractalTail.lean`). **PROVEN.**
- Near-star tail `Φ¹¹(N(0,s)) ≤ 1` ∀s (`near_star_tail`, ratio + `162¹¹·486<161¹¹·529`). **PROVEN.**
- Asymptote `D∞<1` ⟺ `3¹¹·64²<2¹¹·621²` (`fractal_eigenvalue`, `FractalTail.lean`). **PROVEN.**

## R1 — single-hub extremality (via the master inequality)

**Master inequality** (`arm_maximal`): for every rooted tree `B`,
`(2+μ_B)¹¹ · F_B ≤ (64/621)·3¹¹`, equality iff `B` is a leaf.  It implies arm-maximality and single-hub BG.
— **VERIFIED n≤11** (0 violations, 4394 rooted trees; tight at the leaf).  Proof = strong induction on n:

| Induction case | Status |
|---|---|
| Base: leaf (`(2+1)¹¹·(64/621) = C`, tight) | **PROVEN** |
| Chains / paths (arm is the unique path max) | **PROVEN** (`arm_monotone` Case 1) |
| Leaf-child blocks | **VERIFIED (census)** (`arm_monotone` Case 2) — all-n rigor open |
| Branching (j'≥2, all children non-leaf) → the g-lemma | see below |

**The g-lemma** (branching residual): `g_bound(μ₁..μ_{j'}) < γ`.
- Over-the-reals **T1/T2 unimodality** (box-max at symmetric μ*), via the exact identity `(j'+1)boost =
  j'+4/3+S` and the descent `> 3+μ_i` for j'≥2. — **PROVEN** (`branching_unimodality`).
- Two rational leaves `μ*<1/3` and `W(4/3)¹¹<γ` (⟺ `621·4¹¹<64·5¹¹`). — **PROVEN** (`gstep_reduction`).
- **Abstract g-lemma, kernel-proven** (2026-08-20): `gV_le` — `g(C) ≤ γ = W²(5/3)¹¹` for every block of
  the `Blk` cavity model — is a kernel-checked Lean theorem in the standalone
  `examples/g1_floors/lean/GLemma.lean` package (achievability supplied structurally by
  `muV_nonleaf_le_half`). Port into `R3Cert` (`GArmExtAbstract.lean`, `GLemmaAbstract.lean`) in review
  (PR #20).
- **Branch-induction wiring** (that `g_bound<γ` + children-master ⟹ parent-master, exactly, all cases).
  — **NARROWED** (2026-08-20; previously a monolithic OPEN). The correction-and-reduction cycle landed on
  `main` (`R3Cert/CappedJointAchievable.lean`, kernel-checked, axioms clean):
  the original `Case2Property` was **FALSE as stated** (g-step factor `>1` on the unachievable band
  `μ ∈ (1/2,1)`, witnessed exactly by `bg/g_step_margin.py`); the fix is the **achievability**
  constraint (non-leaf messages have `μ = 1/(j+1+S) ≤ 1/2`; the only achievable `μ > 1/2` is the leaf
  `μ = 1`) — the relocated integrality content. Then, kernel-checked: `single_child_le_one`
  (`0<μ≤1/2`), `two_child_le_one` (all `a,b>0` — no achievability needed for `j'≥2`; the integrality
  wall is a single-child phenomenon), `prodBcap_le_prodGlemma`, and the assembly bridge
  `gstep_le_one_of_glemmaBound` reducing the config g-step at **every arity** to the single inequality
  `W·baseOf¹¹·prodGlemma ≤ γ` = the abstract g-lemma above. **Remaining OPEN, named:** the ℚ→ℝ cast
  seam (`baseOf = boostR`, `Bcap ≤ factorR`; recipe in PR #20) and the mixed leaf-child cases.

## R2 — multi-hub extremality

- **Double-near-star family bound** `Φ¹¹(DN(a,b)) < 1` for all a,b≥2, via gluing submultiplicativity
  (`2b(2a−3)≥9`) + the near-star tail, and the a=2 ratio test. — **PROVEN** (`r2_submultiplicative`).
- **Multi-hub reduction (partial — cover with one named hole)** — the moves {*2-hub base* `DN`; *deg≥4 hub-hub
  cut* + between-hub contraction, `multihub_submultiplicative`; *peeling/contraction to ≤2 hubs*,
  `multihub_peeling`} cover **every multi-hub tree exhaustively for n≤17** (0 uncovered, 45013 three-hub trees
  at n=17). The maximizer among ≥3-hub trees is the deg-3 hub *caterpillar* (per-hub transfer ρ≈0.726<1, peak
  `DN(2,2)=0.700`). **CORRECTION (2026-08-18):** an earlier "100% cover" claim was an overclaim — the
  peeling-existence lemma (L2) is **FALSE**. Counterexample: the **hub-star of near-stars** `hubstar(3,3)`
  (n=22, hub-degrees [3,4,4,4], `Φ¹¹=0.386<1`) — no deg≥4–deg≥4 edge, every near-star-end-hub peel *decreases*
  `Φ¹¹`, no contraction available ⇒ no non-decreasing hub-reducing move exists. This is the marginal-tie wall
  recurring at the multi-hub level (resonant band k∈{3,5,7}; coverable again at k=1 and k≥19). The hole is
  **narrow, non-recursing, bounded**: exactly the depth-2 hub-star-of-near-stars family (3-level nested are
  covered; family peak `Φ¹¹=0.682<1`). Closing it needs a **direct family bound**, not a local move. So the
  front reduces to: (L1) deg≥4 submult+contraction; (L2′) peeling for trees *outside* the hub-star family;
  (L3) the direct hub-star-of-near-stars family bound.
- **(L3) Hub-star-of-near-stars family bound — PROVEN** (`hubstar_bound`). `Φ¹¹(hub-star) < 1` for every
  hub-star with ≥1 near-star branch, via three exact reductions on the closed form
  `Φ¹¹ = W(1+S/d)¹¹·∏B(kᵢ)·armᵃᶜ` (center = max root): **(A)** branches `k≥6` dominated by the `k=5` tie
  (`s`,`B` monotone); **(B)** tie-count `t` is Möbius-monotone, so the `t→∞` limit `W(26/23)¹¹=0.397<1`
  (⟺ proven `64·26¹¹<621·23¹¹`, `family_martingale`) never lifts the max above `t=0`; **(C)** finite `t=0`
  optimization (non-tie count `<160`; `≤2` types by concavity) gives EXACT max `Φ¹¹=0.852381` (≥1 branch),
  `0.681555` (≥3 branches — the uncovered case). **This closes the one known hole.** Generalizes
  `family_martingale` (its `hub+k·N(0,5)` is the all-tie, no-arm slice).
- **(i)/(ii) RESOLVED — as refutations (2026-08-18).** The multi-hub front does **not** close by
  {reduction + finite family bounds}. A systematic decorated-hub-core enumeration shows the **irreducible**
  trees (>2 hubs, no deg≥4–deg≥4 edge, no non-decreasing hub-reducing move) form an **unbounded, growing
  hierarchy** — one family per hub-core shape: non-hub-star irreducible families number 0, 4, 10, **80** at
  core sizes h=4,5,6,7 (first at n=27). So **(i) [hub-star is the only irreducible family] is FALSE**, and
  **(ii)-L2′ [peeling covers all non-hub-star trees] is FALSE** (peeling fails on exactly these). **(ii)-L1
  [deg≥4 cut submultiplicativity] survives** stress-testing (0 violations on large tie-laden trees; still
  verified-not-proven all-n). Silver lining: every irreducible family is uniformly bounded and the bound
  *improves* with core size (max `Φ¹¹` = 0.288, 0.230, 0.184 at h=5,6,7 — each extra hub adds net `(64/621)`
  suppression). The `Φ¹¹`-maximal irreducible tree is **`hubstar(3,3)` itself at `Φ¹¹=0.38609`** (deg-3
  center, three `N(0,3)` branches, no center arms; the larger `0.68/0.85` hub-stars are *reducible* — center
  arms create a deg≥4 cut). The honest remaining theorem is a **uniform bound "irreducible ⇒ `Φ¹¹≤0.386<1`"**
  (`hubstar(3,3)` extremal), a transfer-decay (ratio ≈0.80/core-hub). Despite the huge margin, its proof is the
  **same collective crux** — the per-node telescoping potential verifies `≤0.93` but its per-node super-solution
  fails on the relaxed domain (non-local coupling), and the transfer-decay is a Perron statement over arbitrary
  core topologies. **OPEN, equivalent to the multi-hub crux.**
- **"DN is the multi-hub Φ¹¹-maximizer at each n"** (competitor extremality *within* multi-hub). —
  **VERIFIED n≤13** (`double_near_star`). Now subsumed by the reduction above. **OPEN** all-n.

### Object note (Pant reconciliation)
`Φ¹¹ = (64/621)ⁿ(∏aᵥ)¹¹` is **not** the raw Laplacian ratio `π(T)=per(L)/∏deg`. Raw `π` is unbounded
(star = `per(L)`-minimizer, path/spiders = maximizers) and the near-star does **not** maximize it — Pant
(arXiv:2605.14176) refutes the subdivided-star maximizer guess for raw `π`. That refutation does **not**
touch `Φ¹¹`: on Pant's counterexample spiders our object stays far below 1 (`T(4,4,4,4)=0.097`,
`T(3,4,3)=0.256`), with the near-star `N(0,5)=1` the unique maximizer. The `(64/621)ⁿ` per-vertex
normalization is exactly what makes the near-star extremal. (GTS/Kelmans are per(L)-monotone toward the
star-as-*minimizer* — the wrong direction — confirmed computationally; they cannot crown the interior-point
near-star.)

## The two hardest near-1 families — both PROVEN below 1

- Tie-recursive `hub + k·N(0,5)` (`family_martingale`, F=1 conservation + `64·26¹¹<621·23¹¹`). **PROVEN.**
- Double-near-star (above). **PROVEN.**

Both anchored in the proven near-star spine. These are the families that approach 1; both are now strictly bounded below it.

---

## Honest verdict

**The analytic content is proven; the structural assembly is not complete.**

PROVEN (all n): the near-star spine; the g-lemma's unimodality + rational leaves; both hardest near-1
families; the R2 double-near-star family bound; the master inequality's base + chain + branching-analytic
steps.

The **remaining gaps** — all structural or verified-in-range, none analytic — are:

1. **R1 Branch-induction wiring** — **narrowed 2026-08-20** to two named seams: the ℚ→ℝ cast bridge
   tying the kernel-checked any-arity reduction (`gstep_le_one_of_glemmaBound`) to the kernel-proven
   abstract g-lemma `gV_le` (PR #20 recipe), and the mixed leaf-child cases. Mechanical Lean work, not
   open mathematics — but not done, so still *the load-bearing open piece of R1*.
2. **R1 leaf-child case** — census-verified, needs all-n rigor.
3. **R2 multi-hub maximality** — "DN is the multi-hub max at each n," verified n≤13, not proven.
4. **Per-root reduction** — verified n≤10 (a restatement; likely provable but not yet).

BG's ≤-half is therefore **NOT closed**.  It is a well-founded strong induction whose *base and every analytic
step* are proven, awaiting (1) the rigorous inductive wiring and (3) the multi-hub maximality.  The wall is no
longer an unbroken analytic inequality — it is the completion of a scaffold whose planks are individually
sound.  `conjecture1_proved = False`.
