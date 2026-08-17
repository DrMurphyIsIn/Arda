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
- **Branch-induction wiring** (that `g_bound<γ` + children-master ⟹ parent-master, exactly, all cases).
  — **OPEN** (structural layer; the naive substitution has the `C^{j'-1}` blow-up, which the g-lemma's
  two-regime bound is meant to defeat — the wiring makes that precise). Verified broadly (n≤11).

## R2 — multi-hub extremality

- **Double-near-star family bound** `Φ¹¹(DN(a,b)) < 1` for all a,b≥2, via gluing submultiplicativity
  (`2b(2a−3)≥9`) + the near-star tail, and the a=2 ratio test. — **PROVEN** (`r2_submultiplicative`).
- **"DN is the multi-hub Φ¹¹-maximizer at each n"** (competitor extremality *within* multi-hub). —
  **VERIFIED n≤13** (`double_near_star`). Not proven for all n. **OPEN.**

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

1. **R1 Branch-induction wiring** — assemble `g_bound<γ` + children-master into `parent-master` rigorously
   for all cases (the parallel session's structural layer). *This is the load-bearing open piece of R1.*
2. **R1 leaf-child case** — census-verified, needs all-n rigor.
3. **R2 multi-hub maximality** — "DN is the multi-hub max at each n," verified n≤13, not proven.
4. **Per-root reduction** — verified n≤10 (a restatement; likely provable but not yet).

BG's ≤-half is therefore **NOT closed**.  It is a well-founded strong induction whose *base and every analytic
step* are proven, awaiting (1) the rigorous inductive wiring and (3) the multi-hub maximality.  The wall is no
longer an unbroken analytic inequality — it is the completion of a scaffold whose planks are individually
sound.  `conjecture1_proved = False`.
