# Research note: the `hwh` straightening inequality (open BG core)

**Date:** 2026-09-11. **Status:** OPEN. `conjecture1_proved = False`. A self-contained handoff: problem,
proven results, negative results, and an honest analysis of the two candidate techniques.

## 1. Problem

Objective `Aobj(T) = per(L(T)) / prod_v deg(v) = sum over matchings M of T of prod_{(u,v) in M} 1/(deg u
deg v)` (the monomer-dimer partition function with degree weights). `hwh` (equivalently `HnormMulti`,
equivalently "the per-size `Aobj`-maximizer over all trees is a multi-hub cherry-backbone"): every tree is
`Aobj`-dominated by a hub-backbone of its own vertex count. Reduces (proven, kernel-checked) to:

> **(hwh leaf conjecture)** Every non-backbone tree (outside finite sub-star exceptions, e.g. the n=13
> triple-3-star) admits a SIZE-PRESERVING, strDefect-reducing move -- concretely a leaf/piece relocation to
> strictly-lower degree -- that does not decrease `Aobj`.

This is the open Brualdi-Goldwasser structural core (Pant 2026 refuted the Wu-Dong-Lai maximizer conjecture;
the true maximizer is open). Empirically the conjecture holds: exhaustive over all trees n<=14, every
non-backbone tree has such a move (0 failures).

## 2. The exact decomposition (proven)

Relocate a rigid piece `K` (anchor `c`, degree `dc`) from a degree-`a` vertex `p` to a non-adjacent
degree-`b` vertex `w`. Let `G = T - K`, `H = G - p - w`, and classify matchings of `G` by whether `p`,`w`
are matched (their degree factors removed): `P00,P10,P01,P11`. With `Z = Ztot(dtSub K)`, `rho = phi/dc`
(`phi` = matchings of `K` with `c` unmatched):

```
(Aobj(T') - Aobj(T)) * a(b+1)
   = rho*(a-b-1)*P00 + (Z*(b+1)+rho*a)/(a-1)*P10 - (Z*a+rho*(b+1))/b*P01 - Z*(a-b-1)/(b*(a-1))*P11.
```

Leaf `Z=rho=1`: `= (a+b+1)*B1 + (a-b-1)*B2`, `B1 = P10/(a-1) - P01/b`, `B2 = P00 - P11/(b*(a-1))`.
Verified exact (0 mismatches, ~13000 leaf-moves + cherry/arm). Formalized: `R3Cert/R47HwhLeafDecomp.lean`,
`R3Cert/R47HwhPieceDecomp.lean` (kernel-clean).

Matching-sum factorization (verified): `P00 = Z(H)`, `P10 = sum_{q~p}(1/deg_q)Z(H-q)`,
`P01 = sum_{r~w}(1/deg_r)Z(H-r)`, `P11 = sum_{q~p,r~w,q!=r}(1/deg_q)(1/deg_r)Z(H-q-r)`.

## 3. `B2 >= 0` (proven, universal)

For each pair `(q,r)`, `Z(H-q-r) <= Z(H) = P00` (a subset of matchings, positive weights) and
`1/deg_q, 1/deg_r <= 1`; there are `<= (a-1)b` pairs, so `P11 <= (a-1)b P00`, i.e. `B2 >= 0`. Holds for all
`a>=2, b>=1` (0 counterexamples). NOTE: the clean split is special to the leaf; for a general piece the
`P00,P11` coefficient needs `rho(a-1)b P00 >= Z P11` (cherry: 3x stronger, not unconditional).

## 4. The open kernel: `B1 >= 0` existence

With `B2 >= 0` and `b+1 <= a`, monotonicity reduces to `B1 >= 0`. Characterization (`g(v)=Z(H-v)/deg_v`):

```
B1 >= 0  <=>  avg_{q~p} g(q) >= avg_{r~w} g(r).
```

Since `g(v) = Z(H)*P(v unmatched)/deg_v` in the matching measure on `H`, this is: `p`'s neighbourhood has
at least the average "unmatched-probability-per-degree" of `w`'s neighbourhood. The conjecture is that a
defect-reducing strictly-lower-degree move with this property EXISTS.

## 5. Negative results: the natural certificates FAIL

| strategy | verdict |
|---|---|
| degree-only lemma `deg_w<deg_p => Aobj nondecr` | FALSE (15522 counterexamples; first n=6, leaf-onto-leaf) |
| deterministic min-receiving-degree rule | monotone 99.6% but not degree-certifiable |
| max-degree source forces `B1>=0` | FALSE (29/369; existence fails on 14 trees) |
| "any lower-degree defect-reducing move monotone" | FALSE (233/3662 decrease `Aobj`) |
| averaging `sum_moves B1 >= 0` => some `B1>=0` | holds n<=12, **FAILS at n=13 (4/131)** |

The averaging certificate failing exactly at the n=13 triple-3-star localizes the obstruction. A proof
cannot come from degrees, a fixed rule, or a uniform average.

## 6. Candidate techniques (honest analysis)

- **Heilmann-Lieb / negative association.** The matching measure is strongly Rayleigh (real-rooted matching
  polynomial), hence negatively associated. But negative association bounds correlations WITHIN one graph
  (`P(u,v both unmatched) <= P(u)P(v)`); `B1` is a comparison BETWEEN two neighbourhoods whose outcome
  depends on the attached subtrees. So HL is a tool usable inside a proof, not a decision procedure for the
  structural comparison. Open.
- **Kelmans / shifting induction.** The classical extremal-tree tool. The repo already pursued it
  (`R47R4KelmansCorner*`); the residual is recorded as the open "Kelmans Obligation A". So Kelmans relocates
  the difficulty to the same open obligation rather than closing it.

## 7. Precise open statement (for a combinatorialist)

Prove or refute: for every tree `H` (a forest after deletions) arising as `T - leaf - p - w` from a
non-backbone tree `T`, there is a choice of a degree-`a` vertex `p` with a leaf child, and a non-adjacent
degree-`b <= a-1` vertex `w`, such that the relocation reduces `strDefect` and
`sum_{q~p} Z(H-q)/((a-1) deg_q) >= sum_{r~w} Z(H-r)/(b deg_r)`, where `Z` is the degree-weighted matching
sum. Equivalently: the per-size `Aobj = per(L)/prod deg` maximizer over trees is a multi-hub cherry-backbone.

Everything except this is proven and kernel-checked (PRs #482, #488). No closure is claimed.
