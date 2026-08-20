# knapsack_sos: symbolic-n SOS lower bound pipeline (P-vs-NP certificate ladder, rung 2)

Exact verification prototype for the Grigoriev (2001) knapsack SOS degree
lower bound as a SYMBOLIC-in-n certified statement -- the first target of the
"kernel-checked asymptotic lower bound" arc.

## Statement (prototype-verified, Lean formalization pending)

For every odd n and every d <= (n-1)/2 the degree-2d pseudoexpectation
E[x_S] = (r)_{|S|} / (n)_{|S|}, r = n/2, is a valid dual witness for the
knapsack system { x_i^2 = x_i, sum x_i = n/2 }: the constraint is satisfied
exactly in the ideal sense, and the moment matrix M_d is PSD. Hence no SOS
refutation of degree <= 2d exists, i.e. certified refutation degree >= n+1.

## Structure discovered/verified (the emit-ready reduction)

1. S_n symmetry block-diagonalizes M_d into harmonic blocks realized as exact
   Gram matrices G_k via pair-difference vectors; closed combinatorial formula
   validated against brute force AND full-spectrum reconstruction (130x130,
   err < 1e-14).
2. The constraint ideal collapses every block to RANK ONE: exact kernel
   identities (i-r) G_k[.,i] + (i+1-k) G_k[.,i+1] = 0 (telescoping, same
   discipline as the BG cavity closed forms).
3. Closed-form scalars: G_k = g_k v v^T with
   g_k = 2^k prod_{j<k} (r-j)(n-r-j)/((n-2j)(n-2j-1)),
   which at r = n/2 telescopes to g_k = prod_{j<k} (n-2j)/(2(n-2j-1)).
4. PSDness of the whole moment matrix therefore reduces to d+1 univariate
   rational-function positivity facts, each a product of manifestly positive
   linear factors on the odd ray n >= 2k+1 -- emit_handelman territory.

Teeth: for r = 3/2 the factor (r-2) < 0 makes g_3 < 0, and the prototype
measures PSD failure at exactly d = 3 -- the witness genuinely discriminates.

## Honesty notes

* The lower bound itself is Grigoriev's theorem; the contribution here is the
  exact rank-1 closed-form decomposition in emit-ready per-factor form and the
  (pending) kernel-checked pipeline. Related exact symmetric-SOS analyses
  exist (Kurpisz-Leppanen-Mastrolilli); novelty claims deferred to lit review.
* verdict-path arithmetic is exact; floats only in the redundant spectral
  cross-check.

## Lean status (2026-08-20): GREEN, axioms clean

`telperion/examples/g1_floors/lean/KnapsackSOS.lean` (registered lean_lib in
that workspace; verify with `lake env lean KnapsackSOS.lean` there -- mathlib
v4.32.0 oleans cached in .lake). Kernel-checked, symbolic in n, axioms exactly
[propext, Classical.choice, Quot.sound] for all of: constraint/ideal identity
(telescoping), kernel recurrence (rank-1 collapse), g1..g4 closed product
forms, g0..g4 positivity (all n > 2k-1), rank-1 quadform PSD (block0..4_psd),
two combinatorial Gram-bridge entries (k=1 block), knapsack_unsat nonvacuity
(odd N has no boolean solution), and the master knapsack_certificate.

UPDATE (same day): the FULL d=4 Gram bridge is now kernel-checked --
gen_bridge_d4.py emits BridgeD4.lean with all 35 entry identities
(combinatorial formula = g_k * v * v, every block k <= 4), each validated in
exact Fractions against gram_block_fast AND the rank-1 form before emission
(anti-phantom gate + corruption negative control); all 35 axioms-clean.
Also added, uniform-k layer in KnapsackSOS.lean: gProd (product form) with
gProd_pos for EVERY k by induction (all rational n > 2k-1); gSum (general-k
alternating sum) with gSum_zero..four; gProd_eq_g1..g4; and the named open
W2 target `SumEqProd` (sum = product for all k), kernel-checked for k <= 4
via sumEqProd_upto4. Total: 45 axioms-clean theorems, no sorryAx.

What remains Python-pinned: the z-vector Gram derivation (that these blocks
ARE the harmonic blocks of the moment matrix -- validated by the 130x130
spectral reconstruction) and the standard moment/SOS duality (literature).

## SumEqProd: DISCHARGED (2026-08-20, same day)

`SumEqProd.lean` proves the general-k identity gSum = gProd -- the W2
creative-telescoping target -- via: (1) mathlib's fwdDiff_iter_eq_sum_shift
(Newton expansion; no hand Pascal induction) + sum reflection, giving
gSum n k = 2^k (-1)^k Delta^[k](f n)(k); (2) the contiguous-relation
induction Delta^[j](f n)(q) = (-1)^j pnum(j) f(q)/pden(q,j); (3) a product
induction at q = j = k. Payoff theorems (axioms-clean): `sumEqProd_general`
(all k, all rational n > 2k), `gSum_pos` (uniform-in-degree positivity of
the alternating-sum scalar), `sumEqProd_holds : SumEqProd`. The knapsack
scalar certificate is now UNIFORM IN DEGREE: 51 axioms-clean theorems total
across KnapsackSOS + BridgeD4 + SumEqProd.

## Next
2. Random 3XOR / planted clique: blocks are NOT rank one -- this is where the
   W2 holonomic-positivity machinery (scheme eigenvalue sequences) becomes
   load-bearing.
3. LRS transfer (Lee-Raghavendra-Steurer): from SOS degree bounds to
   "no polynomial-size SDP relaxation" statements (paper-level first).

Run: `python3 knapsack_pseudoexpectation.py --dmax 4` (all-exact, ~1 min).
