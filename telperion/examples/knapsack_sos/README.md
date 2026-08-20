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

## Next

1. Lean: formalize E, the telescoping constraint/kernel identities, the
   rank-1 factorization, and per-factor positivity (emit_handelman) -->
   kernel-checked "SOS degree > 2d for all odd n" per fixed d; then the
   uniform-d statement.
2. Random 3XOR / planted clique: blocks are NOT rank one -- this is where the
   W2 holonomic-positivity machinery (scheme eigenvalue sequences) becomes
   load-bearing.
3. LRS transfer (Lee-Raghavendra-Steurer): from SOS degree bounds to
   "no polynomial-size SDP relaxation" statements (paper-level first).

Run: `python3 knapsack_pseudoexpectation.py --dmax 4` (all-exact, ~1 min).
