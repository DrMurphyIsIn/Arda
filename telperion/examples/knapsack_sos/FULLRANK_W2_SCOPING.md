# Planted clique / Laurent max-cut: the full-rank W2 target (scoping, 2026-08-21)

## Why these are different

Every certified object so far has RANK-ONE harmonic blocks (knapsack: the
constraint ideal collapses them; 3XOR: derivability classes are rank-one).
The W2 machinery (holonomic/scheme-eigenvalue positivity) has therefore
never been load-bearing. The two named targets where blocks are genuinely
FULL-RANK:

## 1. Laurent's max-cut bound (the tractable entry)

Laurent (Math. OR 2003): the Lasserre relaxation of max-cut on K_n needs
ceil(n/2) rounds. The dual witness is an S_n-symmetric pseudoexpectation
on +-1 variables whose moment matrix has full-rank symmetric blocks;
PSDness in the literature goes through univariate orthogonal-polynomial
(Hahn-type) positivity -- EXACTLY the W2 certificate family.

Plan (mirrors knapsack day-one):
  a. exact prototype: build Laurent's pseudoexpectation from the paper
     (do NOT reconstruct from memory -- fetch the construction), verify
     PSD exactly at small n, extract the block structure;
  b. symbolic-n blocks: fit block entries as rational functions of n
     (the established interpolation pipeline);
  c. the certificate: eigenvalue sequences are hypergeometric in n ->
     FwdTelescopeEmitter GENERALIZATION NEEDED: the current template is
     first-order/affine (f(q+1) = f(q) A(q)/(P-q)); Hahn-type sequences
     satisfy SECOND-order recurrences -> the emitter needs the
     three-term-recurrence version of the contiguous identity (certificate
     = the recurrence + boundary positivity + an interlacing/positivity
     induction, still sympy-checkable);
  d. duality layer: reuse Duality.no_refutation verbatim (it is
     system-generic); only the pe-functional and kills are new.

## 2. Planted clique (the deep target)

The BHKKMP pseudo-calibration witness is graph-indexed (random-instance),
with the deterministic core being Johnson-scheme eigenvalue estimates of
the EXPECTED moment matrix -- W2-shaped -- but the full proof needs
norm-concentration of the random fluctuation, which is NOT
certificate-shaped at current technology. Honest scope: the expected-
matrix eigenvalue layer as certified symbolic-n statements; the
concentration layer stays literature. Enter only after Laurent max-cut
proves out the second-order W2 machinery.

## Dependency graph

  FwdTelescope 2nd-order generalization  ->  Laurent max-cut certified
    ->  (a) first genuinely-full-rank W2 theorem
        (b) planted-clique expected-matrix layer
  SymmetricQuadFormEmitter  ->  SubsetFormPSD d=2,3,... (knapsack ladder)
