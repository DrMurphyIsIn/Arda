# The LRS transfer: from certified SOS degree bounds to "no polynomial-size SDP"

*Working note, 2026-08-21. Paper-level analysis; nothing here is formalized.*

## The theorem being invoked

Lee-Raghavendra-Steurer (STOC 2015): for max-CSPs, the sum-of-squares
hierarchy is OPTIMAL among all semidefinite programming relaxations of
comparable size -- formally, any SDP relaxation of size r for a CSP is at
most as strong as the degree-O(log r / log n)... (in the polynomial-size
regime: poly-size SDP relaxations are no stronger than O(1)... precisely,
n^{delta}-size SDPs are captured by degree-O(delta * n / log n)-ish SOS;
the clean statement: for boolean CSPs, SDP relaxations of size n^{o(1)}
... see LRS Thm 1.4/6.4 for exact tradeoffs). The mechanism: the SDP
relaxation's slack matrix has low PSD rank; a low-PSD-rank certificate
yields low-degree SOS certificates by a quantum-learning/factorization
argument.

## What our certified bounds give through it

Our kernel-checked statement (Duality.lean + the named hsq hypothesis):
no SOS refutation of knapsack with squares of degree <= d and cofactors of
degree <= 2d exists for N > 2d. Through LRS-type transfer, degree lower
bounds of Omega(n) for a CSP-shaped problem convert to EXPONENTIAL lower
bounds on the PSD extension complexity of any SDP relaxation solving it.

CAVEATS specific to our instance, in decreasing order of severity:
1. LRS is stated for max-CSP VALUE problems; knapsack `sum x = n/2` is a
   single global linear constraint, not a bounded-arity CSP. The transfer
   does NOT directly apply; the honest target for a transfer paper is a
   3XOR-type instance (bounded arity, where Schoenebeck degree bounds +
   LRS give the canonical "no poly-size SDP for max-3XOR approximation"
   -- this is Theorem 1.1-adjacent territory in LRS itself).
2. The transfer machinery (pseudo-density operators, low-rank
   factorization to low-degree pseudoexpectations) is far beyond current
   formalization reach; a certified end-to-end statement would need the
   LRS argument itself formalized (a multi-year project).
3. Rothvoss's matching-polytope bound (exponential extension complexity,
   LP side) and Fiorini et al. are the unconditional exemplars; the SDP
   side rests on LRS.

## Realistic certified milestones, in order

1. DONE (modulo hsq): refutation-form degree bound for knapsack
   (Duality.lean).
2. 3XOR refutation-form per-instance bounds via the closure certificates
   (PetersenCertificate + a duality layer over the +-1 Fourier basis --
   the 3XOR analog of pe is the sign-table functional; same abstract
   no_refutation theorem applies, over a different monomial semantics).
3. Paper-level: state the LRS corollary for 3XOR with full attribution,
   certified-degree-bound inputs clearly separated from unformalized
   transfer machinery (honest-conditional, R7'-style).
4. Formalizing LRS itself: named as out of scope; would be its own
   research program.

## Bottom line

The transfer note's role in the paper: position the certified degree
bounds as the INPUT side of the strongest known degree-to-size pipeline,
claim only the certified layer, and state the corollary conditionally.
No overclaim: "no polynomial-size SDP" remains a literature-conditional
statement until someone formalizes LRS.
