# D3: the superabundant reduction toward "Robin for all n <= X" -- what is and isn't kernel-verified

> **Honest scope.** This delivers the reusable *core* of the superabundant/colossally-abundant
> reduction plus kernel-verified Robin certificates at every RH-tight superabundant number in a
> concrete range. It does **NOT** kernel-prove "Robin holds for all n <= X" (that needs two further
> pieces named below), and it does not prove RH. `conjecture1_proved` stays False.

## What is kernel-verified (in `RH/RobinReduction.lean` + `RH/Robin.lean`)

1. **The G-monotonicity reduction lemma** (`robin_G_monotone`): if the abundancy `sigma(m)/m`
   dominates `sigma(n)/n` and `log log m <= log log n` (as holds when `m <= n`), then the Robin
   quotient `G(n) = sigma(n)/(n log log n)` is dominated by `G(m)`. This is the elementary heart of
   Akbary-Friggstad (2009) "the least Robin counterexample is superabundant": a violation at `n`
   forces one at the abundancy-record `m`.

2. **Every superabundant number in (5040, 2*10^6] satisfies Robin, kernel-exactly.** There are
   exactly 13 such numbers -- 10080, 15120, 25200, 27720, 55440, 110880, 166320, 277200, 332640,
   554400, 665280, 720720, 1441440 -- and `TightRobinCertificate.for_superabundant(n)` emits an
   UNCONDITIONAL proof of `sigma(n) < e^gamma n log log n` for each, via a tight gamma
   (`eulerMascheroniSeq`, `m+1 = 2^p`) and a tight loglog (`log n >= a2 log2 + a3 log3`, then
   `loglog >= b2 log2 + b3 log3 + taylor_log(k)`). The crux is n=10080 (ratio 1.7558, the tightest
   case above 5040; ~1.4% total margin). This is the first *kernel-exact* verification of Robin on
   these numbers -- the Briggs (n <= 10^(10^10)) and Morrill-Platt (n <= 10^(10^13.11)) computations
   are floating-point / interval-arithmetic, not machine-checked proofs.

## What remains for a complete kernel "Robin for all n <= 2*10^6" (NOT done here)

The reduction "no superabundant counterexample in (5040, X] => no counterexample in (5040, X]"
(Akbary-Friggstad) needs two more ingredients, both flagged high-effort in the D2 triage:

- **(a) Superabundant-completeness.** A kernel proof that the superabundant numbers in (5040, 2*10^6]
  are *exactly* those 13 -- i.e. no other n in the range is a record for `sigma(n)/n`. This is a
  finite structural fact but not one Mathlib can `decide` cheaply (it ranges over ~2*10^6 values),
  and the clean route needs the Alaoglu-Erdos exponent structure (Mertens-type estimates absent from
  Mathlib v4.32.0).
- **(b) The boundary (5040, 10080).** The first superabundant number above 5040 is 10080, so for
  n in (5040, 10080) the abundancy record <= n is 5040 itself (a Robin *exception*), and the
  monotonicity bound is vacuous there. Those ~5039 integers must be checked directly -- ~5000
  transcendental `log log` bounds, not kernel-feasible at scale with the present machinery.

So the honest statement is: **the reduction lemma and the 13 tight SA certificates are proven; the
composition into "all n <= X" is gated on (a) and (b), which are additional (high-effort) work.**

## Why none of this approaches RH

Even a complete kernel "Robin for all n <= X" would be a FINITE result. RH requires Robin for all n,
equivalently `G(n) < e^gamma` for *all* colossally abundant numbers as n -> infinity, whose limsup is
`e^gamma` (Gronwall) with the sharp finite-CA bound governed by the width of the zeta zero-free region
(Robin Thm 7 / the Wall in `ROBIN_RH_MAP.md`). No finite range, however large or kernel-exact, is
evidence *for* RH -- only consistency with it.
